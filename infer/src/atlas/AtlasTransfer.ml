
module Formula = AtlasFormula
module Expr = Formula.Expr
module Id = Formula.Id
module VarIdMap = Formula.VarIdMap
module Astral = AtlasAstral

open !AtlasState

module TransferFunctions = struct
  module CFG = ProcCfg.Normal
  module DisjDomain = AtlasDomain.DisjDomain
  module NonDisjDomain = AtlasDomain.NonDisjDomain

  type analysis_data = IntraproceduralAnalysis.t

  let sil_instr_to_string = Format.asprintf "%a" (Sil.pp_instr ~print_types:true Pp.text)
  let sil_metadata_to_string = Format.asprintf "%a" (Sil.pp_instr_metadata Pp.text)

  let pp_session_name _node fmt = Format.pp_print_string fmt "Atlas"

  (** Transfer function for a single state — returns a list of successor states *)
  let rec exec_instr_single _node analysis_data state instr =
    let tenv = analysis_data.IntraproceduralAnalysis.tenv in
    let states = match instr with
    | Sil.Load { id; e; typ; loc } ->
      Format.print_string (
        "[SIL_LOAD]: " ^ sil_instr_to_string instr ^ "\n");
      let rhs_expr = sil_exp_to_expr ~typ:typ e tenv state in
      let states = if is_pointer_type typ then
        check_sil_ptr_arith loc instr tenv e state
      else [state] in
      let states = concat_map_ok_states
        (check_sil_ptrsub loc instr tenv e) states in
      concat_map_ok_states
        (exec_load_instr loc instr id tenv typ e rhs_expr)
        states
    | Sil.Store {e1; typ; e2; loc} ->
      Format.print_string (
        "[SIL_STORE]: " ^ sil_instr_to_string instr ^ "\n");
      let lhs_expr = sil_exp_to_expr ~typ:typ e1 tenv state in
      let rhs_expr = sil_exp_to_expr ~typ:typ e2 tenv state in
      let states = if is_pointer_type typ then
        check_sil_ptr_arith loc instr tenv e2 state
      else [state] in
      let states = concat_map_ok_states
        (check_sil_ptrsub loc instr tenv e2) states in
      concat_map_ok_states
        (exec_store_instr loc instr tenv typ e1 lhs_expr rhs_expr)
        states
    | Sil.Call
      ( (ident, typ), Exp.Const (Const.Cfun procname), ((actual, actual_typ) :: _), _loc, _ )
        when BuiltinDecl.(match_builtin malloc procname (Procname.to_string procname)) ->
          Format.print_string (
            "[SIL_MALLOC]: " ^ sil_instr_to_string instr ^ "\n");
          let actual_expr = sil_exp_to_expr ~typ:actual_typ actual tenv state in
          exec_malloc_instr ident typ actual_expr state
    | Sil.Call
      ( _, Exp.Const (Const.Cfun procname), ((actual, _actual_typ) :: _), loc, _ )
        when BuiltinDecl.(match_builtin free procname (Procname.to_string procname)) ->
          (* Note: _actual_typ is always void* in SIL — the original type is on
             the preceding Sil.Load instruction. We recover it from state.types. *)
          Format.print_string (
            "[SIL_FREE]: " ^ sil_instr_to_string instr ^ "\n");
          let actual_expr = sil_exp_to_expr actual tenv state in
          exec_free_instr loc instr tenv actual_expr state
    | Sil.Call
      ((ret, ret_typ), Exp.Const (Const.Cfun procname), ((dest, _) :: (src, _) :: (size, _) :: _), loc, _)
        when Procname.equal (Procname.from_string_c_fun "memcpy") procname ->
          Format.print_string (
          "[SIL_CALL]: " ^ sil_instr_to_string instr ^ "\n");
          let dest_expr = sil_exp_to_expr dest tenv state in
          let src_expr = sil_exp_to_expr src tenv state in
          let size_expr = sil_exp_to_expr size tenv state in
          exec_memcpy_instr loc instr tenv state ret ret_typ dest dest_expr src src_expr size size_expr
    | Sil.Prune (exp, loc, _is_then_branch, _if_kind) ->
      begin
        Format.print_string (
          "[SIL_PRUNE]: " ^ sil_instr_to_string instr ^ "\n");
        let cond = sil_exp_to_expr exp tenv state in
        let states = check_sil_ptr_arith loc instr tenv exp state in
        let states = concat_map_ok_states
          (check_sil_ptrsub loc instr tenv exp) states in
        concat_map_ok_states (fun state ->
          match eval_prune_condition cond state with
          | Unsat -> []
          | Sat -> [state]
          | Unknown ->
            match Astral.eval_prune state cond with
            | Unsat -> []
            | Sat -> [state]
            | Unknown ->
              [{ state with
                missing = { state.missing with pure = cond :: state.missing.pure };
                current = { state.current with pure = cond :: state.current.pure } }])
          states
      end
    | Sil.Call _ ->
      Format.print_string (
        "[SIL_CALL]: " ^ sil_instr_to_string instr ^ "\n");
      [state]
    | Sil.Metadata metadata ->
      Format.print_string (
        "[SIL_METADATA]: " ^ sil_metadata_to_string metadata ^ "\n");
      exec_metadata_instr metadata state
    in

    let is_modified_state = match instr with
      | Sil.Load _ | Sil.Store _ | Sil.Call _ | Sil.Prune _ | Sil.Metadata (Sil.ExitScope _) -> true
      | _ -> false
    in
    if is_modified_state then
      Format.print_string (String.concat (
        List.map
          ~f:(fun state -> to_string state)
          states));

    states

  (* ==================== SIL Load ==================== *)

  (** Dispatches a SIL Load instruction to the appropriate handler based on the RHS form:
      - Dereference (RHS contains a temp): resolve base+offset, delegate to [exec_load_deref]
      - Address assign (RHS is an address expression on a pointer type): record subst alias
      - Value load (everything else): normalize and assign via [assign_to_variable] *)
  and exec_load_instr loc instr lhs tenv typ rhs rhs_expr state =
    let lhs_id = Id.fresh () in
    let state = { state with
      vars = VarIdMap.add lhs_id (Var.of_id lhs) state.vars;
      types = VarIdMap.add lhs_id typ state.types }
    in
    if is_sil_dereference rhs then
      match base_and_offset_of_expr rhs_expr state with
      | Some (rhs_id, off) ->
        exec_load_deref loc instr tenv typ lhs_id rhs_id off state
      | None ->
        [{ state with status = Error (err_load_deref_no_base, loc, instr) }]
    else begin
      if is_sil_address_assign rhs && is_pointer_type typ then
        match base_and_offset_of_expr rhs_expr state with
        | Some (rhs_id, off) ->
          let rhs_canonical = canonical_expr state.subst rhs_id off in
          [{ state with
            subst = VarIdMap.add lhs_id rhs_canonical state.subst }]
        | None ->
          (* Const(Cint(null)) cannot appear here — SIL only places heap addresses
             on the RHS of Load address assigns, and null is not a heap address *)
          [{ state with status = Error (err_load_assign_no_base, loc, instr) }]
      else
        let rhs_norm = Formula.normalize_expr rhs_expr in
        assign_to_variable lhs_id rhs_norm state
    end

  (** Assigns [rhs] to [lhs_id]: substitution if RHS is a variable, pure equality otherwise.
      Clears stale value constraints and subst entries for [lhs_id] before the assignment.
      Handles self-reassignment (e.g. [i = i + 1]): when rhs references [lhs_id],
      resolves the old value from the existing Peq constraint and substitutes it into
      rhs before clearing, avoiding circular constraints.
      Note: when called from load, [lhs_id] is always a fresh temp so self-reassignment
      and cleanup are no-ops *)
  and assign_to_variable lhs_id rhs state =
    (* Self-reassignment: resolve old value before clearing *)
    let rhs = if Formula.expr_contains_var lhs_id rhs then
      match Formula.find_peq_value lhs_id state.current.pure with
      | Some old_value ->
        Formula.expr_replace ~old_:(Expr.Var lhs_id) ~new_:old_value rhs
      | None -> rhs
    else rhs in
    let state, rewrite_spatial = clear_stale_value_constraints lhs_id state in
    let state = { state with current = { state.current with
      spatial = rewrite_spatial state.current.spatial } } in
    match rhs with
    | Expr.Var rhs_id ->
      if Id.equal lhs_id rhs_id then
        [state]
      else
        [{ state with subst = VarIdMap.add lhs_id (Var rhs_id) state.subst }]
    | _ ->
      let exp = Expr.BinOp (Peq, Expr.Var lhs_id, Formula.normalize_expr rhs) in
      [{ state with current = { state.current with pure = exp :: state.current.pure } }]

  (** Load dereference pipeline: checks freed → base bounds → end bounds → heap match *)
  and exec_load_deref loc instr tenv rhs_typ lhs_id rhs_var_id rhs_offset state =
    let cell_size = typ_size_of tenv rhs_typ in
    [state]
    |> concat_map_ok_states
      (deref_check_freed loc instr rhs_var_id)
    |> concat_map_ok_states
      (deref_check_base loc instr rhs_var_id rhs_offset cell_size)
    |> concat_map_ok_states
      (deref_check_end loc instr rhs_var_id rhs_offset cell_size)
    |> concat_map_ok_states
      (load_match_heap loc instr lhs_id rhs_typ rhs_var_id rhs_offset cell_size)

  (** Attempts to match heap predicates for load dereference. Resolves both
      current and missing matches, then dispatches:
      - Both match → formal pointer, mirror split to both sides
      - Current only → local allocation, split current only
      - Missing only → bug (missing mirroring failure)
      - Neither → fallback to create missing cell *)
  and load_match_heap loc instr lhs_id rhs_typ rhs_var_id rhs_offset cell_size state =
    let curr_hps, curr_rest, miss_hps, miss_rest =
      heap_find_block_fragments state rhs_var_id rhs_offset cell_size
    in
    let curr_match = heap_try_match curr_hps rhs_var_id rhs_offset cell_size in
    let miss_match = heap_try_match miss_hps rhs_var_id rhs_offset cell_size in
    match curr_match, miss_match with
    | Some match_res, Some _ ->
      load_match_formal lhs_id rhs_typ match_res
        curr_hps curr_rest miss_hps miss_rest state
    | Some match_res, None ->
      load_match_local lhs_id rhs_typ match_res curr_hps curr_rest state
    | None, Some _ ->
      Logging.die InternalError
        "load_match_heap: found match in missing but not in current (mirroring bug)"
    | None, None ->
      load_create_missing_cell loc instr lhs_id rhs_typ rhs_var_id rhs_offset cell_size state

  (** Handles a heap match for a formal pointer (found in both current and missing).
      Exact match adds subst/pure eq. Block split transforms both current and missing
      spatial, adds new [ExpPointsTo] to both *)
  and load_match_formal lhs_id rhs_typ match_res
      curr_hps curr_rest miss_hps miss_rest state =
    match match_res with
    | MatchExpExact { matched = _; dest = Expr.Var id_of_dest } ->
      [{ state with subst = VarIdMap.add lhs_id (Var id_of_dest) state.subst }]
    | MatchExpExact { matched = _; dest } ->
      let exp = Expr.BinOp (Peq, Expr.Var lhs_id, dest) in
      [{ state with current = { state.current with pure = exp :: state.current.pure } }]
    | MatchBlockSplit block_split_res ->
      let { to_remove; to_add; new_exp_points_to; new_dest_id } =
        match block_split_res with
        | ExpExactMatch { block_split_args; old_dest = _ } -> block_split_args
        | BlockExactMatch args | BlockEdgeMatch args | BlockMiddleMatch args -> args
      in
      let curr_spatial = transform_spatial to_remove curr_hps to_add curr_rest in
      let miss_spatial = transform_spatial to_remove miss_hps to_add miss_rest in
      let state = { state with
        current = { state.current with
          spatial = new_exp_points_to :: curr_spatial };
        missing = { state.missing with
          spatial = new_exp_points_to :: miss_spatial } }
      in
      [{ state with
        subst = VarIdMap.add lhs_id (Var new_dest_id) state.subst;
        types = VarIdMap.add new_dest_id rhs_typ state.types }]

  (** Handles a heap match for a local allocation (found in current only).
      Exact match adds subst/pure eq. Block split transforms current spatial
      and adds new [ExpPointsTo] to current only *)
  and load_match_local lhs_id rhs_typ match_res curr_hps curr_rest state =
    match match_res with
    | MatchExpExact { matched = _; dest = Expr.Var id_of_dest } ->
      [{ state with subst = VarIdMap.add lhs_id (Var id_of_dest) state.subst }]
    | MatchExpExact { matched = _; dest } ->
      let exp = Expr.BinOp (Peq, Expr.Var lhs_id, dest) in
      [{ state with current = { state.current with pure = exp :: state.current.pure } }]
    | MatchBlockSplit block_split_res ->
      let { to_remove; to_add; new_exp_points_to; new_dest_id } =
        match block_split_res with
        | ExpExactMatch { block_split_args; old_dest = _ } -> block_split_args
        | BlockExactMatch args | BlockEdgeMatch args | BlockMiddleMatch args -> args
      in
      let curr_spatial = transform_spatial to_remove curr_hps to_add curr_rest in
      let state = { state with
        current = { state.current with
          spatial = new_exp_points_to :: curr_spatial } }
      in
      [{ state with
        subst = VarIdMap.add lhs_id (Var new_dest_id) state.subst;
        types = VarIdMap.add new_dest_id rhs_typ state.types }]

  (** Creates missing ExpPointsTo when no heap predicate matches. Should not happen
      in practice (deref_create_missing_base/end create BlockPointsTo that matches),
      but kept for consistency. Generates Freed error contract + ok with mirrored cell *)
  and load_create_missing_cell loc instr lhs_id rhs_typ rhs_var_id rhs_offset cell_size state =
    let err_freed = { state with status = Error (err_load_deref_missing_cell, loc, instr);
      missing = { state.missing with pure =
        Expr.UnOp (Freed, Var rhs_var_id) :: state.missing.pure } }
    in
    let cell_id = Id.fresh () in
    let missing_spatial = Formula.ExpPointsTo (
      Expr.BinOp (Pplus, Var rhs_var_id, Const (Int rhs_offset)),
      Expr.Const (Int cell_size),
      Expr.Var cell_id)
    in
    let ok_state = { state with
      missing = { state.missing with spatial = missing_spatial :: state.missing.spatial };
      current = { state.current with spatial = missing_spatial :: state.current.spatial };
      subst = VarIdMap.add lhs_id (Var cell_id) state.subst;
      types = VarIdMap.add cell_id rhs_typ state.types }
    in
    [err_freed; ok_state]

  (* ==================== Shared dereference utilities ==================== *)

  (** Pipes a list of states through [f], applying [f] only to Ok states
      and passing Error states through unchanged *)
  and concat_map_ok_states f states =
    List.concat_map ~f:(fun s ->
      match s.status with
      | Ok -> f s
      | Error _ -> [s])
    states

  (** Replaces [to_remove] in [from] with [to_add], then appends [rest].
      Used after block split to reconstruct the spatial predicate list *)
  and transform_spatial to_remove from to_add rest =
    let removed = Stdlib.List.filter
      (fun hp -> not (Formula.heap_pred_equal hp to_remove))
      from
    in
    List.append removed (List.append to_add rest)

  (** Checks whether pointer [var_id] has been freed — terminal error if so *)
  and deref_check_freed loc instr var_id state =
    if is_freed_expr var_id state then
      [{ state with status = Error (err_deref_use_after_free, loc, instr) }]
    else [state]

  (** Checks Base bound for dereference. Dispatches to lowering, strict check,
      or missing resource generation depending on where the bound is found.
      [cell_size] is forwarded to [deref_create_missing_base] for the case
      where no Base exists and all missing resources must be created at once *)
  and deref_check_base loc instr var_id offset cell_size state =
    match lookup_pure_bound_expr var_id Expr.Base state with
    | (Some e, _) when Formula.is_zero_expr e ->
      [{ state with status = Error (err_deref_null_base, loc, instr) }]
    | (_, Some e) when Formula.is_zero_expr e ->
      [{ state with status = Error (err_deref_null_base, loc, instr) }]
    | (_, Some e) ->
      deref_lower_base_bound loc instr e var_id offset cell_size state
    | (Some e, None) ->
      let base_off_expr = Formula.extract_offset_expr e var_id in
      begin match eval_expr_to_int64_opt base_off_expr state with
      | Some base_offset ->
        if Int64.compare offset base_offset < 0 then
          [{ state with status = Error (err_deref_below_lower_bound, loc, instr) }]
        else
          [state]
      | None ->
        Logging.die InternalError
          "deref_check_base: local Base offset is symbolic — this should be unreachable"
      end
    | (None, None) ->
      deref_create_missing_base loc instr var_id offset cell_size state

  (** Creates all missing resources when no Base constraint exists (first access
      to this pointer). Since no Base implies no End and no spatial predicate,
      we generate three error contracts and one OK state with full resources:
      - err_base: Base(id) > id + offset (access before block start)
      - err_end: End(id) < id + offset + cell_size (buffer too small / unallocated)
      - err_freed: Freed(id) (use after free)
      - ok: Base <= id+offset, End >= id+offset+cell_size, BlockPointsTo at access point
      The OK state provides Base + End + BlockPointsTo so downstream check_end and
      match_heap find everything in place and pass through without further errors *)
  and deref_create_missing_base loc instr var_id offset cell_size state =
    let access_end = Stdlib.Int64.add offset cell_size in
    (* Error contract 1: access before block start *)
    let err_base = { state with status = Error (err_deref_missing_base, loc, instr);
      missing = { state.missing with pure =
        Expr.BinOp (Pless, Expr.BinOp (Pplus, Var var_id, Const (Int offset)),
          Expr.UnOp (Base, Var var_id)) :: state.missing.pure } }
    in
    (* Error contract 2: buffer too small *)
    let err_end = { state with status = Error (err_deref_missing_end, loc, instr);
      missing = { state.missing with pure =
        Expr.BinOp (Pless, Expr.UnOp (End, Var var_id),
          Expr.BinOp (Pplus, Var var_id, Const (Int access_end))) :: state.missing.pure } }
    in
    (* Error contract 3: use after free *)
    let err_freed = { state with status = Error (err_deref_use_after_free, loc, instr);
      missing = { state.missing with pure =
        Expr.UnOp (Freed, Var var_id) :: state.missing.pure } }
    in
    (* OK state: full resources — Base + End bounds + BlockPointsTo at access point *)
    let base_bound = Expr.BinOp (Plesseq,
      Expr.UnOp (Base, Var var_id),
      Expr.BinOp (Pplus, Var var_id, Const (Int offset)))
    in
    let end_bound = Expr.BinOp (Plesseq,
      Expr.BinOp (Pplus, Var var_id, Const (Int access_end)),
      Expr.UnOp (End, Var var_id))
    in
    let block_src = Expr.BinOp (Pplus, Var var_id, Const (Int offset)) in
    let block_pto = Formula.BlockPointsTo (block_src, Const (Int cell_size)) in
    let ok_state = { state with
      missing = { state.missing with
        pure = base_bound :: end_bound :: state.missing.pure;
        spatial = block_pto :: state.missing.spatial };
      current = { state.current with
        pure = base_bound :: end_bound :: state.current.pure;
        spatial = block_pto :: state.current.spatial } }
    in
    [err_base; err_end; err_freed; ok_state]

  (** Checks End bound for dereference. Dispatches to raising, strict check,
      or missing resource generation depending on where the bound is found *)
  and deref_check_end loc instr var_id offset cell_size state =
    match lookup_pure_bound_expr var_id Expr.End state with
    | (Some e, _) when Formula.is_zero_expr e ->
      [{ state with status = Error (err_deref_null_end, loc, instr) }]
    | (_, Some e) when Formula.is_zero_expr e ->
      [{ state with status = Error (err_deref_null_end, loc, instr) }]
    | (_, Some e) ->
      deref_raise_end_bound loc instr e var_id offset cell_size state
    | (Some e, None) ->
      let end_off_expr = Formula.extract_offset_expr e var_id in
      let access_end = Stdlib.Int64.add offset cell_size in
      begin match eval_expr_to_int64_opt end_off_expr state with
      | Some end_offset ->
        if Int64.compare access_end end_offset > 0 then
          [{ state with status = Error (err_deref_above_upper_bound, loc, instr) }]
        else
          [state]
      | None ->
        deref_check_end_symbolic loc instr e end_off_expr var_id access_end state
      end
    | (None, None) ->
      deref_create_missing_end loc instr var_id offset cell_size state

  (** Handles End bound check when the End offset is symbolic (e.g. End(x) = x + n
      where n is a formal parameter from malloc(n)). Compares the symbolic offset
      expression directly against the concrete access end (integer sort) using Astral.
      - Definitely within bounds (end_off <= access_end is Unsat): pass through
      - Definitely out of bounds (access_end < end_off is Unsat): terminal error
      - Unknown: error contract (end_off <= access_end) + ok contract with upserted
        access_end < end_off, no BlockPointsTo gap needed (local malloc covers it). *)
  and deref_check_end_symbolic loc instr end_exp end_off_expr var_id access_end state =
    let oob_condition = Expr.BinOp (Pless, end_off_expr, Const (Int access_end)) in
    let within_condition = Expr.BinOp (Plesseq, Const(Int access_end), end_off_expr) in
    let within, not_within = 
      match AtlasAstral.check_sat_with_condition state oob_condition with
      | `Unsat -> true, false
      | _ ->
        match AtlasAstral.check_sat_with_condition state within_condition with
        | `Unsat -> false, true
        | _ -> false, false
    in
    match within, not_within with
    | true, false -> [state]
    | false, true ->
      [{ state with status = Error (err_deref_above_upper_bound, loc, instr) }]
    | _ ->
      let err_state = { state with
        status = Error (err_deref_above_upper_bound, loc, instr);
        missing = { state.missing with
          pure = oob_condition :: state.missing.pure } }
      in
      let filter pure = Stdlib.List.filter
        (fun e -> match e with
          | Expr.BinOp (Plesseq, _, end_off_expr')
            when Expr.equal end_off_expr end_off_expr'
              -> false
          | _ -> true)
        pure
      in
      let ok_state = { state with
        current = { state.current with
          pure = within_condition :: filter state.current.pure };
        missing = { state.missing with
          pure = within_condition :: filter state.missing.pure } }
      in
      [err_state; ok_state]

  (** Creates missing End + spatial resources when End constraint not found.
      Should not happen in practice (deref_create_missing_base creates everything),
      but kept for consistency. Base already passed, so two error contracts:
      - err_end: End(id) < id + offset + cell_size (buffer too small)
      - err_freed: Freed(id) (use after free)
      OK state gets End bound + BlockPointsTo at access point, mirrored to both *)
  and deref_create_missing_end loc instr var_id offset cell_size state =
    let access_end = Stdlib.Int64.add offset cell_size in
    (* Error contract 1: buffer too small *)
    let err_end = { state with status = Error (err_deref_missing_end, loc, instr);
      missing = { state.missing with pure =
        Expr.BinOp (Pless, Expr.UnOp (End, Var var_id),
          Expr.BinOp (Pplus, Var var_id, Const (Int access_end))) :: state.missing.pure } }
    in
    (* Error contract 2: use after free *)
    let err_freed = { state with status = Error (err_deref_use_after_free, loc, instr);
      missing = { state.missing with pure =
        Expr.UnOp (Freed, Var var_id) :: state.missing.pure } }
    in
    (* OK state: End bound + BlockPointsTo at access point *)
    let end_bound = Expr.BinOp (Plesseq,
      Expr.BinOp (Pplus, Var var_id, Const (Int access_end)),
      Expr.UnOp (End, Var var_id))
    in
    let block_src = Expr.BinOp (Pplus, Var var_id, Const (Int offset)) in
    let block_pto = Formula.BlockPointsTo (block_src, Const (Int cell_size)) in
    let ok_state = { state with
      missing = { state.missing with
        pure = end_bound :: state.missing.pure;
        spatial = block_pto :: state.missing.spatial };
      current = { state.current with
        pure = end_bound :: state.current.pure;
        spatial = block_pto :: state.current.spatial } }
    in
    [err_end; err_freed; ok_state]

  (** Lowers the Base bound in both missing and current when access offset is below
      the existing bound. Generates an error contract with Base(id) > id + offset
      added to missing precondition (access before block start in the gap) *)
  and deref_lower_base_bound loc instr base_exp var_id offset cell_size state =
    let base_offset = eval_expr_offset base_exp var_id state in
    if Int64.compare offset base_offset < 0 then
      let err_state = { state with status = Error (err_deref_below_lower_bound, loc, instr);
        missing = { state.missing with pure =
          Expr.BinOp (Pless, Expr.BinOp (Pplus, Var var_id, Const (Int offset)),
            Expr.UnOp (Base, Var var_id)) :: state.missing.pure } }
      in
      let to_remove = Expr.BinOp (Plesseq, UnOp (Base, Var var_id), base_exp) in
      let to_add = Expr.BinOp (Plesseq,
        UnOp (Base, Var var_id),
        BinOp (Pplus, Var var_id, Const (Int offset)))
      in
      let gap_size = Stdlib.Int64.sub base_offset offset in
      let block_src = Expr.BinOp (Pplus, Var var_id, Const (Int offset)) in
      let block_pto = Formula.BlockPointsTo (block_src, Expr.Const (Int gap_size)) in
      let filter pure = Stdlib.List.filter (fun e -> not (Expr.equal e to_remove)) pure in
      let ok_state = { state with
        missing = { state.missing with
          spatial = block_pto :: state.missing.spatial;
          pure = to_add :: filter state.missing.pure };
        current = { state.current with
          spatial = block_pto :: state.current.spatial;
          pure = to_add :: filter state.current.pure } }
      in
      [err_state; ok_state]
    else
      [state]

  (** Raises the End bound in both missing and current when access exceeds
      the existing bound. Generates an error contract with End(id) < id + offset + cell_size
      added to missing precondition (buffer too small in the gap) *)
  and deref_raise_end_bound loc instr end_exp var_id offset cell_size state =
    let end_offset = eval_expr_offset end_exp var_id state in
    let access_end = Stdlib.Int64.add offset cell_size in
    if Int64.compare access_end end_offset > 0 then
      let err_state = { state with status = Error (err_deref_above_upper_bound, loc, instr);
        missing = { state.missing with pure =
          Expr.BinOp (Pless, Expr.UnOp (End, Var var_id),
            Expr.BinOp (Pplus, Var var_id, Const (Int access_end))) :: state.missing.pure } }
      in
      let to_remove = Expr.BinOp (Plesseq, end_exp, UnOp (End, Var var_id)) in
      let to_add = Expr.BinOp (Plesseq,
        BinOp (Pplus, Var var_id, Const (Int access_end)),
        UnOp (End, Var var_id))
      in
      let gap_size = Stdlib.Int64.sub access_end end_offset in
      let block_src = Expr.BinOp (Pplus, Var var_id, Const (Int end_offset)) in
      let block_pto = Formula.BlockPointsTo (block_src, Expr.Const (Int gap_size)) in
      let filter pure = Stdlib.List.filter (fun e -> not (Expr.equal e to_remove)) pure in
      let ok_state = { state with
        missing = { state.missing with
          spatial = block_pto :: state.missing.spatial;
          pure = to_add :: filter state.missing.pure };
        current = { state.current with
          spatial = block_pto :: state.current.spatial;
          pure = to_add :: filter state.current.pure } }
      in
      [err_state; ok_state]
    else
      [state]

  (* ==================== SIL Store ==================== *)

  (** Dispatches a SIL Store instruction to the appropriate handler based on the LHS form:
      - Dereference (LHS contains a temp): resolve base+offset, delegate to [exec_store_deref]
      - Address assign (LHS is a program variable, RHS is a pointer): delegate to [store_address_assign]
      - Value store (everything else): delegate to [store_value_assign] *)
  and exec_store_instr loc instr tenv lhs_typ lhs lhs_expr rhs_expr state =
    if is_sil_dereference lhs then
      match base_and_offset_of_expr lhs_expr state with
      | Some (lhs_id, off) ->
        exec_store_deref loc instr tenv lhs_typ lhs_id off rhs_expr state
      | None ->
        [{ state with status = Error (err_store_deref_no_base, loc, instr) }]
    else if is_sil_pointer_address_assign lhs lhs_typ state then
      store_address_assign loc instr lhs lhs_expr rhs_expr state
    else
      store_value_assign lhs lhs_expr rhs_expr state

  (** Store address assignment: LHS is a program variable being assigned a pointer value.
      Dispatches based on RHS shape:
      - [x = x]: identity, no-op
      - [x = x + offset]: self-reassignment, rename base to fresh variable
      - [x = y + offset]: different base, temp rename or alias
      - [x = NULL]: reset to unallocated
      - Otherwise: error *)
  and store_address_assign loc instr lhs _lhs_expr rhs_expr state =
    match direct_id_of_sil_lvar lhs state with
    | Some lhs_direct_id ->
      let rhs_norm = Formula.normalize_expr rhs_expr in
      begin match base_and_offset_of_expr rhs_norm state with
      | Some (rhs_base_id, rhs_offset) ->
        let lhs_canonical = canonical_expr state.subst lhs_direct_id 0L in
        let rhs_canonical = canonical_expr state.subst rhs_base_id rhs_offset in
        let extract_canon_base = function
          | Var id -> id
          | Ptr { base; _ } -> base
        in
        let lhs_canon_base, rhs_canon_base = 
          extract_canon_base lhs_canonical,
          extract_canon_base rhs_canonical
        in
        if Int.equal lhs_canon_base rhs_canon_base then
          if Int64.equal rhs_offset 0L then
            (* x = x: identity — no change *)
            [state]
          else
            (* x = x + offset: self-reassignment within same block *)
            store_address_self_reassign lhs_direct_id rhs_offset state
        else
          store_address_assign_other loc instr lhs_direct_id rhs_canonical rhs_canon_base state
      | None when Formula.is_null_expr rhs_norm ->
        (* RHS is null — reset LHS to unallocated state *)
        let state = clear_before_subst lhs_direct_id state in
        let lhs_var = Expr.Var lhs_direct_id in
        let pure =
          Expr.BinOp (Peq, lhs_var, Expr.null) ::
          Expr.BinOp (Peq, UnOp (Base, lhs_var), Expr.zero) ::
          Expr.BinOp (Peq, UnOp (End, lhs_var), Expr.zero) ::
          state.current.pure
        in
        [{ state with current = { state.current with pure } }]
      | None ->
        [{ state with status = Error (err_store_assign_no_rhs_base, loc, instr) }]
      end
    | None ->
      [{ state with status = Error (err_store_assign_no_lhs, loc, instr) }]

  (** Self-reassignment [x = x + offset]: the pointer shifts within its own block.
      Creates a fresh variable to represent the original allocation base, renames
      all occurrences of [lhs_id] to [fresh_id] in the state, then records
      [lhs_id -> Ptr(fresh_id, offset)] in substitutions *)
  and store_address_self_reassign lhs_id offset state =
    let fresh_id = Id.fresh () in
    let state = subst_apply
      ~from_:(Expr.Var lhs_id) ~to_:(Expr.Var fresh_id) state in
    let typ = VarIdMap.find_opt lhs_id state.types in
    let state = match typ with
      | Some t -> { state with types = VarIdMap.add fresh_id t state.types }
      | None -> Logging.die InternalError
        "store_address_self_reassign: VarIdMap.find_opt call failed"
    in
    let rhs_canonical = Ptr { base = fresh_id; offset } in
    [{ state with subst = VarIdMap.add lhs_id rhs_canonical state.subst }]

  (** Address assignment where RHS base differs from LHS: temp rename or alias.
      Temps (e.g. malloc retval) get renamed in the formula so that the temp's
      entries become owned by the LHS variable. Program variables record an alias
      in subst without modifying the formula *)
  and store_address_assign_other loc instr lhs_direct_id rhs_canonical rhs_canon_base state =
    let is_temp = match VarIdMap.find_opt rhs_canon_base state.vars with
      | Some var -> not (Var.is_pvar var)
      | None -> false
    in
    let state = clear_before_subst lhs_direct_id state in
    if is_temp then
      let rhs_norm = Formula.normalize_expr (subst_expr_to_formula_expr rhs_canonical) in
      let lhs_norm = Expr.Var lhs_direct_id in
      [subst_apply ~from_:rhs_norm ~to_:lhs_norm state]
    else
      [{ state with subst = VarIdMap.add lhs_direct_id rhs_canonical state.subst }]

  (** Store value assignment: LHS is a program variable being assigned a non-pointer value.
      Uses [assign_to_variable] when LHS resolves to a direct id, falls back to pure equality *)
  and store_value_assign lhs lhs_expr rhs_expr state =
    match direct_id_of_sil_lvar lhs state with
    | Some lhs_direct_id ->
      let rhs_norm = Formula.normalize_expr rhs_expr in
      assign_to_variable lhs_direct_id rhs_norm state
    | None ->
      let rhs_norm = Formula.normalize_expr rhs_expr in
      let lhs_norm = Formula.normalize_expr lhs_expr in
      let state = match lhs_norm with
        | Expr.Var id ->
          let state, rewrite_spatial = clear_stale_value_constraints id state in
          { state with current = { state.current with
            spatial = rewrite_spatial state.current.spatial } }
        | _ -> state
      in
      let exp = Expr.BinOp (Peq, lhs_norm, rhs_norm) in
      [{ state with current = { state.current with pure = exp :: state.current.pure } }]

  (** Store dereference pipeline: checks freed → base bounds → end bounds → heap match *)
  and exec_store_deref loc instr tenv lhs_typ lhs_var_id lhs_offset rhs_expr state =
    let cell_size = typ_size_of tenv lhs_typ in
    [state]
    |> concat_map_ok_states
      (deref_check_freed loc instr lhs_var_id)
    |> concat_map_ok_states
      (deref_check_base loc instr lhs_var_id lhs_offset cell_size)
    |> concat_map_ok_states
      (deref_check_end loc instr lhs_var_id lhs_offset cell_size)
    |> concat_map_ok_states
      (store_match_heap loc instr lhs_typ lhs_var_id lhs_offset cell_size rhs_expr)

  (** Attempts to match heap predicates for store dereference. Resolves both
      current and missing matches, then dispatches:
      - Both match → formal pointer, mirror split to both sides
      - Current only → local allocation, split current only
      - Missing only → bug (missing mirroring failure)
      - Neither → fallback to create missing cell *)
  and store_match_heap loc instr lhs_typ lhs_var_id lhs_offset cell_size rhs_expr state =
    let rhs_norm = Formula.normalize_expr rhs_expr in
    let curr_hps, curr_rest, miss_hps, miss_rest =
      heap_find_block_fragments state lhs_var_id lhs_offset cell_size
    in
    let curr_split = heap_try_block_split curr_hps lhs_var_id lhs_offset cell_size in
    let miss_split = heap_try_block_split miss_hps lhs_var_id lhs_offset cell_size in
    match curr_split, miss_split with
    | Some block_split_res, Some _ ->
      store_split_formal lhs_typ rhs_norm block_split_res
        curr_hps curr_rest miss_hps miss_rest state
    | Some block_split_res, None ->
      store_split_local lhs_typ rhs_norm block_split_res curr_hps curr_rest state
    | None, Some _ ->
      Logging.die InternalError
        "store_match_heap: found match in missing but not in current (mirroring bug)"
    | None, None ->
      store_create_missing_cell loc instr lhs_typ lhs_var_id lhs_offset cell_size rhs_norm state

  (** Extracts block split args and optional old_dest from a [block_split_res],
      dispatching [ExpExactMatch] stale constraint cleanup.
      Returns the old destination variable and its value (looked up BEFORE clearing)
      so callers can resolve self-reassignment in [store_dereference_assign] *)
  and store_extract_split_args block_split_res state =
    match block_split_res with
    | ExpExactMatch { block_split_args; old_dest } ->
      let old_dest_value = match old_dest with
        | Expr.Var id -> Formula.find_peq_value id state.current.pure
        | _ -> None
      in
      let state, rewrite_spatial = match old_dest with
        | Expr.Var id -> clear_stale_value_constraints id state
        | _ -> (state, Fun.id)
      in
      (state, block_split_args, rewrite_spatial, Some old_dest, old_dest_value)
    | BlockExactMatch args | BlockEdgeMatch args | BlockMiddleMatch args ->
      (state, args, Fun.id, None, None)

  (** Handles a block split for a local allocation (found in current only).
      Transforms current spatial, runs assignment, prepends new [ExpPointsTo] to current *)
  and store_split_local lhs_typ rhs_norm block_split_res curr_hps curr_rest state =
    let state, { to_remove; to_add; new_exp_points_to; new_dest_id }, rewrite_spatial,
        old_dest, old_dest_value =
      store_extract_split_args block_split_res state
    in
    let curr_spatial = transform_spatial to_remove curr_hps to_add curr_rest in
    let state = { state with current = { state.current with spatial = curr_spatial } } in
    let lhs_expr = Expr.Var new_dest_id in
    let assign_res = store_dereference_assign state lhs_typ new_dest_id lhs_expr rhs_norm
      ~old_dest ~old_dest_value in
    let state, new_exp_points_to = store_fixup_pto assign_res new_exp_points_to lhs_expr new_dest_id in
    let state = { state with current = { state.current with
      spatial = rewrite_spatial state.current.spatial } } in
    [{ state with current = { state.current with
      spatial = new_exp_points_to :: state.current.spatial } }]

  (** Handles a block split for a formal pointer (found in both current and missing).
      For [Block*Match] (first access): transforms both current and missing spatial,
      adds new [ExpPointsTo] to both.
      For [ExpExactMatch] (reassignment): only updates current — missing precondition
      cell is left intact to preserve the pre-postcondition connection *)
  and store_split_formal lhs_typ rhs_norm block_split_res
      curr_hps curr_rest miss_hps miss_rest state =
    match block_split_res with
    | ExpExactMatch _ ->
      (* Reassignment: treat like local — only update current, leave missing intact *)
      store_split_local lhs_typ rhs_norm block_split_res curr_hps curr_rest state
    | BlockExactMatch _ | BlockEdgeMatch _ | BlockMiddleMatch _ ->
      (* First access: mirror split to both current and missing *)
      let state, { to_remove; to_add; new_exp_points_to; new_dest_id }, _rewrite_spatial,
          old_dest, old_dest_value =
        store_extract_split_args block_split_res state
      in
      let curr_spatial = transform_spatial to_remove curr_hps to_add curr_rest in
      let miss_spatial = transform_spatial to_remove miss_hps to_add miss_rest in
      let state = { state with
        current = { state.current with spatial = curr_spatial };
        missing = { state.missing with spatial = miss_spatial } }
      in
      let lhs_expr = Expr.Var new_dest_id in
      let assign_res = store_dereference_assign state lhs_typ new_dest_id lhs_expr rhs_norm
        ~old_dest ~old_dest_value in
      let state, new_exp_points_to = store_fixup_pto assign_res new_exp_points_to lhs_expr new_dest_id in
      [{ state with
        current = { state.current with
          spatial = new_exp_points_to :: state.current.spatial };
        missing = { state.missing with
          spatial = new_exp_points_to :: state.missing.spatial } }]

  (** Fixes up [new_exp_points_to] after assignment: when an address was stored,
      replaces [canonical_rhs] references in the source/size with the cell variable *)
  and store_fixup_pto assign_res new_exp_points_to lhs_expr new_dest_id =
    match assign_res with
    | ValueStored state | AliasStored state ->
      (state, new_exp_points_to)
    | AddressStored { state; canonical_rhs } ->
      let src, size = match new_exp_points_to with
        | Formula.ExpPointsTo (src, size, _) -> (src, size)
        | _ -> Logging.die InternalError
                 "store_fixup_pto: expected ExpPointsTo for new cell"
      in
      (state, Formula.ExpPointsTo (
        Formula.expr_replace ~old_:canonical_rhs ~new_:lhs_expr src,
        Formula.expr_replace ~old_:canonical_rhs ~new_:lhs_expr size,
        Expr.Var new_dest_id))

  (** Creates missing ExpPointsTo when no heap predicate matches for store dereference.
      Should not happen in practice (deref_create_missing_base/end create BlockPointsTo
      that matches), but kept for consistency. Generates Freed error contract + ok *)
  and store_create_missing_cell loc instr lhs_typ lhs_var_id lhs_offset cell_size rhs_norm state =
    let err_freed = { state with status = Error (err_store_deref_missing_cell, loc, instr);
      missing = { state.missing with pure =
        Expr.UnOp (Freed, Var lhs_var_id) :: state.missing.pure } }
    in
    let cell_id = Id.fresh () in
    let lhs_expr = Expr.Var cell_id in
    let missing_spatial = Formula.ExpPointsTo (
      Expr.BinOp (Pplus, Var lhs_var_id, Const (Int lhs_offset)),
      Expr.Const (Int cell_size),
      lhs_expr)
    in
    let assign_res = store_dereference_assign state lhs_typ cell_id lhs_expr rhs_norm
      ~old_dest:None ~old_dest_value:None in
    let state, missing_spatial = match assign_res with
      | ValueStored state | AliasStored state ->
        (state, missing_spatial)
      | AddressStored { state; canonical_rhs } ->
        let src, size = match missing_spatial with
          | Formula.ExpPointsTo (src, size, _) -> (src, size)
          | _ -> Logging.die InternalError
                   "store_create_missing_cell: expected ExpPointsTo"
        in
        (state, Formula.ExpPointsTo (
          Formula.expr_replace ~old_:canonical_rhs ~new_:lhs_expr src,
          Formula.expr_replace ~old_:canonical_rhs ~new_:lhs_expr size,
          lhs_expr))
    in
    let ok_state = { state with
      missing = { state.missing with spatial = missing_spatial :: state.missing.spatial };
      current = { state.current with spatial = missing_spatial :: state.current.spatial } } in
    [err_freed; ok_state]

  (* ==================== SIL Call - malloc ==================== *)

  and exec_malloc_instr lhs typ actual state =
    let lhs_id = Id.fresh () in
    let state = { state with
      vars = VarIdMap.add lhs_id (Var.of_id lhs) state.vars;
      types = VarIdMap.add lhs_id typ state.types }
    in
    let source = Expr.Var lhs_id in
    (* we assume expression denotes to some size_t since it passed compilation *)
    let size = Formula.normalize_expr actual in
    (* try to evaluate the size *)
    let size = match eval_expr_to_int64_opt size state with
      | Some i -> Expr.Const (Int i)
      | None -> size
    in
    (* success state: block allocated with Base/End constraints *)
    let ok_state = { state with
      current = {
        spatial = Formula.BlockPointsTo (source, size) :: state.current.spatial;
        pure =
          Expr.BinOp (Peq, UnOp (Base, source), source) ::
          Expr.BinOp (Peq, UnOp (End, source), BinOp (Pplus, source, size)) ::
          state.current.pure } } in
    (* failure state: malloc returned NULL *)
    let null_state = { state with
      current = { state.current with
        pure =
          Expr.BinOp (Peq, source, Expr.null) ::
          Expr.BinOp (Peq, UnOp (Base, source), Expr.zero) ::
          Expr.BinOp (Peq, UnOp (End, source), Expr.zero) ::
          state.current.pure } } in
    [ok_state; null_state]

  (* ==================== SIL Call - free ==================== *)

  (** free(NULL) is a no-op per the C standard. Recovers base pointer and offset,
      checks for null (both literal and resolved), then delegates to freed/base checks.
      Null pointer with non-zero offset is UB — terminal error *)
  and exec_free_instr loc instr tenv actual_expr state =
    if Formula.is_null_expr actual_expr then
      [state]
    else
      match base_and_offset_of_expr actual_expr state with
      | Some (base_id, offset) ->
        let is_null = match Formula.lookup_pure_const_exp_of_id base_id state.current.pure with
          | Some e -> Formula.is_null_expr e
          | None -> false
        in
        if is_null && Int64.equal offset 0L then
          [state]
        else if is_null then
          [{ state with status = Error (err_free_non_base_offset, loc, instr) }]
        else
          free_compute_offset loc instr tenv base_id offset state
      | None ->
        [{ state with status = Error (err_free_no_base_pointer, loc, instr) }]

  (** Recovers element size from type info, then checks for double-free
      before proceeding to base lookup. Offset is already in bytes
      (scaled during SIL→Expr translation by [sil_ptr_arith_to_expr]) *)
  and free_compute_offset loc instr tenv base_id offset state =
    let element_size =
      match VarIdMap.find_opt base_id state.types with
      | Some typ ->
        begin match typ_size_of_element_opt tenv typ with
        | Some 0L -> 1L
        | Some size -> size
        | None -> 1L
        end
      | None -> 1L
    in
    [state]
    |> concat_map_ok_states (deref_check_freed loc instr base_id)
    |> concat_map_ok_states (free_lookup_base loc instr base_id offset element_size)

  (** Looks up Base(Var id) in current. If found and non-zero, delegates to [free_with_base].
      If found and zero, reports unallocated error. If not found, creates missing contract *)
  and free_lookup_base loc instr id offset cell_size state =
    match Formula.lookup_pure_base_expr id state.current.pure with
    | Some base_exp ->
      if Formula.is_zero_expr base_exp then
        [{ state with status = Error (err_free_unallocated, loc, instr) }]
      else
        free_with_base loc instr id offset base_exp state
    | None ->
      free_create_missing_contract loc instr id offset cell_size state

  (** Base found in current — compares offset against base offset to determine validity.
      Equal offset: happy path (cleanup + Freed). Lower offset: attempt to lower bound
      in missing precondition. Higher offset: non-base-pointer free error *)
  and free_with_base loc instr id offset base_exp state =
    (* TODO: eval_expr_offset falls back to zero for unknown formals — add comment/handling *)
    let base_offset = eval_expr_offset base_exp id state in
    if Int64.equal base_offset offset then
      (* happy path: offset matches base, cleanup and add Freed to current *)
      let state = cleanup_after_free id state in
      let pure = Expr.UnOp (Freed, Var id) :: state.current.pure in
      let ok = { state with current = { state.current with pure } } in
      match Formula.lookup_pure_base_expr id state.missing.pure with
      | Some miss_base_exp ->
        (* memory allocated outside the method, need to change leq -> eq *)
        let err, ok = 
          free_create_non_base_error_contract loc instr id offset state,
          free_mutate_base_ok_contract id miss_base_exp offset ok
        in [err; ok]
      | None -> [ok] (* memory allocated locally *)
    else if Int64.compare offset base_offset < 0 then
      (* offset below current base — check missing for lowering *)
      begin match Formula.lookup_pure_base_expr id state.missing.pure with
      | Some miss_base_exp ->
        (* Found in missing — lower bound in precondition only, then free. *)
        let to_remove = Expr.BinOp (Plesseq, UnOp (Base, Var id), miss_base_exp) in
        let to_add = Expr.BinOp (Plesseq,
          UnOp (Base, Var id),
          BinOp (Pplus, Var id, Const (Int offset))) in
        let missing_pure = Stdlib.List.filter
          (fun e -> not (Expr.equal e to_remove)) state.missing.pure in
        let state = { state with missing =
          { state.missing with pure = to_add :: missing_pure } }
        in
        let pure = Expr.UnOp (Freed, Var id) :: state.current.pure in
        let ok = { state with current = { state.current with pure } } in
        let state = cleanup_after_free id state in
        let err, ok =
          free_create_non_base_error_contract loc instr id offset state,
          free_mutate_base_ok_contract id miss_base_exp offset ok
        in [err; ok]
      | None ->
        [{ state with status = Error (err_free_non_base_offset, loc, instr) }]
      end
    else
      (* offset above base — by definition a non-base-pointer free *)
      [{ state with status = Error (err_free_non_base_offset, loc, instr) }]

  (** Creates [Base(id) != id + offset] error contract *)
  and free_create_non_base_error_contract loc instr id offset state =
    let to_add = Expr.BinOp (Pneq, UnOp(Base, Var id),
      BinOp (Pplus, Var id, Const (Int offset))) in
    let missing_pure = to_add :: state.missing.pure in
    { state with
      status = Error (err_free_non_base_offset, loc, instr);
      missing = { state.missing with pure = missing_pure } }

  (** Replaces [Base(id) <= base_exp] pure constraint with
      [Base(id) == id + offset] constraint in missing *)
  and free_mutate_base_ok_contract id base_exp offset state =
    let to_remove = Expr.BinOp (Plesseq, UnOp(Base, Var id), base_exp) in
    let to_add = Expr.BinOp (Peq, UnOp(Base, Var id),
      BinOp (Pplus, Var id, Const (Int offset))) in
    let missing_pure = Stdlib.List.filter
      (fun e -> not (Expr.equal e to_remove)) state.missing.pure in
    { state with missing = { state.missing with pure = to_add :: missing_pure } }

  (** Base not found in current — creates missing resources (Base, End, BlockPointsTo)
      in missing only (NOT mirrored to current — Base/End + Freed is contradictory).
      Returns both an error contract and an ok contract with the missing resources *)
  and free_create_missing_contract loc instr id offset cell_size state =    
    let access_end = Stdlib.Int64.add offset cell_size in
    (* Error contract 1: access not equal to block start *)
    let err_base = free_create_non_base_error_contract loc instr id offset state in
    (* Error contract 2: double free *)
    let err_freed = { state with status = Error (err_deref_use_after_free, loc, instr);
      missing = { state.missing with pure =
        Expr.UnOp (Freed, Var id) :: state.missing.pure } }
    in
    (* Ok contract 1: variable is null *)
    let ok_null = { state with missing =
      { state.missing with pure =
        Expr.BinOp (Peq, BinOp (Pplus, Var id, Const (Int offset)),
        Expr.null) :: state.missing.pure } }
    in
    (* OK contract 2: full resources — Base + End bounds + BlockPointsTo at access point *)
    let missing_base = Expr.BinOp (Peq,
      UnOp (Base, Var id),
      BinOp (Pplus, Var id, Const (Int offset))) in
    let missing_end = Expr.BinOp (Plesseq,
      BinOp (Pplus, Var id, Const (Int access_end)),
      UnOp (End, Var id)) in
    let missing_heap_pred = Formula.BlockPointsTo (
      Expr.Var id,
      Expr.Const (Int cell_size)) in
    let missing = { state.missing with
      spatial = missing_heap_pred :: state.missing.spatial;
      pure = missing_base :: missing_end :: state.missing.pure } in
    let pure = Expr.UnOp (Freed, Var id) :: state.current.pure in
    let ok_allocated = { state with
      current = { state.current with pure };
      missing } in
    [err_base; err_freed; ok_null; ok_allocated]


  (* ==================== SIL Call - memcpy ==================== *)

  (** Handles [memcpy(dest, src, size)] — copies [size] bytes from [src] to [dest].
      Returns [dest] pointer as the result (assigned to [ret_id]).

      Splits into two disjunctive paths based on [size]:
      - **Zero-size path:** no memory access, assigns [ret_id = dest] (address assign).
        Skipped when size is provably non-zero (via [eval_expr_to_int64_opt] or Astral).
      - **Non-zero path:** delegates to [exec_memcpy_deref] for freed/base/end/overlap
        checks and spatial copy. Skipped when size is provably zero.

      When [size] is symbolic and cannot be resolved, both paths are produced.
      Astral is used as fallback to refine the zero/non-zero split when static
      evaluation fails — checks [SAT(size == 0)] and [SAT(size != 0)] against the
      current state to prune infeasible paths.

      Produces terminal error states when [dest] or [src] cannot be decomposed
      into [(base_id, concrete_offset)] by [base_and_offset_of_expr] *)
  and exec_memcpy_instr loc instr tenv state ret ret_typ dest dest_expr src src_expr size size_expr =
    let ret_id = Id.fresh () in
    let state = { state with
      vars = VarIdMap.add ret_id (Var.of_id ret) state.vars;
      types = VarIdMap.add ret_id ret_typ state.types }
    in
    (* Resolve base+offset for both pointers — terminal error if either is unresolvable *)
    match base_and_offset_of_expr dest_expr state, base_and_offset_of_expr src_expr state with
    | None, _ ->
      [{ state with status = Error (err_load_deref_no_base, loc, instr) }]
    | _, None ->
      [{ state with status = Error (err_store_deref_no_base, loc, instr) }]
    | Some (dest_id, dest_off), Some (src_id, src_off) ->
      let size_val = eval_expr_to_int64_opt size_expr state in
      let is_zero, is_non_zero =
        match size_val with
        | Some i -> Int64.equal i 0L, not (Int64.equal i 0L)
        | None ->
          let is_zero_sat = AtlasAstral.check_sat_with_condition state
            (BinOp (Peq, size_expr, Const (Int 0L))) in
          let is_nonzero_sat = AtlasAstral.check_sat_with_condition state
            (BinOp (Pneq, size_expr, Const (Int 0L))) in
          match is_zero_sat, is_nonzero_sat with
          | `Unsat, _ -> false, true
          | _, `Unsat -> true, false
          | _ -> false, false
      in
      let zero_size_states =
        if is_non_zero then []
        else exec_memcpy_addr_assign loc instr state ret_id dest_id dest_off src_id src_off
      in
      let non_zero_size_states =
        if is_zero then []
        else exec_memcpy_deref loc instr tenv state ret_id
          dest_id dest_off src_id src_off size_expr size_val
      in
      zero_size_states @ non_zero_size_states

  (** Zero-size memcpy: per C standard 7.21.1, pointers must still be valid even
      when n=0. Checks freed/base/end for both pointers using access size 1L
      (to avoid zero-sized blocks in missing), then assigns ret = dest *)
  and exec_memcpy_addr_assign loc instr state ret_id dest_id dest_off src_id src_off =
    [state]
    |> concat_map_ok_states
      (deref_check_freed loc instr dest_id)
    |> concat_map_ok_states
      (deref_check_freed loc instr src_id)
    |> concat_map_ok_states
      (deref_check_base loc instr dest_id dest_off 1L)
    |> concat_map_ok_states
      (deref_check_base loc instr src_id src_off 1L)
    |> concat_map_ok_states
      (deref_check_end loc instr dest_id dest_off 1L)
    |> concat_map_ok_states
      (deref_check_end loc instr src_id src_off 1L)
    |> List.map ~f:(fun state ->
      match state.status with
      | Ok ->
        let dest_canonical = canonical_expr state.subst dest_id dest_off in
        { state with subst = VarIdMap.add ret_id dest_canonical state.subst }
      | _ -> state)

  and exec_memcpy_deref loc instr tenv state ret_id dest_id dest_off src_id src_off size_expr size_val =
    let size =
      match size_val with
      | Some s -> s
      | None -> 1L (* TODO: symbolic sizes not fully supported *)
    in
    (* Recover actual types from state.types — SIL passes void* for memcpy args *)
    let typ_of_element id =
      match VarIdMap.find_opt id state.types with
      | Some typ ->
        begin match typ.Typ.desc with
        | Typ.Tptr (elt, _) -> elt
        | Typ.Tarray { elt } -> elt
        | _ -> Typ.mk Typ.Tvoid
        end
      | None -> Typ.mk Typ.Tvoid
    in
    let dest_elem_typ = typ_of_element dest_id in
    let src_elem_typ = typ_of_element src_id in
    let dest_elem_size = typ_size_of tenv dest_elem_typ in
    let src_elem_size = typ_size_of tenv src_elem_typ in
    [state]
    |> concat_map_ok_states
      (deref_check_freed loc instr dest_id)
    |> concat_map_ok_states
      (deref_check_freed loc instr src_id)
    |> concat_map_ok_states
      (deref_check_base loc instr dest_id dest_off size)
    |> concat_map_ok_states
      (deref_check_base loc instr src_id src_off size)
    |> concat_map_ok_states
      (deref_check_end loc instr dest_id dest_off size)
    |> concat_map_ok_states
      (deref_check_end loc instr src_id src_off size)
    |> concat_map_ok_states
      (memcpy_check_overlap loc instr dest_id dest_off src_id src_off size)
    |> concat_map_ok_states
      (memcpy_copy_cells loc instr tenv ret_id dest_id dest_off dest_elem_typ dest_elem_size src_id src_off src_elem_typ src_elem_size size)

  (** Checks for overlapping memory regions in memcpy.
      When [dest_id] and [src_id] refer to different blocks (different variable ids),
      overlap is impossible — passes through.
      When they refer to the same block, checks whether the concrete offsets are
      far enough apart: [|dest_off - src_off| >= size]. If not, produces an error
      contract for undefined behaviour (overlapping memcpy).
      NOTE: does not support symbolic offsets — assumes concrete offset arithmetic *)
  and memcpy_check_overlap loc instr dest_id dest_off src_id src_off size state =
    if not (Id.equal dest_id src_id) then
      (* Different blocks — no overlap possible *)
      [state]
    else
      let diff = Int64.abs (Stdlib.Int64.sub dest_off src_off) in
      if Int64.compare diff size >= 0 then
        (* Same block but ranges do not overlap *)
        [state]
      else
        (* Same block and ranges overlap — undefined behaviour *)
        [{ state with status = Error (err_memcpy_overlap, loc, instr) }]

  (** Performs the actual memory copy for memcpy. After all safety checks have
      passed, extracts source cells from the interval \[src_off, src_off + size)\],
      then writes each source cell's value to the corresponding destination offset
      via [store_match_heap]. Finally assigns [ret_id = dest].

      Dispatches to [heap_extract_interval_formal] or [heap_extract_interval_local]
      based on whether the source block exists in missing (formal) or not (local).
      The dest side is always written via [store_match_heap] which handles its own
      formal/local dispatch internally.

      NOTE: assumes concrete offsets and sizes.
      When the element type is a struct, dispatches to struct-aware chopping
      via [interval_trim_and_convert_struct] which uses field-aligned cell sizes.
      Misaligned copies (size not aligned to field boundaries) raise InternalError. *)
  and memcpy_copy_cells loc instr tenv ret_id dest_id dest_off dest_elem_typ dest_elem_size src_id src_off src_elem_typ src_elem_size size state =
    (* if elem size is 0L, change it to 1L to prevent infinite loop *)
    let dest_elem_size, src_elem_size =
      (if Int64.equal dest_elem_size 0L then 1L else dest_elem_size),
      (if Int64.equal src_elem_size 0L then 1L else src_elem_size)
    in
    (* Detect struct element type — compute field layout for struct-aware chopping *)
    let src_struct_layout = match struct_field_layout tenv src_elem_typ with
      | Some layout ->
        let struct_size = List.fold layout ~init:0L ~f:(fun acc (_, sz, _) -> Stdlib.Int64.add acc sz) in
        Some (layout, struct_size)
      | None -> None
    in
    (* Extract source cells *)
    let curr_in, curr_rest, miss_in, miss_rest =
      heap_find_block_interval state src_id src_off size
    in
    let mirror = List.length miss_in > 0 in
    let state, src_offset_map =
      if mirror then
        heap_extract_interval_formal state src_id src_off size src_elem_size
          src_elem_typ ?struct_layout:src_struct_layout
          curr_in curr_rest miss_in miss_rest
      else
        heap_extract_interval_local state src_id src_off size src_elem_size
          src_elem_typ ?struct_layout:src_struct_layout
          curr_in curr_rest
    in
    (* For each source cell, compute the dest offset and call store_match_heap.
       Cell size is derived from the source cell's registered type — correct for
       both uniform (non-struct) and variable-sized (struct field) cases *)
    let states = List.fold src_offset_map ~init:[state] ~f:(fun acc (src_rel_off, src_dest_id) ->
      let dest_abs_off = Stdlib.Int64.add dest_off src_rel_off in
      let rhs_expr = Expr.Var src_dest_id in
      let cell_typ, cell_size = match VarIdMap.find_opt src_dest_id state.types with
        | Some t -> (t, typ_size_of tenv t)
        | None -> (dest_elem_typ, dest_elem_size)
      in
      concat_map_ok_states
        (store_match_heap loc instr cell_typ dest_id dest_abs_off cell_size rhs_expr)
        acc)
    in
    (* Assign ret_id = dest *)
    List.map states ~f:(fun s ->
      match s.status with
      | Ok ->
        let dest_canonical = canonical_expr s.subst dest_id dest_off in
        { s with subst = VarIdMap.add ret_id dest_canonical s.subst }
      | Error _ -> s)


  (* ==================== Pointer Arithmetic Checks ==================== *)

  (** Scans a SIL expression for pointer arithmetic nodes ([PlusPI], [MinusPI],
      [Lindex]) and runs bound checks on each. Returns the input states with
      additional error contracts for any OOB pointer arithmetic found.
      The base pointer is always e1 (LHS) per SIL convention.
      Collects [(base_sil_exp, full_arith_sil_exp)] pairs *)
  and check_sil_ptr_arith loc instr tenv sil_exp state =
    let arith_nodes = collect_sil_ptr_arith_nodes sil_exp in
    List.fold arith_nodes ~init:[state] ~f:(fun acc (base_sil, full_sil) ->
      concat_map_ok_states
        (ptrplus_check loc instr tenv base_sil full_sil)
        acc)

  (** Scans a SIL expression for [MinusPP] nodes and runs pointer subtraction
      checks on each. Runs unconditionally (MinusPP result is an integer,
      not gated by [is_pointer_type]) *)
  and check_sil_ptrsub loc instr tenv sil_exp state =
    let ptrsub_nodes = collect_sil_ptrsub_nodes sil_exp in
    List.fold ptrsub_nodes ~init:[state] ~f:(fun acc (lhs_sil, rhs_sil) ->
      concat_map_ok_states
        (ptrsub_check loc instr tenv lhs_sil rhs_sil)
        acc)

  (** Collects all pointer arithmetic nodes from a SIL expression.
      Returns a list of [(base_sil_exp, full_arith_sil_exp)] pairs.
      The full expression is needed for correct byte-scaled translation *)
  and collect_sil_ptr_arith_nodes sil_exp =
    let rec aux acc exp =
      match Exp.ignore_cast exp with
      | Exp.BinOp ((Binop.PlusPI | Binop.MinusPI), e1, _) ->
        let acc = (e1, exp) :: acc in
        aux acc e1
      | Exp.Lindex (base, _) ->
        let acc = (base, exp) :: acc in
        aux acc base
      | Exp.BinOp (_, e1, e2) ->
        let acc = aux acc e1 in
        aux acc e2
      | Exp.UnOp (_, e, _) -> aux acc e
      | _ -> acc
    in
    aux [] sil_exp

  (** Collects all [MinusPP] nodes from a SIL expression.
      Returns a list of [(lhs_sil_exp, rhs_sil_exp)] pairs *)
  and collect_sil_ptrsub_nodes sil_exp =
    let rec aux acc exp =
      match Exp.ignore_cast exp with
      | Exp.BinOp (Binop.MinusPP, e1, e2) ->
        (e1, e2) :: acc
      | Exp.BinOp (_, e1, e2) ->
        let acc = aux acc e1 in
        aux acc e2
      | Exp.UnOp (_, e, _) -> aux acc e
      | _ -> acc
    in
    aux [] sil_exp

  (** Entry point for a single pointer arithmetic check.
      Extracts base variable id, translates the full arithmetic expression
      to get byte-scaled result, then runs the check pipeline:
      freed → base+end lookup → bounds comparison *)
  and ptrplus_check loc instr tenv base_sil full_sil state =
    match sil_extract_base_var_id base_sil state with
    | None ->
      [{ state with status = Error (err_ptrplus_no_base_var, loc, instr) }]
    | Some base_id ->
      match VarIdMap.find_opt base_id state.types with
      | None ->
        Logging.die InternalError "pointer arithmetic: base variable %d has no type" base_id
      | Some _typ ->
        (* Translate the full SIL expression — sil_ptr_arith_to_expr / sil_array_offset_bytes
           handle byte scaling correctly *)
        let result_expr = sil_exp_to_expr full_sil tenv state in
        (* Extract byte offset relative to base variable *)
        let result_offset = eval_expr_offset result_expr base_id state in
        ptrplus_check_freed loc instr tenv base_id result_expr result_offset state

  (** Entry point for a MinusPP (pointer subtraction) check.
      Extracts base variable ids from both operands, checks freed on both,
      looks up Base for LHS, then dispatches:
      - Base found & ids match → null check only
      - Base found & ids differ → check RHS within LHS bounds
      - Base not found & ids match → create minimal missing contracts
      - Base not found & ids differ → create full missing contracts with bound checks *)
  and ptrsub_check loc instr tenv lhs_sil rhs_sil state =
    match sil_extract_base_var_id lhs_sil state, sil_extract_base_var_id rhs_sil state with
    | None, _ | _, None ->
      [{ state with status = Error (err_ptrsub_no_base_var, loc, instr) }]
    | Some x_id, Some y_id ->
      (* Check freed on both operands *)
      if is_freed_expr x_id state then
        [{ state with status = Error (err_ptrsub_use_after_free, loc, instr) }]
      else if is_freed_expr y_id state then
        [{ state with status = Error (err_ptrsub_use_after_free, loc, instr) }]
      else
        let base_bound = lookup_pure_bound_expr x_id Expr.Base state in
        let ids_match = Int.equal x_id y_id in
        match base_bound, ids_match with
        (* Base found & same block — null check only *)
        | (Some base_exp, _), true ->
          ptrsub_base_found_same loc instr base_exp state
        (* Base in current only & different ids — local memory, terminal error *)
        | (Some _, None), false ->
          ptrsub_current_found_diff loc instr state
        (* Base in missing & different ids — formal memory, error + ok contracts *)
        | (Some _, Some _), false ->
          let end_bound = lookup_pure_bound_expr x_id Expr.End state in
          ptrsub_missing_found_diff loc instr x_id y_id end_bound state
        (* No base & same variable — minimal contracts *)
        | (None, _), true ->
          ptrsub_no_base_same loc instr x_id state
        (* No base & different ids — full contracts with bound checks *)
        | (None, _), false ->
          ptrsub_no_base_diff loc instr x_id y_id state

  (** Base in current only, different variable ids — two separate local
      allocations, definitely different blocks. Terminal error *)
  and ptrsub_current_found_diff loc instr state =
    [{ state with status = Error (err_ptrsub_different_blocks, loc, instr) }]

  (** Base in missing, different variable ids — formal memory, could be same
      block at runtime. Generate error contracts (y outside x's block) +
      ok contract (y within x's block) using existing bounds *)
  and ptrsub_missing_found_diff loc instr x_id y_id end_bound state =
    (* Error: y below Base(x) — different blocks *)
    let err_below = { state with
      status = Error (err_ptrsub_different_blocks, loc, instr);
      missing = { state.missing with pure =
        Expr.BinOp (Pless, Var y_id, Expr.UnOp (Base, Var x_id))
        :: state.missing.pure } }
    in
    (* Error: y above End(x) — different blocks *)
    let err_above = { state with
      status = Error (err_ptrsub_different_blocks, loc, instr);
      missing = { state.missing with pure =
        Expr.BinOp (Pless, Expr.UnOp (End, Var x_id), Var y_id)
        :: state.missing.pure } }
    in
    (* OK: Base(x) <= y <= End(x) *)
    let y_geq_base = Expr.BinOp (Plesseq, Expr.UnOp (Base, Var x_id), Var y_id) in
    let y_leq_end = match fst end_bound with
      | Some _ -> Expr.BinOp (Plesseq, Var y_id, Expr.UnOp (End, Var x_id))
      | None -> Logging.die InternalError
          "ptrsub_missing_found_diff: Base found but End missing for %d" x_id
    in
    let ok = { state with
      missing = { state.missing with pure =
        y_geq_base :: y_leq_end :: state.missing.pure };
      current = { state.current with pure =
        y_geq_base :: y_leq_end :: state.current.pure } }
    in
    [err_below; err_above; ok]

  (** No Base, different variable ids — first access, full contracts.
      err_null (Base(x)==0), err_freed (x), err_below (y < Base(x)),
      err_above (y > End(x)), ok (Base(x) <= y <= End(x) with Base/End mirrored) *)
  and ptrsub_no_base_diff loc instr x_id y_id state =
    (* Error: null pointer (Base==End==0) *)
    let err_null = { state with
      status = Error (err_ptrsub_null, loc, instr);
      missing = { state.missing with pure =
        Expr.BinOp (Peq, Expr.UnOp (Base, Var x_id), Expr.Const (Int 0L))
        :: Expr.BinOp (Peq, Expr.UnOp (End, Var x_id), Expr.Const (Int 0L))
        :: state.missing.pure } }
    in
    (* Error: x freed *)
    let err_freed = { state with
      status = Error (err_ptrsub_use_after_free, loc, instr);
      missing = { state.missing with pure =
        Expr.UnOp (Freed, Var x_id) :: state.missing.pure } }
    in
    (* Error: y below Base(x) — different blocks *)
    let err_below = { state with
      status = Error (err_ptrsub_different_blocks, loc, instr);
      missing = { state.missing with pure =
        Expr.BinOp (Pless, Var y_id, Expr.UnOp (Base, Var x_id))
        :: state.missing.pure } }
    in
    (* Error: y above End(x) — different blocks *)
    let err_above = { state with
      status = Error (err_ptrsub_different_blocks, loc, instr);
      missing = { state.missing with pure =
        Expr.BinOp (Pless, Expr.UnOp (End, Var x_id), Var y_id)
        :: state.missing.pure } }
    in
    (* OK: Base(x)!=0 & End(x)!=0 & Base(x) <= y <= End(x) *)
    let base_neq = Expr.BinOp (Pneq, Expr.UnOp (Base, Var x_id), Expr.Const (Int 0L)) in
    let end_neq = Expr.BinOp (Pneq, Expr.UnOp (End, Var x_id), Expr.Const (Int 0L)) in
    let y_geq_base = Expr.BinOp (Plesseq, Expr.UnOp (Base, Var x_id), Var y_id) in
    let y_leq_end = Expr.BinOp (Plesseq, Var y_id, Expr.UnOp (End, Var x_id)) in
    let ok = { state with
      missing = { state.missing with pure =
        base_neq :: end_neq :: y_geq_base :: y_leq_end :: state.missing.pure };
      current = { state.current with pure =
        base_neq :: end_neq :: y_geq_base :: y_leq_end :: state.current.pure } }
    in
    [err_null; err_freed; err_below; err_above; ok]

  (** No Base, same variable — first access via pointer subtraction (e.g. p - p).
      Creates minimal missing contracts: err_freed, err_null, ok with
      Base!=0 & End!=0 mirrored to current *)
  and ptrsub_no_base_same loc instr x_id state =
    (* Error: freed *)
    let err_freed = { state with
      status = Error (err_ptrsub_use_after_free, loc, instr);
      missing = { state.missing with pure =
        Expr.UnOp (Freed, Var x_id) :: state.missing.pure } }
    in
    (* Error: null *)
    let err_null = { state with
      status = Error (err_ptrsub_null, loc, instr);
      missing = { state.missing with pure =
        Expr.BinOp (Peq, Expr.UnOp (Base, Var x_id), Expr.Const (Int 0L))
        :: state.missing.pure } }
    in
    (* OK: Base!=0 & End!=0 *)
    let base_neq = Expr.BinOp (Pneq, Expr.UnOp (Base, Var x_id), Expr.Const (Int 0L)) in
    let end_neq = Expr.BinOp (Pneq, Expr.UnOp (End, Var x_id), Expr.Const (Int 0L)) in
    let ok = { state with
      missing = { state.missing with pure =
        base_neq :: end_neq :: state.missing.pure };
      current = { state.current with pure =
        base_neq :: end_neq :: state.current.pure } }
    in
    [err_freed; err_null; ok]

  (** Base found, same canonical variable — both pointers are in the same block.
      Only check for null (Base==0 means no allocation) *)
  and ptrsub_base_found_same loc instr base_exp state =
    if Formula.is_zero_expr base_exp then
      [{ state with status = Error (err_ptrsub_null, loc, instr) }]
    else
      [state]

  (** Step 1: Check if base pointer has been freed *)
  and ptrplus_check_freed loc instr tenv base_id result_expr result_offset state =
    if is_freed_expr base_id state then
      [{ state with status = Error (err_ptrplus_use_after_free, loc, instr) }]
    else
      ptrplus_check_bounds loc instr tenv base_id result_expr result_offset state

  (** Step 2: Look up Base and End simultaneously, dispatch based on what's found *)
  and ptrplus_check_bounds loc instr _tenv base_id result_expr result_offset state =
    let base_bound = lookup_pure_bound_expr base_id Expr.Base state in
    let end_bound = lookup_pure_bound_expr base_id Expr.End state in
    match base_bound, end_bound with
    (* Both found in current - local memory *)
    | (Some base_exp, None), (Some end_exp, None) ->
      ptrplus_with_bounds loc instr base_id base_exp end_exp result_offset state
    (* Both found in current - caller owned memory *)
    | (Some base_exp, Some _), (Some end_exp, Some _) ->
      ptrplus_with_missing_bound loc instr base_id base_exp end_exp result_offset state
    (* Missing base, end *)
    | (None, None), _ ->
      ptrplus_create_missing_base_end loc instr base_id result_expr state
    | _ ->
      Logging.die InternalError "ptrplus_check_bounds: inconsistent state"

  (** Both Base and End found in current — check null, extract offset expressions,
      try concrete comparison, delegate to symbolic handler if either is non-concrete.
      [result_offset] is the byte offset of the arithmetic result relative to base *)
  and ptrplus_with_bounds loc instr base_id base_exp end_exp result_offset state =
    if Formula.is_zero_expr base_exp then
      [{ state with status = Error (err_ptrplus_null, loc, instr) }]
    else
      let base_off_expr = Formula.extract_offset_expr base_exp base_id in
      let end_off_expr = Formula.extract_offset_expr end_exp base_id in
      let base_val = eval_expr_to_int64_opt base_off_expr state in
      let end_val = eval_expr_to_int64_opt end_off_expr state in
      match base_val, end_val with
      | Some base_offset, Some end_offset ->
        if Int64.compare result_offset base_offset < 0 then
          [{ state with status = Error (err_ptrplus_below_base, loc, instr) }]
        else if Int64.compare result_offset end_offset > 0 then
          [{ state with status = Error (err_ptrplus_above_end, loc, instr) }]
        else
          [state]
      | _ ->
        ptrplus_with_bounds_symbolic loc instr base_id base_off_expr end_off_expr
          base_val end_val result_offset state

  (** Handles pointer arithmetic bounds check when End offset is symbolic.
      Base must always be concrete for local memory — dies if not.
      End check uses Astral fallback: error+ok or pass through.
      No BlockPointsTo gap needed — this is pointer arithmetic, not memory access *)
  and ptrplus_with_bounds_symbolic loc instr _base_id _base_off_expr end_off_expr
      base_val end_val result_offset state =
    let result_const = Expr.Const (Int result_offset) in
    let base_states = match base_val with
      | Some base_offset ->
        if Int64.compare result_offset base_offset < 0 then
          [{ state with status = Error (err_ptrplus_below_base, loc, instr) }]
        else
          [state]
      | None ->
        Logging.die InternalError
          "ptrplus_with_bounds_symbolic: local Base offset is symbolic — this should be unreachable"
    in
    concat_map_ok_states (fun state ->
      match end_val with
      | Some end_offset ->
        if Int64.compare result_offset end_offset > 0 then
          [{ state with status = Error (err_ptrplus_above_end, loc, instr) }]
        else
          [state]
      | None ->
        let above_condition = Expr.BinOp (Pless, end_off_expr, result_const) in
        let below_condition = Expr.BinOp (Plesseq, result_const, end_off_expr) in
        let within, not_within =
          match AtlasAstral.check_sat_with_condition state above_condition with
          | `Unsat -> true, false
          | _ ->
            match AtlasAstral.check_sat_with_condition state below_condition with
            | `Unsat -> false, true
            | _ -> false, false
        in
        match within, not_within with
        | true, false -> [state]
        | false, true ->
          [{ state with status = Error (err_ptrplus_above_end, loc, instr) }]
        | _ ->
          let err_state = { state with
            status = Error (err_ptrplus_above_end, loc, instr);
            missing = { state.missing with
              pure = above_condition :: state.missing.pure } }
          in
          let filter pure = Stdlib.List.filter
            (fun e -> match e with
              | Expr.BinOp (Plesseq, _, end_off_expr')
                when Expr.equal end_off_expr end_off_expr'
                  -> false
              | _ -> true)
            pure
          in
          let ok_state = { state with
            current = { state.current with
              pure = below_condition :: filter state.current.pure };
            missing = { state.missing with
              pure = below_condition :: filter state.missing.pure } }
          in
          [err_state; ok_state]
    ) base_states

  (** Formal memory — both Base and End found in missing. Lowers Base and/or
      raises End bound when result offset falls outside, generating error
      contracts for each gap (same pattern as [deref_lower_base_bound] /
      [deref_raise_end_bound] but without spatial predicates — not an access) *)
  and ptrplus_with_missing_bound loc instr base_id base_exp end_exp result_offset state =
    if Formula.is_zero_expr base_exp then
      [{ state with status = Error (err_ptrplus_null, loc, instr) }]
    else
      let states = [state] in
      (* Lower Base bound if result is below current Base *)
      let states = List.concat_map states ~f:(fun s ->
        let base_offset = eval_expr_offset base_exp base_id s in
        if Int64.compare result_offset base_offset < 0 then
          let err_state = { s with status = Error (err_ptrplus_below_base, loc, instr);
            missing = { s.missing with pure =
              Expr.BinOp (Pless, Expr.BinOp (Pplus, Var base_id, Const (Int result_offset)),
                Expr.UnOp (Base, Var base_id)) :: s.missing.pure } }
          in
          let to_remove = Expr.BinOp (Plesseq, UnOp (Base, Var base_id), base_exp) in
          let to_add = Expr.BinOp (Plesseq,
            UnOp (Base, Var base_id),
            BinOp (Pplus, Var base_id, Const (Int result_offset)))
          in
          let filter pure = Stdlib.List.filter (fun e -> not (Expr.equal e to_remove)) pure in
          let ok_state = { s with
            missing = { s.missing with
              pure = to_add :: filter s.missing.pure };
            current = { s.current with
              pure = to_add :: filter s.current.pure } }
          in
          [err_state; ok_state]
        else [s])
      in
      (* Raise End bound if result is above current End *)
      let states = List.concat_map states ~f:(fun s ->
        match s.status with Error _ -> [s] | Ok ->
        let end_offset = eval_expr_offset end_exp base_id s in
        if Int64.compare result_offset end_offset > 0 then
          let err_state = { s with status = Error (err_ptrplus_above_end, loc, instr);
            missing = { s.missing with pure =
              Expr.BinOp (Pless, Expr.UnOp (End, Var base_id),
                Expr.BinOp (Pplus, Var base_id, Const (Int result_offset)))
              :: s.missing.pure } }
          in
          let to_remove = Expr.BinOp (Plesseq, end_exp, UnOp (End, Var base_id)) in
          let to_add = Expr.BinOp (Plesseq,
            BinOp (Pplus, Var base_id, Const (Int result_offset)),
            UnOp (End, Var base_id))
          in
          let filter pure = Stdlib.List.filter (fun e -> not (Expr.equal e to_remove)) pure in
          let ok_state = { s with
            missing = { s.missing with
              pure = to_add :: filter s.missing.pure };
            current = { s.current with
              pure = to_add :: filter s.current.pure } }
          in
          [err_state; ok_state]
        else [s])
      in
      states

  (** Missing Base and End — create error (null) + error (freed) +
      ok (Base!=0 & End!=0 & within bounds) contracts *)
  and ptrplus_create_missing_base_end loc instr base_id result_expr state =
    (* Error: null pointer *)
    let err_null = { state with
      status = Error (err_ptrplus_null, loc, instr);
      missing = { state.missing with pure =
        Expr.BinOp (Peq, Expr.UnOp (Base, Var base_id), Expr.Const (Int 0L))
          :: state.missing.pure } }
    in
    (* Error: use after free *)
    let err_freed = { state with
      status = Error (err_ptrplus_use_after_free, loc, instr);
      missing = { state.missing with pure =
        Expr.UnOp (Freed, Var base_id) :: state.missing.pure } }
    in
    (* Error: below lower bound *)
    let err_below = { state with
      status = Error (err_ptrplus_below_base, loc, instr);
      missing = { state.missing with pure = 
        Expr.BinOp (Pless, result_expr, Expr.UnOp (Base, Var base_id))
        :: state.missing.pure } }
    in
    (* Error: above upper bound *)
    let err_above = { state with 
      status = Error (err_ptrplus_above_end, loc, instr);
      missing = { state.missing with pure = 
        Expr.BinOp (Pless, Expr.UnOp (End, Var base_id), result_expr)
        :: state.missing.pure } }
    in
    (* OK: Base!=0 & End!=0 & within bounds *)
    let ok = { state with
      missing = { state.missing with pure =
        Expr.BinOp (Pneq, Expr.UnOp (Base, Var base_id), Expr.Const (Int 0L))
        :: Expr.BinOp (Pneq, Expr.UnOp (End, Var base_id), Expr.Const (Int 0L))
        :: Expr.BinOp (Plesseq, Expr.UnOp (Base, Var base_id), result_expr)
        :: Expr.BinOp (Plesseq, result_expr, Expr.UnOp (End, Var base_id))
        :: state.missing.pure };
      current = { state.current with pure =
        Expr.BinOp (Pneq, Expr.UnOp (Base, Var base_id), Expr.Const (Int 0L))
        :: Expr.BinOp (Pneq, Expr.UnOp (End, Var base_id), Expr.Const (Int 0L))
        :: Expr.BinOp (Plesseq, Expr.UnOp (Base, Var base_id), result_expr)
        :: Expr.BinOp (Plesseq, result_expr, Expr.UnOp (End, Var base_id))
        :: state.current.pure } }
    in
    [err_null; err_freed; err_below; err_above; ok]


  (* ==================== SIL Metadata ==================== *)

  and exec_metadata_instr metadata state =
    match metadata with
    | Sil.ExitScope (var_list, _loc) ->
      [List.fold var_list ~init:state ~f:exit_scope_var]
    | _ ->
      [state]

  (** Removes a single logical variable from state maps (vars, types, subst).
      Program variables are ignored — only temporaries (introduced by SIL Load
      or function calls) are cleared, as they are scoped to a single CFG node *)
  and exit_scope_var state = function
    | Var.LogicalVar ident ->
      begin match Formula.lookup_variable_id (Var.of_id ident) state.vars with
      | Some id ->
        { state with
          vars = VarIdMap.remove id state.vars;
          types = VarIdMap.remove id state.types;
          subst = VarIdMap.remove id state.subst }
      | None -> state
      end
    | _ -> state

  (** Transfer function for a single disjunct — the interpreter manages the disjunction.
      Error states are passed through unchanged *)
  let exec_instr ~limit:_ (astate, non_disj) (analysis_data : analysis_data) (node : CFG.Node.t) (instr : Sil.instr) =
    let results = match astate.status with
      | Error _ -> [astate]
      | Ok -> exec_instr_single node analysis_data astate instr
    in
    (results, non_disj)

  let exec_instr_non_disj non_disj _analysis_data _node _instr = non_disj

  let remember_dropped_disjuncts _ non_disj = non_disj

  let widen_list _ next ~num_iters:_ = next

  let pp_disjunct _pp_kind = DisjDomain.pp

  let pp_non_disj _pp_kind = NonDisjDomain.pp

end
