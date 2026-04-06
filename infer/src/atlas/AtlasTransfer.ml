
module Formula = AtlasFormula
module Expr = Formula.Expr
module Id = Formula.Id
module VarIdMap = Formula.VarIdMap

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
      exec_load_instr loc instr id tenv typ e rhs_expr state
    | Sil.Store {e1; typ; e2; loc} ->
      Format.print_string (
        "[SIL_STORE]: " ^ sil_instr_to_string instr ^ "\n");
      let lhs_expr = sil_exp_to_expr ~typ:typ e1 tenv state in
      let rhs_expr = sil_exp_to_expr ~typ:typ e2 tenv state in
      exec_store_instr loc instr tenv typ e1 lhs_expr rhs_expr state
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
    | Sil.Prune (exp, _loc, _is_then_branch, _if_kind) ->
      begin
        Format.print_string (
          "[SIL_PRUNE]: " ^ sil_instr_to_string instr ^ "\n");
        let cond = sil_exp_to_expr exp tenv state in
        match eval_prune_condition cond state with
        | Unsat -> []
        | Sat -> [state]
        | Unknown ->
          (* Fast eval could not determine — delegate to Astral solver *)
          match AtlasAstral.eval_prune state cond with
          | Unsat -> []
          | Sat -> [state]
          | Unknown ->
            [{ state with
              missing = { state.missing with pure = cond :: state.missing.pure };
              current = { state.current with pure = cond :: state.current.pure } }]
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
        let rhs_norm = normalize_expr rhs_expr state in
        assign_to_variable lhs_id rhs_norm state
    end

  (** Assigns [rhs] to [lhs_id]: substitution if RHS is a variable, pure equality otherwise.
      Clears stale value constraints and subst entries for [lhs_id] before the assignment.
      Note: when called from load, [lhs_id] is always a fresh temp so the cleanup is a no-op,
      but the call is kept for correctness when called from store paths *)
  and assign_to_variable lhs_id rhs state =
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
      let exp = Expr.BinOp (Peq, Expr.Var lhs_id, normalize_expr rhs state) in
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
      let base_offset = eval_expr_offset e var_id state in
      if Int64.compare offset base_offset < 0 then
        [{ state with status = Error (err_deref_below_lower_bound, loc, instr) }]
      else
        [state]
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
      let end_offset = eval_expr_offset e var_id state in
      let access_end = Stdlib.Int64.add offset cell_size in
      if Int64.compare access_end end_offset > 0 then
        [{ state with status = Error (err_deref_above_upper_bound, loc, instr) }]
      else
        [state]
    | (None, None) ->
      deref_create_missing_end loc instr var_id offset cell_size state

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
      let block_src = Expr.BinOp (Pplus, Var var_id, Const (Int offset)) in
      let block_pto = Formula.BlockPointsTo (block_src, Expr.Const (Int cell_size)) in
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
      let block_src = Expr.BinOp (Pplus, Var var_id, Const (Int offset)) in
      let block_pto = Formula.BlockPointsTo (block_src, Expr.Const (Int cell_size)) in
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
    else if is_sil_address_assign lhs && is_pointer_type lhs_typ then
      store_address_assign loc instr lhs lhs_expr rhs_expr state
    else
      store_value_assign lhs lhs_expr rhs_expr state

  (** Store address assignment: LHS is a program variable being assigned a pointer value.
      Handles three RHS cases: heap address (temp rename or alias), null, or error *)
  and store_address_assign loc instr lhs _lhs_expr rhs_expr state =
    match direct_id_of_sil_lvar lhs state with
    | Some lhs_direct_id ->
      let rhs_norm = normalize_expr rhs_expr state in
      begin match base_and_offset_of_expr rhs_norm state with
      | Some (rhs_base_id, rhs_offset) ->
        let rhs_canonical = canonical_expr state.subst rhs_base_id rhs_offset in
        let rhs_canon_base = match rhs_canonical with
          | Var id -> id | Ptr { base; _ } -> base
        in
        let is_temp = match VarIdMap.find_opt rhs_canon_base state.vars with
          | Some var -> not (Var.is_pvar var)
          | None -> false
        in
        let state = clear_before_subst lhs_direct_id state in
        if is_temp then
          (* RHS is a temp variable (e.g. malloc retval) — rename it in the formula
             so that the temp's formula entries become owned by the LHS variable *)
          let rhs_norm = normalize_expr (subst_expr_to_formula_expr rhs_canonical) state in
          let lhs_norm = Expr.Var lhs_direct_id in
          [subst_apply ~from_:rhs_norm ~to_:lhs_norm state]
        else
          (* RHS is a program variable or internal id — record the alias in subst
             without modifying the formula, preserving the RHS variable's identity *)
          [{ state with subst = VarIdMap.add lhs_direct_id rhs_canonical state.subst }]
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

  (** Store value assignment: LHS is a program variable being assigned a non-pointer value.
      Uses [assign_to_variable] when LHS resolves to a direct id, falls back to pure equality *)
  and store_value_assign lhs lhs_expr rhs_expr state =
    match direct_id_of_sil_lvar lhs state with
    | Some lhs_direct_id ->
      let rhs_norm = normalize_expr rhs_expr state in
      assign_to_variable lhs_direct_id rhs_norm state
    | None ->
      let rhs_norm = normalize_expr rhs_expr state in
      let lhs_norm = normalize_expr lhs_expr state in
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
    let rhs_norm = normalize_expr rhs_expr state in
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
      dispatching [ExpExactMatch] stale constraint cleanup *)
  and store_extract_split_args block_split_res state =
    match block_split_res with
    | ExpExactMatch { block_split_args; old_dest } ->
      let state, rewrite_spatial = match old_dest with
        | Expr.Var id -> clear_stale_value_constraints id state
        | _ -> (state, Fun.id)
      in
      (state, block_split_args, rewrite_spatial)
    | BlockExactMatch args | BlockEdgeMatch args | BlockMiddleMatch args ->
      (state, args, Fun.id)

  (** Handles a block split for a local allocation (found in current only).
      Transforms current spatial, runs assignment, prepends new [ExpPointsTo] to current *)
  and store_split_local lhs_typ rhs_norm block_split_res curr_hps curr_rest state =
    let state, { to_remove; to_add; new_exp_points_to; new_dest_id }, rewrite_spatial =
      store_extract_split_args block_split_res state
    in
    let curr_spatial = transform_spatial to_remove curr_hps to_add curr_rest in
    let state = { state with current = { state.current with spatial = curr_spatial } } in
    let lhs_expr = Expr.Var new_dest_id in
    let assign_res = store_dereference_assign state lhs_typ new_dest_id lhs_expr rhs_norm in
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
      let state, { to_remove; to_add; new_exp_points_to; new_dest_id }, _rewrite_spatial =
        store_extract_split_args block_split_res state
      in
      let curr_spatial = transform_spatial to_remove curr_hps to_add curr_rest in
      let miss_spatial = transform_spatial to_remove miss_hps to_add miss_rest in
      let state = { state with
        current = { state.current with spatial = curr_spatial };
        missing = { state.missing with spatial = miss_spatial } }
      in
      let lhs_expr = Expr.Var new_dest_id in
      let assign_res = store_dereference_assign state lhs_typ new_dest_id lhs_expr rhs_norm in
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
    let assign_res = store_dereference_assign state lhs_typ cell_id lhs_expr rhs_norm in
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
    let size = normalize_expr actual state in
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

  (** Recovers element size from type info, scales offset to bytes,
      then checks for double-free before proceeding to base lookup *)
  and free_compute_offset loc instr tenv base_id offset state =
    (* Recover the original type from the preceding Load instruction's type info.
       SIL always passes void* to free, but the variable retains its original type *)
    let element_size =
      match VarIdMap.find_opt base_id state.types with
      | Some typ ->
        begin match typ_size_of_element_opt tenv typ with
        | Some 0L -> 1L (* void pointer — no size info *)
        | Some size -> size
        | None -> 1L
        end
      | None -> 1L
    in
    (* offset from base_and_offset_of_expr is in element units, scale to bytes *)
    let offset_bytes = Stdlib.Int64.mul offset element_size in
    [state]
    |> concat_map_ok_states (deref_check_freed loc instr base_id)
    |> concat_map_ok_states (free_lookup_base loc instr base_id offset_bytes element_size)

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
