
module Formula = AtlasFormula
module Expr = Formula.Expr
module State = AtlasState
module Id = Formula.Id

open !Formula
open !State

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
    let open IntraproceduralAnalysis in
    let open State in
    let tenv = analysis_data.tenv in
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
        match State.eval_prune_condition cond state with
        | State.Unsat -> []
        | State.Sat -> [state]
        | State.Unknown ->
          (* condition depends on external input — record as precondition
             and mirror to current (the branch was taken, so it holds as postcondition too) *)
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
          ~f:(fun state -> State.to_string state)
          states));

    states

  and exec_load_instr loc instr lhs tenv typ rhs rhs_expr state =
    let open State in
    let lhs_id = Id.fresh () in
    let state = { state with
      vars = VarIdMap.add lhs_id (Var.of_id lhs) state.vars;
      types = VarIdMap.add lhs_id typ state.types }
    in
    if is_sil_dereference rhs then
      match base_and_offset_of_expr rhs_expr state with
      | Some (rhs_id, off) ->
          exec_load_deref_ loc instr tenv typ lhs_id rhs_id off state
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

  (** If [rhs] is (Var id) then adds substitution, otherwise adds pure constraint (Var ([lhs_id]) == [rhs]) to [state].
      Clears stale value constraints and subst entries for [lhs_id] before the assignment *)
  and assign_to_variable lhs_id rhs state =
    let open Expr in
    let open State in
    let state, rewrite_spatial = State.clear_stale_value_constraints lhs_id state in
    let state = { state with current = { state.current with
      spatial = rewrite_spatial state.current.spatial } } in
    match rhs with
    | Expr.Var rhs_id ->
      (* Both Ids already canonical *)
      if Id.equal lhs_id rhs_id then
        [state]
      else
        [{ state with subst = VarIdMap.add lhs_id (Var rhs_id) state.subst }]
    | _ ->
      let exp = Expr.BinOp (Peq, Var lhs_id, normalize_expr rhs state) in
      let current =
        { state.current with pure = exp :: state.current.pure }
      in
      [{ state with current }]
  
  and exec_load_deref_ loc instr tenv rhs_typ lhs_id rhs_var_id rhs_offset state =
    (* TODO rethink - can it be something else than 8L (pointer) ? *)
    let cell_size = typ_size_of tenv rhs_typ in
    [state]
    |> concat_map_ok_states
      (dereference_check_freed loc instr rhs_var_id)
    |> concat_map_ok_states
      (exec_deref_check_base loc instr rhs_var_id rhs_offset)
    |> concat_map_ok_states
      (exec_deref_check_end loc instr rhs_var_id rhs_offset cell_size)
    |> concat_map_ok_states
      (load_dereference_try_match_heap_predicates loc instr lhs_id rhs_typ rhs_var_id rhs_offset cell_size)

  and load_dereference_try_match_heap_predicates loc instr lhs_id rhs_typ rhs_var_id rhs_offset cell_size state =
    let curr_hps, curr_rest, miss_hps, miss_rest =
      State.heap_find_block_fragments state rhs_var_id rhs_offset cell_size
    in
    let try_match hps =
      State.heap_try_match hps rhs_var_id rhs_offset cell_size
    in
    let transfor_spatial to_remove from to_add rest =
      let removed = Stdlib.List.filter
        (fun hp -> not (heap_pred_equal hp to_remove))
        from
      in
      List.append removed (List.append to_add rest)
    in
    let handle_match_result match_res hps rest ~is_missing state =
      match match_res with
      | MatchExpExact { matched = _; dest = Expr.Var id_of_dest } ->
        let subst = VarIdMap.add lhs_id (Var id_of_dest) state.subst in
        [{ state with subst }]
      | MatchExpExact { matched = _; dest } ->
        let exp = Expr.BinOp (Peq, Var lhs_id, dest) in
        let current = { state.current with pure = exp :: state.current.pure } in
        [{ state with current }]
      | MatchBlockSplit block_split_res ->
        let { to_remove; to_add; new_dest_id } = match block_split_res with
          | ExpExactMatch { block_split_args; old_dest = _ } -> block_split_args
          | BlockExactMatch args
          | BlockEdgeMatch args
          | BlockMiddleMatch args -> args
        in
        let spatial = transfor_spatial to_remove hps to_add rest in
        let state =
          if is_missing then
            { state with missing = { state.missing with spatial } }
          else
            { state with current = { state.current with spatial } }
        in
        let subst = VarIdMap.add lhs_id (Var new_dest_id) state.subst in
        let types = VarIdMap.add new_dest_id rhs_typ state.types in
        [{ state with subst; types }]
    in
    match try_match curr_hps with
    | Some match_res ->
      handle_match_result match_res curr_hps curr_rest ~is_missing:false state
    | None ->
      begin match try_match miss_hps with
      | Some match_res ->
        handle_match_result match_res miss_hps miss_rest ~is_missing:true state
      | None ->
        (* missing resource *)
        let err_state = { state with status = Error (err_load_deref_missing_cell, loc, instr) } in
        let cell_id = Id.fresh () in
        let missing_spatial = ExpPointsTo (
          Expr.BinOp (Pplus, Var rhs_var_id, Const (Int rhs_offset)),
          Expr.Const (Int cell_size),
          Expr.Var cell_id)
        in
        let state = { state with
          missing = { state.missing with spatial = missing_spatial :: state.missing.spatial };
          (* mirror to current — subsequent accesses will find and modify the current copy *)
          current = { state.current with spatial = missing_spatial :: state.current.spatial } } in
        let subst = VarIdMap.add lhs_id (Var cell_id) state.subst in
        let types = VarIdMap.add cell_id rhs_typ state.types in
        [err_state; { state with subst; types }]
      end

  and exec_store_instr loc instr tenv lhs_typ lhs lhs_expr rhs_expr state =
    let open State in
    if is_sil_dereference lhs then
      match base_and_offset_of_expr lhs_expr state with
      | Some (lhs_id, off) ->
          exec_store_deref loc instr tenv lhs_typ lhs_id off rhs_expr state
      | None ->
        [{ state with status = Error (err_store_deref_no_base, loc, instr) }]
    else begin
      if is_sil_address_assign lhs && is_pointer_type lhs_typ then begin
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
              [(subst_apply ~from_:rhs_norm ~to_:lhs_norm state)]
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
      end else
        match direct_id_of_sil_lvar lhs state with
        | Some lhs_direct_id ->
          let rhs_norm = normalize_expr rhs_expr state in
          assign_to_variable lhs_direct_id rhs_norm state
        | None ->
          let rhs_norm = normalize_expr rhs_expr state in
          let lhs_norm = normalize_expr lhs_expr state in
          let state = match lhs_norm with
            | Expr.Var id ->
              let state, rewrite_spatial = State.clear_stale_value_constraints id state in
              { state with current = { state.current with
                spatial = rewrite_spatial state.current.spatial } }
            | _ -> state
          in
          let exp = Expr.BinOp (Peq, lhs_norm, rhs_norm) in
          let current =
            { state.current with pure = exp :: state.current.pure }
          in [{ state with current }]
    end

  and exec_store_deref loc instr tenv lhs_typ lhs_var_id lhs_offset rhs_expr state =
    let cell_size = typ_size_of tenv lhs_typ in
    [state]
    |> concat_map_ok_states
      (dereference_check_freed loc instr lhs_var_id)
    |> concat_map_ok_states
      (exec_deref_check_base loc instr lhs_var_id lhs_offset)
    |> concat_map_ok_states
      (exec_deref_check_end loc instr lhs_var_id lhs_offset cell_size)
    |> concat_map_ok_states
      (store_dereference_try_match_heap_predicates loc instr lhs_typ lhs_var_id lhs_offset cell_size rhs_expr)
  
  and concat_map_ok_states f states = 
    let open State in
    List.concat_map ~f:(fun s ->
      match s.status with
      | Ok -> f s
      | Error _ -> [s])
    states

  and dereference_check_freed loc instr var_id state =
    if State.is_freed_expr var_id state then
      [{ state with status = Error (err_deref_use_after_free, loc, instr)}]
    else [state]

  and exec_deref_check_base loc instr var_id offset state =
    match State.lookup_pure_bound_expr var_id Expr.Base state with
    (* Zero base in either → unallocated pointer *)
    | (Some e, _) when Formula.is_zero_expr e ->
      [{ state with status = Error (err_deref_null_base, loc, instr) }]
    | (_, Some e) when Formula.is_zero_expr e ->
      [{ state with status = Error (err_deref_null_base, loc, instr) }]
    (* Found in missing → precondition inequality, can lower if needed *)
    | (_, Some e) ->
      dereference_lower_base_bound e var_id offset state
    (* Found only in current → allocation equality, strict check *)
    | (Some e, None) ->
      let base_offset = eval_expr_offset e var_id state in
      if Int64.compare offset base_offset < 0 then
        [{ state with status = Error (err_deref_below_lower_bound, loc, instr) }]
      else
        [state]
    (* Not found → create missing Base and mirror to current *)
    | (None, None) ->
      let err_state = { state with status = Error (err_deref_missing_base, loc, instr) } in
      let bound = Expr.BinOp (Plesseq,
        Expr.UnOp (Base, Var var_id),
        Expr.BinOp (Pplus, Var var_id, Const (Int offset)))
      in
      let ok_state = { state with
        missing = { state.missing with pure = bound :: state.missing.pure };
        current = { state.current with pure = bound :: state.current.pure } }
      in
      [ err_state; ok_state ]

  (** Lowers the Base bound in both missing and current when access offset is below it *)
  and dereference_lower_base_bound base_exp var_id offset state =
    let base_offset = eval_expr_offset base_exp var_id state in
    if Int64.compare offset base_offset < 0 then
      let to_remove = Expr.BinOp (Plesseq, UnOp (Base, Var var_id), base_exp) in
      let to_add = Expr.BinOp (Plesseq,
        UnOp (Base, Var var_id),
        BinOp (Pplus, Var var_id, Const (Int offset)))
      in
      let filter pure = Stdlib.List.filter (fun e -> not (Expr.equal e to_remove)) pure in
      [{ state with
        missing = { state.missing with pure = to_add :: filter state.missing.pure };
        current = { state.current with pure = to_add :: filter state.current.pure } }]
    else
      [state]

  and exec_deref_check_end loc instr var_id offset cell_size state =
    match State.lookup_pure_bound_expr var_id Expr.End state with
    (* Zero end in either → unallocated pointer *)
    | (Some e, _) when Formula.is_zero_expr e ->
      [{ state with status = Error (err_deref_null_end, loc, instr) }]
    | (_, Some e) when Formula.is_zero_expr e ->
      [{ state with status = Error (err_deref_null_end, loc, instr) }]
    (* Found in missing → precondition inequality, can increase if needed *)
    | (_, Some e) ->
      dereference_raise_end_bound e var_id offset cell_size state
    (* Found only in current → allocation equality, strict check *)
    | (Some e, None) ->
      let end_offset = eval_expr_offset e var_id state in
      let access_end = Stdlib.Int64.add offset cell_size in
      if Int64.compare access_end end_offset > 0 then
        [{ state with status = Error (err_deref_above_upper_bound, loc, instr) }]
      else
        [state]
    (* Not found → create missing End and mirror to current *)
    | (None, None) ->
      let err_state = { state with status = Error (err_deref_missing_end, loc, instr) } in
      let bound = Expr.BinOp (Plesseq,
        Expr.BinOp (Pplus, Var var_id, Const (Int (Stdlib.Int64.add offset cell_size))),
        Expr.UnOp (End, Var var_id))
      in
      let ok_state = { state with
        missing = { state.missing with pure = bound :: state.missing.pure };
        current = { state.current with pure = bound :: state.current.pure } }
      in
      [ err_state; ok_state ]

  (** Raises the End bound in both missing and current when access exceeds it *)
  and dereference_raise_end_bound end_exp var_id offset cell_size state =
    let end_offset = eval_expr_offset end_exp var_id state in
    let access_end = Stdlib.Int64.add offset cell_size in
    if Int64.compare access_end end_offset > 0 then
      let to_remove = Expr.BinOp (Plesseq, end_exp, UnOp (End, Var var_id)) in
      let to_add = Expr.BinOp (Plesseq,
        BinOp (Pplus, Var var_id, Const (Int access_end)),
        UnOp (End, Var var_id))
      in
      let filter pure = Stdlib.List.filter (fun e -> not (Expr.equal e to_remove)) pure in
      [{ state with
        missing = { state.missing with pure = to_add :: filter state.missing.pure };
        current = { state.current with pure = to_add :: filter state.current.pure } }]
    else
      [state]

  and store_dereference_try_match_heap_predicates loc instr lhs_typ lhs_var_id lhs_offset cell_size rhs_expr state =
    let rhs_norm = normalize_expr rhs_expr state in
    let try_block_split hps =
      State.heap_try_block_split hps lhs_var_id lhs_offset cell_size
    in
    let assign state lhs_id lhs_expr =
      store_dereference_assign state lhs_typ lhs_id lhs_expr rhs_norm
    in
    let transfor_spatial to_remove from to_add rest =
      let removed = Stdlib.List.filter
          (fun hp -> not (heap_pred_equal hp to_remove))
          from
        in
        List.append removed (List.append to_add rest)
    in
    let curr_hps, curr_rest, miss_hps, miss_rest =
      State.heap_find_block_fragments state lhs_var_id lhs_offset cell_size
    in
    (** Applies block split result: removes the matched predicate, adds split fragments,
        runs [store_dereference_assign], then fixes up the separated [new_exp_points_to]
        using [canonical_rhs] from [AddressStored] if a pointer was stored.
        [rewrite_spatial] is a callback from [clear_stale_value_constraints] that rewrites
        stale references in [current.spatial] — applied after spatial transform but before
        prepending the new [ExpPointsTo] *)
    let handle_block_split_res ?(to_missing=false) ?(rewrite_spatial=Fun.id) state to_remove to_add part rest new_dest_id (new_exp_points_to: heap_pred) =
      let spatial = transfor_spatial to_remove part to_add rest in
      let state =
        if to_missing then
          { state with missing = { state.missing with spatial } }
        else
          { state with current = { state.current with spatial } }
      in
      let lhs_expr = Expr.Var new_dest_id in
      let assign_res = assign state new_dest_id lhs_expr in
      let state, new_exp_points_to = match assign_res with
        | ValueStored state | AliasStored state ->
          (* no formula-wide substitution — separated predicate needs no fixup *)
          (state, new_exp_points_to)
        | AddressStored { state; canonical_rhs } ->
          (* address was stored via subst_apply — fix up the separated ExpPointsTo
             using the canonical RHS that subst_apply actually substituted *)
          let src, size = match new_exp_points_to with
            | ExpPointsTo (src, size, _) -> (src, size)
            | _ -> Logging.die InternalError
                     "handle_block_split_res: expected ExpPointsTo for new cell"
          in
          (state, ExpPointsTo (
            Formula.expr_replace ~old_:canonical_rhs ~new_:lhs_expr src,
            Formula.expr_replace ~old_:canonical_rhs ~new_:lhs_expr size,
            Expr.Var new_dest_id))
      in
      (* Apply stale-constraint spatial rewrite after block split transform + assign,
         but before prepending new ExpPointsTo *)
      let state = { state with current = { state.current with
        spatial = rewrite_spatial state.current.spatial } } in
      if to_missing then
        (* mirror new ExpPointsTo to current — subsequent accesses find the current copy *)
        [ { state with
          missing = { state.missing with spatial = new_exp_points_to :: state.missing.spatial };
          current = { state.current with spatial = new_exp_points_to :: state.current.spatial } } ]
      else
        [ { state with current = { state.current with
          spatial = new_exp_points_to :: state.current.spatial } } ]
    in
    match try_block_split curr_hps with
    | Some block_split_res ->
      begin match block_split_res with
      | ExpExactMatch { block_split_args = { to_remove; to_add; new_exp_points_to; new_dest_id }; old_dest } ->
        (* Clear stale value constraints for the old destination being overwritten *)
        let state, rewrite_spatial = match old_dest with
          | Expr.Var id -> State.clear_stale_value_constraints id state
          | _ -> (state, Fun.id)
        in
        handle_block_split_res ~rewrite_spatial state to_remove to_add curr_hps curr_rest new_dest_id new_exp_points_to
      | BlockExactMatch { to_remove; to_add; new_exp_points_to; new_dest_id }
      | BlockEdgeMatch { to_remove; to_add; new_exp_points_to; new_dest_id }
      | BlockMiddleMatch { to_remove; to_add; new_exp_points_to; new_dest_id } ->
        handle_block_split_res state to_remove to_add curr_hps curr_rest new_dest_id new_exp_points_to
      end
    | None ->
      begin match try_block_split miss_hps with
      | Some block_split_res ->
        begin match block_split_res with
        | ExpExactMatch { block_split_args = { to_remove; to_add; new_exp_points_to; new_dest_id }; old_dest } ->
          let state, rewrite_spatial = match old_dest with
            | Expr.Var id -> State.clear_stale_value_constraints id state
            | _ -> (state, Fun.id)
          in
          handle_block_split_res ~to_missing:true ~rewrite_spatial state to_remove to_add miss_hps miss_rest new_dest_id new_exp_points_to
        | BlockExactMatch { to_remove; to_add; new_exp_points_to; new_dest_id }
        | BlockEdgeMatch { to_remove; to_add; new_exp_points_to; new_dest_id }
        | BlockMiddleMatch { to_remove; to_add; new_exp_points_to; new_dest_id } ->
          handle_block_split_res ~to_missing:true state to_remove to_add miss_hps miss_rest new_dest_id new_exp_points_to
      end
      | None ->
        let err_state = { state with status = Error (err_store_deref_missing_cell, loc, instr) } in
        let cell_id = Id.fresh () in
        let lhs_expr = Expr.Var cell_id in
        let missing_spatial = ExpPointsTo (
          Expr.BinOp (Pplus, Var lhs_var_id, Const (Int lhs_offset)),
          Expr.Const (Int cell_size),
          lhs_expr)
        in
        let assign_res = assign state cell_id lhs_expr in
        let state, missing_spatial = match assign_res with
          | ValueStored state | AliasStored state ->
            (state, missing_spatial)
          | AddressStored { state; canonical_rhs } ->
            (* self-referential fix: update source/size of the separated ExpPointsTo *)
            let src, size = match missing_spatial with
              | ExpPointsTo (src, size, _) -> (src, size)
              | _ -> Logging.die InternalError
                       "missing resource: expected ExpPointsTo"
            in
            (state, ExpPointsTo (
              Formula.expr_replace ~old_:canonical_rhs ~new_:lhs_expr src,
              Formula.expr_replace ~old_:canonical_rhs ~new_:lhs_expr size,
              lhs_expr))
        in
        let ok_state = { state with
          missing = { state.missing with spatial = missing_spatial :: state.missing.spatial };
          (* mirror to current — subsequent accesses will find and modify the current copy *)
          current = { state.current with spatial = missing_spatial :: state.current.spatial } } in
        [ err_state; ok_state ]
      end

  and exec_malloc_instr lhs typ actual state =
    let open State in
    let open Formula in
    let open Expr in
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
      Some i -> Const (Int i)
    | None -> size
    in
    let { current } = state in
    (* success state: block allocated with Base/End constraints *)
    let ok_state = {
      state with
      current = {
        spatial = BlockPointsTo (source, size) :: current.spatial;
        pure =
          BinOp (Peq, UnOp (Base, source), source) ::
          BinOp (Peq, UnOp (End, source), BinOp (Pplus, source, size)) ::
          current.pure
      };
    } in
    (* failure state: malloc returned NULL *)
    let null_state = {
      state with
      current = {
        current with pure =
          BinOp (Peq, source, Expr.null) ::
          BinOp (Peq, UnOp (Base, source), Expr.zero) ::
          BinOp (Peq, UnOp (End, source), Expr.zero) ::
          current.pure
      };
    } in
    [ ok_state; null_state ]

  (** free(NULL) is a no-op per the C standard. Recovers base pointer and offset,
      checks for null (both literal and resolved), then delegates to freed/base checks.
      Null pointer with non-zero offset is UB — terminal error *)
  and exec_free_instr loc instr tenv actual_expr state =
    let open State in
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
          (* free(NULL) — no-op *)
          [state]
        else if is_null then
          (* free(NULL + offset) — UB: null pointer arithmetic *)
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
    |> concat_map_ok_states (free_check_freed loc instr base_id)
    |> concat_map_ok_states (free_lookup_base loc instr base_id offset_bytes element_size)

  (** Checks whether the pointer has already been freed — terminal error if so *)
  and free_check_freed loc instr id state =
    if State.is_freed_expr id state then
      [{ state with status = Error (err_free_double_free, loc, instr) }]
    else
      [state]

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
      let state = State.cleanup_after_free id state in
      let pure = Expr.UnOp (Freed, Var id) :: state.current.pure in
      [{ state with current = { state.current with pure } }]
    else if Int64.compare offset base_offset < 0 then
      (* offset below current base — check missing for lowering *)
      begin match Formula.lookup_pure_base_expr id state.missing.pure with
      | Some miss_base_exp ->
        (* Found in missing — lower bound in precondition only, then free.
           TODO: generate error contract for the lowering case (caller might not
           satisfy the lowered precondition — needs NonBasePointerFree error state) *)
        let to_remove = Expr.BinOp (Plesseq, UnOp (Base, Var id), miss_base_exp) in
        let to_add = Expr.BinOp (Plesseq,
          UnOp (Base, Var id),
          BinOp (Pplus, Var id, Const (Int offset))) in
        let missing_pure = Stdlib.List.filter
          (fun e -> not (Expr.equal e to_remove)) state.missing.pure in
        let state = { state with missing =
          { state.missing with pure = to_add :: missing_pure } }
        in
        let state = State.cleanup_after_free id state in
        let pure = Expr.UnOp (Freed, Var id) :: state.current.pure in
        [{ state with current = { state.current with pure } }]
      | None ->
        [{ state with status = Error (err_free_non_base_offset, loc, instr) }]
      end
    else
      (* offset above base — by definition a non-base-pointer free *)
      [{ state with status = Error (err_free_non_base_offset, loc, instr) }]

  (** Base not found in current — creates missing resources (Base, End, BlockPointsTo)
      in missing only (NOT mirrored to current — Base/End + Freed is contradictory).
      Returns both an error contract and an ok contract with the missing resources *)
  and free_create_missing_contract loc instr id offset cell_size state =
    let err_state = { state with status = Error (err_free_missing_base, loc, instr) } in
    let missing_base = Expr.BinOp (Plesseq,
      UnOp (Base, Var id),
      BinOp (Pplus, Var id, Const (Int offset))) in
    let missing_end = Expr.BinOp (Plesseq,
      BinOp (Pplus, Var id, Const (Int (Stdlib.Int64.add offset cell_size))),
      UnOp (End, Var id)) in
    let missing_heap_pred = BlockPointsTo (
      Expr.Var id,
      Expr.Const (Int cell_size)) in
    let missing = {
      spatial = missing_heap_pred :: state.missing.spatial;
      pure = missing_base :: missing_end :: state.missing.pure } in
    let pure = Expr.UnOp (Freed, Var id) :: state.current.pure in
    let ok_state = { state with
      current = { state.current with pure };
      missing } in
    [err_state; ok_state]

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
      begin match lookup_variable_id (Var.of_id ident) state.vars with
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
    let results = match astate.State.status with
      | State.Error _ -> [astate]
      | State.Ok -> exec_instr_single node analysis_data astate instr
    in
    (results, non_disj)

  let exec_instr_non_disj non_disj _analysis_data _node _instr = non_disj

  let remember_dropped_disjuncts _ non_disj = non_disj

  let widen_list _ next ~num_iters:_ = next

  let pp_disjunct _pp_kind = DisjDomain.pp

  let pp_non_disj _pp_kind = NonDisjDomain.pp

end
