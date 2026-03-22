
type reporter = 
  { proc_desc : Procdesc.t 
  ; err_log : Errlog.t
  ; checker : Checker.t }

let reporter_of_analysis (analysis_data : IntraproceduralAnalysis.t ) = 
  { proc_desc = analysis_data.proc_desc
  ; err_log = analysis_data.err_log
  ; checker = Checker.Atlas }
  
let report
  (r : reporter)
  (loc : Location.t)
  (issue : IssueType.t)
  (msg : string) =
    Reporting.log_issue
      r.proc_desc
      r.err_log
      ~loc:loc
      r.checker
      issue
      msg


let double_free (r : reporter) (loc : Location.t) =
  report r loc IssueType.atlas_double_free
    (Format.asprintf
      "free called on already freed block")

let free_non_base_pointer (r : reporter) (loc : Location.t) =
  report r loc IssueType.atlas_free_non_base_pointer
    (Format.asprintf
      "free called with non-base pointer")

let use_after_free (r: reporter) (loc: Location.t) =
  report r loc IssueType.atlas_use_after_free
    (Format.asprintf
      "usage of variable storing a value pointing to freed block")

(*
let free_invalid_addr (r: reporter) (loc: Location.t) =
  report r loc IssueType.atlas_free_invalid_addr
    (Format.asprintf
      "free called with invalid address")
      *)


module Formula = AtlasFormula
module Expr = Formula.Expr
module State = AtlasState
module Id = Formula.Id

open !Formula
open !State

module TransferFunctions2 = struct
  module CFG = ProcCfg.Normal

  type instr = Sil.instr

  let rec exec_instr _node analysis_data state instr =
    Format.fprintf Format.err_formatter "@[<h>%a;@]@;" (Sil.pp_instr ~print_types:true Pp.text) instr;
    Format.print_newline ();

    let open IntraproceduralAnalysis in
    let open State in
    let tenv = analysis_data.tenv in
    let _r = reporter_of_analysis analysis_data in
    let states = match instr with
    | Sil.Load { id; e; typ; loc } ->
      let rhs_expr = sil_exp_to_expr ~typ:typ e tenv state in

      Format.print_string (
        "[SIL_LOAD]\n[SIL_INSTR_RHS]: " ^ sil_exp_to_string e ^ "\n[RHS_EXPR]: " ^ Expr.to_string state.vars rhs_expr ^ "\n");

      exec_load_instr loc instr id tenv typ e rhs_expr state
    | Sil.Store {e1; typ; e2; loc} ->

      Format.print_string (
        "[SIL_STORE]\n[SIL_INSTR_LHS]: " ^ sil_exp_to_string e1 ^ "\n[SIL_INSTR_RHS]: " ^ sil_exp_to_string e2) ;

      let lhs_expr = sil_exp_to_expr ~typ:typ e1 tenv state in
      let rhs_expr = sil_exp_to_expr e2 tenv state in

      Format.print_string (
        "\n[LHS_EXPR]: " ^ Expr.to_string state.vars lhs_expr ^ "\n[RHS_EXPR]: " ^ Expr.to_string state.vars rhs_expr ^ "\n");

      exec_store_instr loc instr tenv typ e1 lhs_expr rhs_expr state
    | Sil.Call
      ( (ident, typ), Exp.Const (Const.Cfun procname), (actual, actual_typ) :: _, _loc, _ )
        when BuiltinDecl.(match_builtin malloc procname (Procname.to_string procname)) ->
          let actual_expr = sil_exp_to_expr ~typ:actual_typ actual tenv state in

          Format.print_string (
            "[SIL_MALLOC]\n[SIL_ACTUAL]: " ^ sil_exp_to_string actual ^ "\n[ACTUAL_EXPR]: " ^ Expr.to_string state.vars actual_expr ^ "\n");

          exec_malloc_instr ident typ actual_expr state
    | Sil.Call
      ( _, Exp.Const (Const.Cfun procname), (actual, _) :: _, loc, _ )
        when BuiltinDecl.(match_builtin free procname (Procname.to_string procname)) ->
          let actual_expr = sil_exp_to_expr actual tenv state in

          Format.print_string (
            "[SIL_FREE]\n[SIL_ACTUAL]: " ^ sil_exp_to_string actual ^ "\n[ACTUAL_EXPR]: " ^ Expr.to_string state.vars actual_expr ^ "\n");

          exec_free_instr loc instr actual actual_expr state
    | Sil.Prune (_exp, _loc, _is_then_branch, _if_kind) ->
      [state] (* TODO - for starters, kill unsat states, in other words implement eval_cond *)
    | Sil.Metadata metadata ->
      exec_metadata_instr metadata state
    | Sil.Call _ ->
      [state]
    in

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
        Logging.die InternalError
          "[Error] method is_sil_dereference returned true but no base pointer variable found"
    else begin
      if is_sil_address_assign rhs && is_pointer_type typ then
        match base_and_offset_of_expr rhs_expr state with
        | Some (rhs_id, off) ->
          let rhs_canonical = canonical_expr state.subst rhs_id off in
          [{ state with
            subst = VarIdMap.add lhs_id rhs_canonical state.subst }]
        | None ->
          Logging.die InternalError
          "[Error] method is_sil_address_assign returned true but no base pointer variable found"
      else
        let rhs_norm = normalize_expr rhs_expr state in
        assign_to_variable lhs_id rhs_norm state
    end

  (** If [rhs] is (Var id) then adds substitution, otherwise adds pure constaitn (Var ([lhs_id]) == [rhs]) to [state] *)
  and assign_to_variable lhs_id rhs state =
    let open Expr in
    let open State in
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
      (load_dereference_try_match_heap_predicates loc instr lhs_id rhs_var_id rhs_offset cell_size)

  and load_dereference_try_match_heap_predicates loc instr lhs_id rhs_var_id rhs_offset cell_size state =
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
        [{ state with subst }]
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
        let err_state = { state with status = Error (None, loc, instr) } in
        let cell_id = Id.fresh () in
        let missing_spatial = ExpPointsTo (
          Expr.BinOp (Pplus, Var rhs_var_id, Const (Int rhs_offset)),
          Expr.Const (Int cell_size),
          Expr.Var cell_id)
        in
        let spatial = missing_spatial :: state.missing.spatial in
        let state = { state with missing = { state.missing with spatial } } in
        let subst = VarIdMap.add lhs_id (Var cell_id) state.subst in
        [err_state; { state with subst }]
      end

  and exec_store_instr loc instr tenv lhs_typ lhs lhs_expr rhs_expr state =
    let open State in
    if is_sil_dereference lhs then
      match base_and_offset_of_expr lhs_expr state with
      | Some (lhs_id, off) ->
          exec_store_deref loc instr tenv lhs_typ lhs_id off rhs_expr state
      | None ->
        Logging.die InternalError
          "[Error] method is_sil_dereference returned true but no base pointer variable found"
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
          | None ->
            Logging.die InternalError
              "[Error] address assign: failed to extract base pointer from RHS"
          end
        | None ->
          Logging.die InternalError
            "[Error] address assign: failed to extract direct variable id from LHS Lvar"
      end else
        match direct_id_of_sil_lvar lhs state with
        | Some lhs_direct_id ->
          let rhs_norm = normalize_expr rhs_expr state in
          assign_to_variable lhs_direct_id rhs_norm state
        | None ->
          let rhs_norm = normalize_expr rhs_expr state in
          let lhs_norm = normalize_expr lhs_expr state in
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
    if State.is_freed_expr var_id state then begin
      Format.print_string "[Error]: exec_store failed with: memory block is freed\n";
      [{ state with status = Error (None, loc, instr)}]
      end
    else [state]

  and exec_deref_check_base loc instr var_id offset state =
    match State.lookup_pure_unop_eq_expr var_id Expr.Base state with
    | Some (e, _) when Formula.is_zero_expr e ->
      (* Base() == 0 *)
      [{ state with
        status = Error (None, loc, instr) }]
    | Some (e, is_current) ->
      dereference_check_lower_bound loc instr e is_current var_id offset state
    | None ->
      (* missing resource *)
      let err_state = { state with
        status = Error (None, loc, instr) }
      in
      let missing_part = Expr.BinOp (
        Peq,
        Expr.UnOp (Base, Var var_id), 
        Expr.BinOp (Pplus, Var var_id, Const (Int (Int64.min 0L offset))))
      in
      let ok_state = { state with
        missing = { state.missing with
          pure = missing_part :: state.missing.pure } }
      in
      [ err_state; ok_state ]

  and dereference_check_lower_bound loc instr base_exp is_current var_id offset state =
    let base_offset = eval_expr_offset base_exp var_id state in
    if (Int64.compare offset base_offset) < 0 then begin
      if is_current then begin
        Format.print_string "[Error]: exec_store failed with: offset of expression is lesser than lower bound\n";
        (* offset out of bounds *)
        [{ state with status = Error (None, loc, instr) }]
        end
      else
        (* missing resource - we can lower the bound *)
        let to_remove = Expr.BinOp (Peq, UnOp (Base, Var var_id), base_exp) in
        let missing_pure = Stdlib.List.filter
          (fun e -> not (Expr.equal e to_remove))
          state.missing.pure
        in
        let to_add = Expr.BinOp (
          Peq,
          UnOp (Base, Var var_id),
          BinOp (Pplus, Var var_id, Const (Int offset)))
        in
        [{ state with missing = {
          state.missing with pure = to_add :: missing_pure } }]
      end
    else
      [state]

  and exec_deref_check_end loc instr var_id offset cell_size state =
    match State.lookup_pure_unop_eq_expr var_id Expr.End state with
    | Some (e, _) when Formula.is_zero_expr e ->
      (* Base() == 0 *)
      [{ state with
        status = Error (None, loc, instr) }]
    | Some (e, is_current) ->
      dereference_check_upper_bound loc instr e is_current var_id offset cell_size state
    | None ->
      (* missing resource *)
      let err_state = { state with
        status = Error (None, loc, instr) }
      in
      let missing_part = Expr.BinOp (
        Peq,
        Expr.UnOp (End, Var var_id),
        Expr.BinOp (Pplus, Var var_id, Const (Int (Stdlib.Int64.add offset cell_size))))
      in
      let ok_state = { state with
        missing = { state.missing with
          pure = missing_part :: state.missing.pure } }
      in
      [ err_state; ok_state ]

  and dereference_check_upper_bound loc instr end_expr is_current var_id offset cell_size state =
    let end_offset = eval_expr_offset end_expr var_id state in
    let access_end = Stdlib.Int64.add offset cell_size in
    if (Int64.compare access_end end_offset) > 0 then begin
      if is_current then begin
        (* offset out of bounds *)
        Format.print_string "[Error]: exec_store failed with: offset of expression is greater than upper bound \n";
        [{ state with status = Error (None, loc, instr) }]
        end
      else
        (* missing resource - we can increase the bound *)
        let to_remove = Expr.BinOp (Peq, UnOp (End, Var var_id), end_expr) in
        let missing_pure = Stdlib.List.filter
          (fun e -> not (Expr.equal e to_remove))
          state.missing.pure
        in
        let to_add = Expr.BinOp (
          Peq,
          UnOp (End, Var var_id),
          BinOp (Pplus, Var var_id, Const (Int access_end)))
        in
        [{ state with missing = {
          state.missing with pure = to_add :: missing_pure } }]
      end
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
    let curr_count = List.count curr_hps ~f:(fun _ -> true) in
    let miss_count = List.count miss_hps ~f:(fun _ -> true) in
    Format.print_string (
      "[Block_fragments] - found " ^
      Int.to_string curr_count ^
      " in state.current ; found " ^
      Int.to_string miss_count ^
      " in state.missing\n"
    );
    Format.print_string (
      "[LHS] - typ=" ^ Typ.to_string lhs_typ ^ " ; id=" ^ Int.to_string lhs_var_id ^ " ; offset=" ^ Int64.to_string lhs_offset ^ "\n"
    );
    (** Applies block split result: removes the matched predicate, adds split fragments,
        runs [store_dereference_assign], then fixes up the separated [new_exp_points_to]
        using [canonical_rhs] from [AddressStored] if a pointer was stored *)
    let handle_block_split_res ?(to_missing=false) to_remove to_add part rest new_dest_id (new_exp_points_to: heap_pred) =
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
        | ValueStored state ->
          (state, new_exp_points_to)
        | AddressStored { state; canonical_rhs } ->
          (* address was stored — fix up the separated ExpPointsTo using
             the canonical RHS that subst_apply actually substituted *)
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
      let spatial = new_exp_points_to ::
        (if to_missing then state.missing.spatial else state.current.spatial)
      in
      if to_missing then
        [ { state with missing = { state.missing with spatial } } ]
      else
        [ { state with current = { state.current with spatial } } ]
    in
    match try_block_split curr_hps with
    | Some block_split_res ->
      begin match block_split_res with
      | ExpExactMatch { block_split_args = { to_remove; to_add; new_exp_points_to; new_dest_id }; old_dest = _ } ->
        (* TODO - what to do with old_dest ?? *)
        handle_block_split_res to_remove to_add curr_hps curr_rest new_dest_id new_exp_points_to
      | BlockExactMatch { to_remove; to_add; new_exp_points_to; new_dest_id }
      | BlockEdgeMatch { to_remove; to_add; new_exp_points_to; new_dest_id }
      | BlockMiddleMatch { to_remove; to_add; new_exp_points_to; new_dest_id } ->
        handle_block_split_res to_remove to_add curr_hps curr_rest new_dest_id new_exp_points_to
      end
    | None ->
      begin match try_block_split miss_hps with
      | Some block_split_res ->
        begin match block_split_res with
        | ExpExactMatch { block_split_args = { to_remove; to_add; new_exp_points_to; new_dest_id }; old_dest = _ } ->
          handle_block_split_res ~to_missing:true to_remove to_add miss_hps miss_rest new_dest_id new_exp_points_to
        | BlockExactMatch { to_remove; to_add; new_exp_points_to; new_dest_id }
        | BlockEdgeMatch { to_remove; to_add; new_exp_points_to; new_dest_id }
        | BlockMiddleMatch { to_remove; to_add; new_exp_points_to; new_dest_id } ->
          handle_block_split_res ~to_missing:true to_remove to_add miss_hps miss_rest new_dest_id new_exp_points_to
      end
      | None ->
        (* missing resource *)
        let err_state = { state with status = Error (None, loc, instr) } in
        let cell_id = Id.fresh () in
        let lhs_expr = Expr.Var cell_id in
        let missing_spatial = ExpPointsTo (
          Expr.BinOp (Pplus, Var lhs_var_id, Const (Int lhs_offset)),
          Expr.Const (Int cell_size),
          lhs_expr)
        in
        let assign_res = assign state cell_id lhs_expr in
        let state, missing_spatial = match assign_res with
          | ValueStored state ->
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
        let spatial = missing_spatial :: state.missing.spatial in
        let ok_state = { state with missing = { state.missing with spatial } } in
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
    let { current } = state in [{
      state with
      current = {
        spatial = BlockPointsTo (source, size) :: current.spatial;
        pure =
          BinOp (Peq, UnOp (Base, source), source) ::
          BinOp (Peq, UnOp (End, source), BinOp (Pplus, source, size)) ::
          current.pure
      };
    }]

  (* Note: free(NULL) is translated by SIL as Metadata.Skip, so we do not handle it here.
     A NULL value stored in a variable (e.g. void* x = NULL; free(x);) would go through
     the store/load sequence before reaching free, and would have been caught by dereference
     checks earlier in execution. Skipping explicit NULL handling for now. *)
  and exec_free_instr loc instr _actual actual_expr state =
    let open State in
    match base_and_offset_of_expr actual_expr state with
    | Some (base_id, offset) ->
      free_block loc instr base_id offset state
    | None ->
      [{ state with
        status = Error (None, loc, instr) }]

  and exec_metadata_instr metadata state =
    let open Sil in
    match metadata with
    | VariableLifetimeBegins { pvar; typ = _; loc = _; is_cpp_structured_binding = _} ->
        Format.print_string "[SIL_VARIABLE_LIFETIME_BEGINS]\n";
        begin match
          lookup_variable_id (Var.of_pvar pvar) state.vars
        with
        | Some id ->
          let base_constr = Expr.BinOp (Peq, UnOp (Base, Var id), Const (Int 0L)) in
          let end_constr = Expr.BinOp (Peq, UnOp (End, Var id), Const (Int 0L)) in
          let current = { state.current with
            pure = base_constr :: end_constr :: state.current.pure } in
          [{ state with current }]
        | None -> Logging.die InternalError
          "[Error]: VariableLifetimeBegins instruction was triggered but no matching variable was found in our state"
        end
    | ExitScope (var_list, _loc) ->
      Format.print_string "[SIL_EXIT_SCOPE]\n";
      let state = List.fold var_list ~init:state
        ~f:(fun state var ->
          match var with
          | Var.LogicalVar ident ->
            begin match lookup_variable_id (Var.of_id ident) state.vars with
            | Some id ->
              { state with
                vars = VarIdMap.remove id state.vars;
                types = VarIdMap.remove id state.types;
                subst = VarIdMap.remove id state.subst }
            | None -> state
            end
          | _ -> state)
      in
      [state]
    | Nullify (_pvar, _loc) ->
      Format.print_string "[SIL_NULLIFY]\n";
      [state]
    | Skip ->
      Format.print_string "[SIL_SKIP]\n";
      [state]
    | LoopBackEdge _ ->
      Format.print_string "[SIL_LOOPBACK_EDGE]\n";
      [state]
    | LoopEntry _ ->
      Format.print_string "[SIL_LOOP_ENTRY]\n";
      [state]
    | _ ->
      [state]

    (** Checks whether freeing pointer [id] at [offset] is valid and adds Freed constraint.
        Steps: 1) check double free, 2) find Base constraint, 3) compare offsets *)
    and free_block loc instr id offset state =
      let open State in
      (* Step 1: check if already freed *)
      if State.is_freed_expr id state then
        (* double free *)
        [{ state with status = Error (None, loc, instr) }]
      else
      (* Step 2: find Base(Var id) == some_exp *)
      match State.lookup_pure_unop_eq_expr id Expr.Base state with
      | Some (base_exp, _is_current) ->
        if Formula.is_zero_expr base_exp then
          (* Base(id) == 0 means no memory allocated *)
          [{ state with status = Error (None, loc, instr) }]
        else
          let base_offset = eval_expr_offset base_exp id state in
          if Int64.equal base_offset offset then
            (* happy path: offset matches base, add Freed to current *)
            let pure = Expr.UnOp (Freed, Var id) :: state.current.pure in
            [{ state with current = { state.current with pure } }]
          else
            (* free called with non-base pointer, hard error *)
            [{ state with status = Error (None, loc, instr) }]
      | None ->
        (* missing resource: no Base constraint found *)
        let err_state = { state with status = Error (None, loc, instr) } in
        let missing_base = Expr.BinOp (
          Peq,
          UnOp (Base, Var id),
          BinOp (Pplus, Var id, Const (Int offset)))
        in
        let missing = { state.missing with
          pure = missing_base :: state.missing.pure }
        in
        let pure = Expr.UnOp (Freed, Var id) :: state.current.pure in
        let ok_state = { state with
          current = { state.current with pure };
          missing }
        in
        (* Note: unmatched base_exp patterns (not BinOp/Var/Const(0)) are not possible
           at this stage but will need handling once symbolic offsets are introduced *)
        [err_state; ok_state]

end

  let run (analysis_data : IntraproceduralAnalysis.t) (init_state : State.t) =
    let open Procdesc in
    let open TransferFunctions2 in
    let open State in
    let proc_desc = analysis_data.proc_desc in
    let start_node = get_start_node proc_desc in
    let states_at = ref IdMap.empty in
    let error_states = ref [] in
    let ok_states = ref [] in
    let add_states node new_states = 
      let old = IdMap.find_opt (Node.get_id node) !states_at
        |> Option.value ~default:[] in
      let combined = old @ new_states in
      states_at :=
        IdMap.add (Node.get_id node) combined !states_at
    in
    let worklist = Stdlib.Queue.create () in
    add_states start_node [init_state];
    Stdlib.Queue.add start_node worklist;
    while not (Stdlib.Queue.is_empty worklist) do
      let node = Stdlib.Queue.take worklist in
      let incoming =
        IdMap.find (Node.get_id node) !states_at
      in
      let instrs = Node.get_instrs node in
      let outgoing = 
        Instrs.fold ~init:incoming
          ~f:(fun states instr ->
            List.concat_map ~f:(fun state ->
              match state.status with
                Error _ -> [state]
              | Ok ->
                exec_instr node analysis_data state instr
              ) states
            ) instrs
      in
      let ok_states', new_errors =
        Stdlib.List.partition (fun s ->
          match s.status with
            Ok -> true
          | Error _ -> false)
          outgoing
      in
      error_states := new_errors @ !error_states;
      ok_states := ok_states' @ !ok_states;
      if not (List.is_empty ok_states') then
        Node.get_succs node
        |> List.iter ~f:(fun succ ->
          add_states succ outgoing;
          Stdlib.Queue.add succ worklist)
    done;
    (!ok_states, !error_states)
