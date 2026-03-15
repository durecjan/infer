
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
      match expr_base_and_offset rhs_expr state with
      | Some (rhs_id, off) ->
          exec_load_deref loc instr lhs_id tenv typ rhs_id off state
      | None ->
        Logging.die InternalError
          "[Error] method is_sil_dereference returned true but no base pointer variable found"
    else begin
      if is_sil_address_assign rhs && is_pointer_type typ then
        match expr_base_and_offset rhs_expr state with
        | Some (rhs_id, off) ->
          let rhs_canonical = canonical_expr state.subst rhs_id off in
          [{ state with
            subst = VarIdMap.add lhs_id rhs_canonical state.subst }]
        | None ->
          Logging.die InternalError
          "[Error] method is_sil_dereference returned true but no base pointer variable found"
      else
        let rhs_norm = expr_normalize rhs_expr state in
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
      let exp = Expr.BinOp (Peq, Var lhs_id, expr_normalize rhs state) in
      let current =
        { state.current with pure = exp :: state.current.pure }
      in
      [{ state with current }]
  
  (** Ids [lhs_id] and [rhs_id] must be canonical! *)
  and exec_load_deref loc instr lhs_id tenv rhs_typ rhs_id off state =
    let cell_size = typ_size_of tenv rhs_typ in
    [state]
    |> concat_map_ok_states
      (dereference_check_freed loc instr rhs_id)
    |> concat_map_ok_states
      (exec_deref_check_base loc instr rhs_id off)
    |> concat_map_ok_states
      (exec_deref_check_end loc instr rhs_id off cell_size)
    |> concat_map_ok_states
      (exec_load_deref_check_heap_pred loc instr lhs_id rhs_id off)
  
  and exec_load_deref_check_heap_pred loc instr lhs_id rhs_id off state =
    let open State in
    let open Formula in
    match state_heap_pred_find_block_points_to rhs_id state with
    | Some BlockPointsTo (_, size) ->
      if (Int64.compare off 0L) <> 0 then
        (* check offset *)
        exec_load_deref_check_offset loc instr lhs_id rhs_id off size state
      else
        exec_load_deref_assign loc instr lhs_id rhs_id off state
    | _ ->
      (* missing resource *)
      let err_state = { state with
        status = Error (None, loc, instr) }
      in
      let missing_part =
        BlockPointsTo (Expr.Var rhs_id, Expr.Undef)
      in
      let spatial = missing_part :: state.missing.spatial in
      let ok_state = { state with
        missing = { state.missing with spatial } }
      in
      (* only check non-zero offset *)
      if (Int64.compare off 0L) <> 0 then begin
        [err_state; ok_state]
        |> concat_map_ok_states
          (exec_load_deref_check_offset loc instr lhs_id rhs_id off Expr.Undef)
      end else
        [err_state; ok_state]
        |> concat_map_ok_states
          (exec_load_deref_assign loc instr lhs_id rhs_id off)

  and exec_load_deref_check_offset loc instr lhs_id rhs_id rhs_offset block_size state =
    let open State in
    if (Int64.compare rhs_offset 0L) < 0 then
      (* offset out of bounds *)
      [{ state with
        status = Error (None, loc, instr) }]
    else begin
      match eval_state_expr_to_int64_opt block_size state with
      | Some s when (Int64.compare rhs_offset s) > 0 ->
        (* offset out of bounds *)
        [{ state with
          status = Error (None, loc, instr) }]
      | _ ->
        (* correct *)
        exec_load_deref_assign loc instr lhs_id rhs_id rhs_offset state
      end

  and exec_load_deref_assign loc instr lhs_id rhs_id rhs_offset state =
    let open State in
    let src =
      Expr.BinOp (Pplus, Var rhs_id, Const (Int rhs_offset))
    in
    match state_heap_pred_find_exp_points_to src state with
    | Some ExpPointsTo (_, _, Var cell_id) ->
      [(subst_add ~from_:lhs_id ~to_:cell_id state)]
    | _ ->
      (* missing resource *)
      (* also it is possible it's a uniform block created by calloc() *)
      let cell_id = Id.fresh () in
      let missing_part =
        Formula.ExpPointsTo (src, Undef, Var cell_id)
      in
      let current_part = 
        Expr.BinOp (Peq, Var cell_id, Undef)
      in
      let ok_state = { state with
        missing = { state.missing with
          spatial = missing_part :: state.missing.spatial };
        current = { state.current with
          pure = current_part :: state.current.pure } }
      in
      let error_state = { state with
        status = Error (None, loc, instr) }
      in
      [error_state; ok_state]

  and exec_store_instr loc instr tenv lhs_typ lhs lhs_expr rhs_expr state =
    let open State in
    if is_sil_dereference lhs then
      match expr_base_and_offset lhs_expr state with
      | Some (lhs_id, off) ->
          exec_store_deref loc instr tenv lhs_typ lhs_id off rhs_expr state
      | None ->
        Logging.die InternalError
          "[Error] method is_sil_dereference returned true but no base pointer variable found"
    else begin
      if is_sil_address_assign lhs && is_pointer_type lhs_typ then begin
        match expr_base_and_offset lhs_expr state with
        | Some (lhs_id, off) ->
          let lhs_canonical = canonical_expr state.subst lhs_id off in
          let lhs_norm = expr_normalize (subst_expr_to_formula_expr lhs_canonical) state in
          let rhs_norm = expr_normalize rhs_expr state in
          (* it must be ensured rhs contains a temp variable~! *)
          [(subst_apply ~from_:rhs_norm ~to_:lhs_norm state)]
        | None ->
          Logging.die InternalError
            "[Error] method is_sil_address_assign returned true but no base pointer variable found"
      end else
        let rhs_norm = expr_normalize rhs_expr state in
        let lhs_norm = expr_normalize lhs_expr state in
        match lhs_norm with
        | Var id ->
          assign_to_variable id rhs_norm state
        | _ ->
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
    if state_is_freed_expr var_id state then begin
      Format.print_string "[Error]: exec_store failed with: memory block is freed\n";
      [{ state with status = Error (None, loc, instr)}]
      end
    else [state]

  and exec_deref_check_base loc instr var_id offset state =
    match state_find_pure_unop_eq_expr var_id Expr.Base state with
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
    let base_offset = expr_eval_offset base_exp var_id state in
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
    match state_find_pure_unop_eq_expr var_id Expr.End state with
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
    let end_offset = expr_eval_offset end_expr var_id state in
    if (Int64.compare offset end_offset) > 0 then begin
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
          UnOp (Base, Var var_id),
          BinOp (Pplus, Var var_id, Const (Int (Stdlib.Int64.add offset cell_size))))
        in
        [{ state with missing = {
          state.missing with pure = to_add :: missing_pure } }]
      end
    else
      [state]

  and store_dereference_try_match_heap_predicates loc instr lhs_typ lhs_var_id lhs_offset cell_size rhs_expr state =
    let rhs_norm = expr_normalize rhs_expr state in
    let try_block_split hps =
      state_heap_try_block_split hps lhs_var_id lhs_offset cell_size
    in
    let assign ?to_missing:(to_missing=false) state lhs_id lhs_expr =
      store_dereference_assign ~to_missing:to_missing state lhs_typ lhs_id lhs_expr rhs_norm
    in
    let transfor_spatial to_remove from to_add rest =
      let removed = Stdlib.List.filter
          (fun hp -> not (heap_pred_equal hp to_remove))
          from
        in
        List.append removed (List.append to_add rest)
    in
    let curr_hps, curr_rest, miss_hps, miss_rest =
      state_heap_find_block_fragments state lhs_var_id lhs_offset cell_size
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
    match try_block_split curr_hps with
    | Some block_split_res ->
      begin match block_split_res with
      | ExpExactMatch { block_split_args = { to_remove; to_add; new_dest_id }; old_dest = _ } ->
        (* TODO - what to do with old_dest ?? *)
        let spatial =
          transfor_spatial to_remove curr_hps to_add curr_rest
        in
        let state =
          { state with current = { state.current with spatial } }
        in
        let lhs_expr = Expr.Var new_dest_id in
        [ assign state new_dest_id lhs_expr ]
      | BlockExactMatch { to_remove; to_add; new_dest_id }
      | BlockEdgeMatch { to_remove; to_add; new_dest_id }
      | BlockMiddleMatch { to_remove; to_add; new_dest_id } ->
        let spatial =
          transfor_spatial to_remove curr_hps to_add curr_rest
        in
        let state =
          { state with current = { state.current with spatial } }
        in
        let lhs_expr = Expr.Var new_dest_id in
        [ assign state new_dest_id lhs_expr ]
      end
    | None ->
      begin match try_block_split miss_hps with
      | Some block_split_res ->
        begin match block_split_res with
        | ExpExactMatch { block_split_args = { to_remove; to_add; new_dest_id }; old_dest = _ } ->
          let spatial =
            transfor_spatial to_remove miss_hps to_add miss_rest
          in
          let state = 
            { state with missing = { state.missing with spatial } }
          in
          let lhs_expr = Expr.Var new_dest_id in
          [ assign ~to_missing:true state new_dest_id lhs_expr ]
        | BlockExactMatch { to_remove; to_add; new_dest_id }
        | BlockEdgeMatch { to_remove; to_add; new_dest_id }
        | BlockMiddleMatch { to_remove; to_add; new_dest_id } ->
          let spatial =
            transfor_spatial to_remove miss_hps to_add miss_rest
          in
          let state = 
            { state with missing = { state.missing with spatial } }
          in
          let lhs_expr = Expr.Var new_dest_id in
          [ assign ~to_missing:true state new_dest_id lhs_expr ]
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
        let spatial = missing_spatial :: state.missing.spatial in
        let state = { state with missing = { state.missing with spatial } } in
        err_state :: [ assign ~to_missing:true state cell_id lhs_expr ]
      end

  and exec_store_deref_check_heap_pred loc instr lhs_typ lhs_var_id lhs_offset rhs_expr state =
    let open State in
    let open Formula in
    (* TODO FIX ME - implement splitting blocks *)
    match state_heap_pred_find_block_points_to lhs_var_id state with
    | Some (BlockPointsTo (_, size)) ->
      (* correct *)
      if (Int64.compare lhs_offset 0L) <> 0 then
        exec_store_deref_check_offset loc instr lhs_typ lhs_var_id lhs_offset size rhs_expr state
      else
        let rhs_norm = expr_normalize rhs_expr state in
        exec_store_deref_assign lhs_typ lhs_var_id lhs_offset rhs_norm state
    | _ ->
      (* missing resouce *)
      let err_state = { state with
        status = Error (None, loc, instr) }
      in
      let missing_part =
        BlockPointsTo (Expr.Var lhs_var_id, Expr.Undef)
      in
      let spatial = missing_part :: state.missing.spatial in
      let ok_state = { state with
        missing = { state.missing with spatial } }
      in
      (* only check non-zero offset *)
      if (Int64.compare lhs_offset 0L) <> 0 then begin
        [err_state; ok_state]
        |> concat_map_ok_states
          (exec_store_deref_check_offset loc instr lhs_typ lhs_var_id lhs_offset Expr.Undef rhs_expr)
      end else
        let rhs_norm = expr_normalize rhs_expr state in
        [err_state; ok_state]
        |> concat_map_ok_states
          (exec_store_deref_assign lhs_typ lhs_var_id lhs_offset rhs_norm)

  and exec_store_deref_check_offset loc instr lhs_typ lhs_var_id lhs_offset block_size rhs_expr state =
    let open State in
    if (Int64.compare lhs_offset 0L) < 0 then begin
      (* offset out of bounds *)
      [{ state with
        status = Error (None, loc, instr) }]
    end else begin
      match eval_state_expr_to_int64_opt block_size state with
      | Some s when (Int64.compare lhs_offset s) > 0 ->
        (* offset out of bounds *)
        [{ state with
          status = Error (None, loc, instr) }]
      | _ ->
        (* correct *)
        let rhs_norm = expr_normalize rhs_expr state in
        exec_store_deref_assign lhs_typ lhs_var_id lhs_offset rhs_norm state
      end
  
  and exec_store_deref_assign lhs_typ lhs_var_id lhs_offset rhs_norm state =
    let open State in
    let src = Expr.BinOp (Pplus, Var lhs_var_id, Const (Int lhs_offset)) in
    let spatial_part, block_cell_id =
      (* block cell can already exist! *)
      match state_heap_pred_find_exp_points_to src state with
      | Some ((Formula.ExpPointsTo (_, _, Var id)) as hp) ->
        hp, id
      | _ ->
        let block_cell_id = Id.fresh () in
        let spatial_part =
          Formula.ExpPointsTo (src, Undef, Var block_cell_id)
        in
        spatial_part, block_cell_id
    in
    let spatial = spatial_part :: state.current.spatial in
    let pure =
      Expr.BinOp (Peq, Var block_cell_id, rhs_norm) :: state.current.pure
    in
    let types = VarIdMap.add block_cell_id lhs_typ state.types in
    [{state with current = { spatial; pure; }; types; }]


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
    let size = expr_normalize actual state in
    (* try to evaluate the size *)
    let size = match eval_state_expr_to_int64_opt size state with
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

  and exec_free_instr loc instr _actual actual_expr state =
    let open State in
    (*
    match expr_normalize actual_expr state with
    | Const (Ptr 0) | Const (Int 0L) -> 
        [state] (* free(NULL); *)
    | _ -> begin *)
    match expr_base_and_offset actual_expr state with
    | Some (base_id, offset) ->
      free_block loc instr base_id offset state
    | None ->
      [{ state with
        status = Error (None, loc, instr) }]

  and exec_metadata_instr metadata state =
    let open Sil in
    match metadata with
    | VariableLifetimeBegins { pvar; typ; loc = _; is_cpp_structured_binding = _}
      when not (is_pointer_type typ) ->
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
    | VariableLifetimeBegins { pvar = _; typ = _; loc = _; is_cpp_structured_binding = _} ->
      Format.print_string "[SIL_VARIABLE_LIFETIME_BEGINS]\n";
      [state]
    | ExitScope (_var_list, _loc) ->
      Format.print_string "[SIL_EXIT_SCOPE]\n";
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

    (** Marks block stored in pointer with [id] and offset [off] as freed. Reports any issues using [loc] *)
    and free_block loc instr id off state =
      let open State in
      let open Formula in
      let open Expr in
      match heap_pred_take_opt id state.current.spatial with
      | Some (((BlockPointsTo (source, _)) as hp), rest) ->
        begin match has_error_exec_free loc instr off false (* TODO FIX ME find Freed() constraint *) state with
          Some error -> error
        | None ->
          let spatial = hp :: rest in (* TODO FIX ME - we do not need to take the hp *)
          let pure =
            Expr.UnOp (Expr.Freed, source) :: state.current.pure
          in
          [{ state with
            current = { spatial; pure } }]
        end
      (* duplicate code caused by heap_pred not being a record *)
      | Some (((UniformBlockPointsTo (source, _, _)) as hp), rest) ->
        begin match has_error_exec_free loc instr off false (* TODO FIX ME find Freed() constraint *) state with
          Some error -> error
        | None ->
          let spatial = hp :: rest in (* TODO FIX ME - we do not need to take the hp *)
          let pure =
            Expr.UnOp (Expr.Freed, source) :: state.current.pure
          in
          [{ state with
            current = { spatial; pure } }]
        end
      | Some _
        (* Error: missing memory block *)
      | None ->
        (* Error: missing heap predicate *)
        let pure =
          BinOp (Peq, UnOp (Base, Var id), Const (Int 0L)) :: state.current.pure
        in
        let err_state = { state with
          current = { state.current with pure };
          status = Error (None, loc, instr) }
        in
        (* add id -> { block with freed = false } to missing *)
        let missing_spatial_part =
          BlockPointsTo (Var id, Const (Int Int64.max_value))
        in
        (* add Base(id) == id & End(id) == id + size to missing *)
        let missing_pure_base_part, missing_pure_end_part = (
          BinOp (Peq, UnOp (Base, Var id), Var id),
          BinOp (Peq, UnOp (End, Var id), BinOp (Pplus, Var id, Const (Int Int64.max_value)))
        ) in
        (* add id -> { block with freed = true } to current *)
        let current_part =
          BlockPointsTo(Var id, Const (Int Int64.max_value))
        in
        let missing_part = add_heap_pred missing_spatial_part state.missing in
        let missing =
          { missing_part with
            pure = missing_pure_base_part :: missing_pure_end_part :: missing_part.pure }
        in
        let current = {
          spatial = current_part :: state.current.spatial;
          pure = (Expr.UnOp (Expr.Freed, Expr.Var id)) :: state.current.pure }
        in
        err_state :: [{ state with current; missing }]

    and has_error_exec_free loc instr var_off is_freed_block state = 
      let open State in
      if not (Int64.equal var_off 0L) then
        (* Error: freeing memory address not returned by malloc *)
        Some [{ state with
          status = Error (None, loc, instr) }]
      else
        if is_freed_block then
          (* Error: double free *)
          Some [{ state with
            status = Error (None, loc, instr) }]
        else
          (* Ok *)
          None

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
