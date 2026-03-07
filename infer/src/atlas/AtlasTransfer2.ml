
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

module TransferFunctions2 = struct
  module CFG = ProcCfg.Normal

  type instr = Sil.instr

  let rec exec_instr _node analysis_data state instr =
    Format.fprintf Format.err_formatter "@[<h>%a;@]@;" (Sil.pp_instr ~print_types:true Pp.text) instr;
    Format.print_newline ();

    let open State in
    let _r = reporter_of_analysis analysis_data in
    let states = match instr with
    | Sil.Load { id; e; typ; loc } ->
      let rhs_expr = sil_exp_to_expr e state in

      Format.print_string (
        "[SIL_LOAD]\n[SIL_INSTR_RHS]: " ^ sil_exp_to_string e ^ "\n[RHS_EXPR]: " ^ Expr.to_string state.vars rhs_expr ^ "\n");

      exec_load_instr loc id typ e rhs_expr state
    | Sil.Store {e1; typ; e2; loc} ->

      Format.print_string (
        "[SIL_STORE]\n[SIL_INSTR_LHS]: " ^ sil_exp_to_string e1 ^ "\n[SIL_INSTR_RHS]: " ^ sil_exp_to_string e2) ;

      let lhs_expr = sil_exp_to_expr e1 state in
      let rhs_expr = sil_exp_to_expr e2 state in

      Format.print_string (
        "\n[LHS_EXPR]: " ^ Expr.to_string state.vars lhs_expr ^ "\n[RHS_EXPR]: " ^ Expr.to_string state.vars rhs_expr ^ "\n");

      exec_store_instr loc typ e1 lhs_expr rhs_expr state
    | Sil.Call
      ( (ident, typ), Exp.Const (Const.Cfun procname), (actual, _) :: _, _loc, _ )
        when BuiltinDecl.(match_builtin malloc procname (Procname.to_string procname)) ->
          let actual_expr = sil_exp_to_expr actual state in

          Format.print_string (
            "[SIL_MALLOC]\n[SIL_ACTUAL]: " ^ sil_exp_to_string actual ^ "\n[ACTUAL_EXPR]: " ^ Expr.to_string state.vars actual_expr ^ "\n");

          exec_malloc_instr ident typ actual_expr state
    | Sil.Call
      ( _, Exp.Const (Const.Cfun procname), (actual, _) :: _, loc, _ )
        when BuiltinDecl.(match_builtin free procname (Procname.to_string procname)) ->
          let actual_expr = sil_exp_to_expr actual state in

          Format.print_string (
            "[SIL_MALLOC]\n[SIL_ACTUAL]: " ^ sil_exp_to_string actual ^ "\n[ACTUAL_EXPR]: " ^ Expr.to_string state.vars actual_expr ^ "\n");

          exec_free_instr loc actual actual_expr state
    | Sil.Prune (_exp, _loc, _is_then_branch, _if_kind) ->
      [state] (* TODO - for starters, kill unsat states, in other words implement eval_cond *)
    | Sil.Metadata metadata ->
      exec_metadata_instr metadata state
    | _ ->
      [state]
    in

    Format.print_string (String.concat (
      List.map
        ~f:(fun state -> State.to_string state)
        states));

    states

  and exec_load_instr loc lhs typ rhs rhs_expr state =
    let open State in
    let lhs_id = Id.fresh () in
    let state = { state with
      vars = (Var.of_id lhs, lhs_id) :: state.vars;
      types = VarIdMap.add lhs_id typ state.types }
    in
    let rhs_norm = expr_normalize rhs_expr state in
    if is_dereference_sil_exp rhs then begin match
      get_base_and_offset_from_expr rhs rhs_norm state with
        Some (rhs_id, off) ->
          exec_load_deref loc lhs_id rhs_id off state
      | None ->
        (* TODO: should throw - if is_dereference_sil is true we have to find a base *)
        [{ state with
            status = Error (
              None, Some loc); }]
    end else
      assign_to_variable lhs_id rhs_norm state

  (** Tries to extract base (pointer variable) and offset
      from given [expr] using the Sil [exp] and [state]. 
      Always pass a normalized [expr]! *)
  and get_base_and_offset_from_expr exp expr state =
    let open State in
    (* get temporaries and map them to our variable ids *)
    let vars = Exp.free_vars exp |> Sequence.to_list in
    let var_ids = List.map ~f:(fun ident ->
      get_canonical_var_id (Var.of_id ident) state)
      vars
    in
    (* filter variable ids, looking for variable that has pointer type *)
    let pointers = 
      List.filter ~f:(fun id ->
        match id with
          None -> false (* should not really happen, unless global variable *)
        | Some id ->
          begin match VarIdMap.find_opt id state.types with
            Some typ -> Typ.is_pointer typ
          | None -> false
        end)
        var_ids
    in
    (* evaluate offset *)
    match pointers with
    | [Some base] -> 
      Format.print_string "\n[get_base_and_offset_from_expr]: found base pointer variable\n" ;
      begin match eval_offset base expr state with
        Some offset -> Format.print_string "\n[get_base_and_offset_from_expr]: found offset\n" ; Some (base, offset)
      | None -> Format.print_string "\n[get_base_and_offset_from_expr]: failed to find offset - defaulting to 0L\n" ; Some (base, 0L) (* TODO revisit *)
      end
    | _ ->
      (* there should not be multiple pointers *)
      Format.print_string "\n[get_base_and_offset_from_expr]: failed to find base pointer variable\n" ;
      None

  (** Evaluates [expr], skipping [base] since it is
    a known pointer, handling BinOp | Const | Var ,
    where Var must have a chain of pure constraints,
    eventually leading to Const. If any part fails
    to evaluate, method returns None *)
  and eval_offset base expr state =
    let open Formula in
    let open Expr in
    let open State in
    (* TODO a lot of None cases, revisit *)
    let rec eval_offset acc = function
        Var id when Id.equal id base ->
        Some acc
      | Var id -> begin match
          lookup_pure_const_exp_of_id id state.current.pure with
            Some e -> eval_offset acc e
          | None -> None 
        end
      | BinOp (Pplus, e1, e2) ->
        begin match eval_offset acc e1 with
          Some acc1 -> eval_offset acc1 e2
        | None ->
            match eval_offset acc e2 with
              Some acc2 -> eval_offset acc2 e1
            | None -> None
        end
      | BinOp (Pminus, e, Const (Int i)) ->
          eval_offset (Stdlib.Int64.sub acc i) e
      | Const (Int i) ->
          Some (Stdlib.Int64.add acc i)
      | _ ->
        None
    in
    eval_offset 0L expr

  and is_dereference_sil_exp exp =
    match Exp.ignore_cast exp with
      Exp.Var _ -> true
    | Exp.Lfield ({ exp = e }, _, _) -> is_dereference_sil_exp e
    | Exp.Lindex (e, _) -> is_dereference_sil_exp e
    | _ -> false

  (** If [rhs] is (Var id) then adds substitution, otherwise adds pure constaitn (Var ([lhs_id]) == [rhs]) to [state] *)
  and assign_to_variable lhs_id rhs state =
    let open Expr in
    let open State in
    match rhs with
    | Var rhs_id ->
      (* Both Ids already canonical *)
      if Id.equal lhs_id rhs_id then
        [state]
      else
        [{ state with subst = VarIdMap.add lhs_id rhs_id state.subst }]
    | _ ->
      let exp = BinOp (Peq, Var lhs_id, expr_normalize rhs state) in
      let current =
        { state.current with pure = exp :: state.current.pure }
      in
      [{ state with current }]
  
  (** Ids [lhs_id] and [rhs_id] must be canonical! *)
  and exec_load_deref loc lhs_id rhs_id off state =
    [state]
    |> concat_map_ok_states
      (exec_deref_check_base loc rhs_id)
    |> concat_map_ok_states
      (exec_load_deref_check_heap_pred loc lhs_id rhs_id off)
  
  and exec_load_deref_check_heap_pred loc lhs_id rhs_id off state =
    let open State in
    let open Formula in
    match state_heap_pred_find_block_points_to rhs_id state with
    | Some PointsToBlock (_, size, block) ->
      if block.freed then
        (* freed block *)
        [{ state with
          status = Error (
            Some IssueType.atlas_use_after_free, Some loc;) }]
      else begin
        if (Int64.compare off 0L) <> 0 then
          (* check offset *)
          exec_load_deref_check_offset loc lhs_id rhs_id off size state
        else
          exec_load_deref_assign loc lhs_id rhs_id off state
      end
    | _ ->
      (* missing resource *)
      let err_state = { state with
        status = Error (
          Some IssueType.atlas_use_after_free, Some loc); }
      in
      let missing_block = {
        id = Id.fresh ();
        base = 0L;
        end_ = 0L;
        freed = false; }
      in
      let missing_part =
        PointsToBlock (Expr.Var rhs_id, Expr.Undef, missing_block)
      in
      let spatial = missing_part :: state.missing.spatial in
      let ok_state = { state with
        missing = { state.missing with spatial } }
      in
      (* only check non-zero offset *)
      if (Int64.compare off 0L) <> 0 then begin
        [err_state; ok_state]
        |> concat_map_ok_states
          (exec_load_deref_check_offset loc lhs_id rhs_id off Expr.Undef)
      end else
        [err_state; ok_state]
        |> concat_map_ok_states
          (exec_load_deref_assign loc lhs_id rhs_id off)

  and exec_load_deref_check_offset loc lhs_id rhs_id rhs_offset block_size state =
    let open State in
    if (Int64.compare rhs_offset 0L) < 0 then
      (* offset out of bounds *)
      [{ state with
        status = Error (
          None, Some loc); }]
    else begin
      match eval_state_expr_to_int64_opt block_size state with
      | Some s when (Int64.compare rhs_offset s) > 0 ->
        (* offset out of bounds *)
        [{ state with
          status = Error (
            None, Some loc); }]
      | _ ->
        (* correct *)
        exec_load_deref_assign loc lhs_id rhs_id rhs_offset state
      end

  and exec_load_deref_assign loc lhs_id rhs_id rhs_offset state =
    let open State in
    let src =
      Expr.BinOp (Pplus, Var rhs_id, Const (Int rhs_offset))
    in
    match state_heap_pred_find_exp_points_to src state with
    | Some PointsToExp (_, _, Var cell_id) ->
      [(subst_add ~from_:lhs_id ~to_:cell_id state)]
    | _ ->
      (* missing resource *)
      (* also it is possible it's a uniform block created by calloc() *)
      let cell_id = Id.fresh () in
      let missing_part =
        Formula.PointsToExp (src, Undef, Var cell_id)
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
        status = Error (
          None, Some loc) }
      in
      [error_state; ok_state]

  and exec_store_instr loc lhs_typ lhs lhs_expr rhs_expr state =
    let open State in
    let open Expr in
    if is_dereference_sil_exp lhs then
      let lhs_norm = expr_normalize lhs_expr state in
      begin match get_base_and_offset_from_expr lhs lhs_norm state with
        Some (lhs_id, off) ->
          exec_store_deref loc lhs_typ lhs_id off rhs_expr state
      | None ->
        (* TODO: should throw - if is_dereference_sil is true we have to find a base *)
        [{ state with
            status = Error (
              None, Some loc); }]
    end else
      let rhs_norm = expr_normalize rhs_expr state in
      let lhs_norm = expr_normalize lhs_expr state in
      begin match lhs_norm with
        Var id ->
        assign_to_variable id rhs_norm state
      | _ ->
        let exp = BinOp (Peq, lhs_norm, rhs_norm) in
        let current =
          { state.current with pure = exp :: state.current.pure }
        in [{ state with current }]
      end

  and exec_store_deref loc lhs_typ lhs_var_id lhs_offset rhs_expr state =
    [state]
    |> concat_map_ok_states
      (exec_deref_check_base loc lhs_var_id)
    |> concat_map_ok_states
      (exec_store_deref_check_heap_pred loc lhs_typ lhs_var_id lhs_offset rhs_expr)
  
  and concat_map_ok_states f states = 
    let open State in
    List.concat_map ~f:(fun s ->
      match s.status with
      | Ok -> f s
      | Error _ -> [s])
    states

  and exec_deref_check_base loc lhs_var_id state =
    let open State in
    let open Formula in
    match state_find_pure_base_expr lhs_var_id state with
    | Some e when Formula.is_zero e ->
      (* Base() == 0*)
      [{ state with
        status = Error (
          None, Some loc); }]
    | Some e when Expr.equal e (Expr.Var lhs_var_id) ->
      (* correct *)
      [state]
    | _ ->
      (* missing resource *)
      let err_state = { state with
        status = Error (
          None, Some loc); }
      in
      let missing_part =
        Expr.BinOp (Expr.Peq, Expr.UnOp (Expr.Base, Expr.Var lhs_var_id), Expr.Var lhs_var_id)
      in
      let ok_state = { state with
        missing = { state.missing with
          pure = missing_part :: state.missing.pure } }
      in
      [ err_state; ok_state ]

  and exec_store_deref_check_heap_pred loc lhs_typ lhs_var_id lhs_offset rhs_expr state =
    let open State in
    let open Formula in
    match state_heap_pred_find_block_points_to lhs_var_id state with
    | Some (PointsToBlock (_, size, block)) ->
      if block.freed then
        (* freed block *)
        [{ state with
          status = Error (
            Some IssueType.atlas_use_after_free,
            Some loc); }]
      else begin
        (* correct *)
        if (Int64.compare lhs_offset 0L) <> 0 then
          exec_store_deref_check_offset loc lhs_typ lhs_var_id lhs_offset size rhs_expr state
        else begin
          let rhs_norm = expr_normalize rhs_expr state in
          exec_store_deref_assign lhs_typ lhs_var_id lhs_offset rhs_norm state
        end
      end
    | _ ->
      (* missing resouce *)
      let err_state = { state with
        status = Error (
          None, Some loc); }
      in
      let missing_block = {
        id = Id.fresh ();
        base = 0L;
        end_ = 0L;
        freed = false; }
      in
      let missing_part =
        PointsToBlock (Expr.Var lhs_var_id, Expr.Undef, missing_block)
      in
      let spatial = missing_part :: state.missing.spatial in
      let ok_state = { state with
        missing = { state.missing with spatial } }
      in
      (* only check non-zero offset *)
      if (Int64.compare lhs_offset 0L) <> 0 then begin
        [err_state; ok_state]
        |> concat_map_ok_states
          (exec_store_deref_check_offset loc lhs_typ lhs_var_id lhs_offset Expr.Undef rhs_expr)
      end else
        let rhs_norm = expr_normalize rhs_expr state in
        [err_state; ok_state]
        |> concat_map_ok_states
          (exec_store_deref_assign lhs_typ lhs_var_id lhs_offset rhs_norm)

  and exec_store_deref_check_offset loc lhs_typ lhs_var_id lhs_offset block_size rhs_expr state =
    let open State in
    Format.print_string "[exec_store_deref_check_offset]: checking offset";
    if (Int64.compare lhs_offset 0L) < 0 then begin
      (* offset out of bounds *)
      Format.print_string ("[exec_store_deref_check_offset]: lower bound check failed (offset=" ^ Int64.to_string lhs_offset ^ ")");
      [{ state with
        status = Error (
          None, Some loc); }]
    end else begin
      match eval_state_expr_to_int64_opt block_size state with
      | Some s when (Int64.compare lhs_offset s) > 0 ->
        (* offset out of bounds *)
        Format.print_string "[exec_store_deref_check_offset]: upper bound check failed";
        [{ state with
          status = Error (
            None, Some loc); }]
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
      | Some ((Formula.PointsToExp (_, _, Var id)) as hp) ->
        hp, id
      | _ ->
        let block_cell_id = Id.fresh () in
        let spatial_part =
          Formula.PointsToExp (src, Undef, Var block_cell_id)
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
      vars = (Var.of_id lhs, lhs_id) :: state.vars;
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
    let block = {
      id = Id.fresh ();
      base = 0L;
      end_ = 0L; (* do we really need base, end_ ? *)
      freed = false;
    }
    in
    let { current } = state in [{
      state with
      current = {
        spatial = PointsToBlock (source, size, block) :: current.spatial;
        pure =
          BinOp (Peq, UnOp (Base, source), source) ::
          BinOp (Peq, UnOp (End, source), BinOp (Pplus, source, size)) ::
          current.pure
      };
    }]

  and exec_free_instr loc actual actual_expr state =
    let open State in
    let open Expr in
    match actual_expr with
      Const (Ptr 0) -> 
        [state] (* free(NULL); *)
    | _ -> begin match
      get_base_and_offset_from_expr actual actual_expr state with
        Some (base_id, offset) ->
        free_block loc base_id offset state
      | None ->
        [{ state with
          status = Error (
            None, Some loc); }]
      end

  and exec_metadata_instr metadata state =
    let open Sil in
    let open State in
    match metadata with
    | VariableLifetimeBegins { pvar; typ; loc = _; is_cpp_structured_binding = _} ->
      let id = Id.fresh () in
      [{ state with
        vars = (Var.of_pvar pvar, id) :: state.vars;
        types = VarIdMap.add id typ state.types }]
    | Nullify (_pvar, _loc) ->
      [state] (* TODO *)
    | ExitScope (_var_list, _loc) ->
      [state] (* TODO - maybe when var id is present in the substitution map,
                we can remove it and re-shuffle the change through formula,
                making a new canonical id or removing the constraints *)
    | Skip | _ ->
      [state]

    (** Marks block stored in pointer with [id] and offset [off] as freed. Reports any issues using [loc] *)
    and free_block loc id off state =
      let open State in
      let open Formula in
      let open Expr in
      match heap_pred_take_opt id state.current.spatial with
      | Some (PointsToBlock (source, size, block), rest) ->
        begin match has_error_exec_free loc off block.freed state with
          Some error -> error
        | None ->
          let block' = { block with freed = true } in
          let spatial =
            PointsToBlock (source, size, block') :: rest
          in
          [{ state with
            current = { state.current with spatial } }]
        end
      (* duplicate code caused by heap_pred not being a record *)
      | Some (PointsToUniformBlock (source, size, block, const_val), rest) ->
        begin match has_error_exec_free loc off block.freed state with
          Some error -> error
        | None ->
          let block' = { block with freed = true } in
          let spatial =
            PointsToUniformBlock (source, size, block', const_val) :: rest
          in
          [{ state with
            current = { state.current with spatial } }]
        end
      | Some _
        (* Error: missing memory block *)
      | None ->
        (* Error: missing heap predicate *)
        let pure =
          BinOp (Peq, UnOp (Base, Var id), null) :: state.current.pure
        in
        let err_state = { state with
          current = { state.current with pure };
          status = Error (
            None, Some loc); }
        in
        let missing_block = {
          id = Id.fresh ();
          base = 0L;
          end_ = 0L; (* do we really need base, end_ ? *)
          freed = false; }
        in
        (* add id -> { block with freed = false } to missing *)
        let missing_spatial_part =
          PointsToBlock (Var id, Const (Int Int64.max_value), missing_block)
        in
        (* add Base(id) == id & End(id) == id + size to missing *)
        let missing_pure_base_part, missing_pure_end_part = (
          BinOp (Peq, UnOp (Base, Var id), Var id),
          BinOp (Peq, UnOp (End, Var id), BinOp (Pplus, Var id, Const (Int Int64.max_value)))
        ) in
        (* add id -> { block with freed = true } to current *)
        let current_part =
          PointsToBlock(Var id, Const (Int Int64.max_value), { missing_block with freed = true })
        in
        let missing_part = add_heap_pred missing_spatial_part state.missing in
        let missing =
          { missing_part with
            pure = missing_pure_base_part :: missing_pure_end_part :: missing_part.pure }
        in
        let current = add_heap_pred current_part state.current in
        err_state :: [{ state with current; missing }]

    and has_error_exec_free loc var_off is_freed_block state = 
      let open State in
      if not (Int64.equal var_off 0L) then
        (* Error: freeing memory address not returned by malloc *)
        Some [{ state with
          status = Error (
            Some IssueType.atlas_free_non_base_pointer,
            Some loc); }]
      else
        if is_freed_block then
          (* Error: double free *)
          Some [{ state with
            status = Error (
              Some IssueType.atlas_double_free,
              Some loc); }]
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
