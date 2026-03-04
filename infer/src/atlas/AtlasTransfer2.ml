
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
    | Sil.Load { id; e = rhs; typ; loc } ->
      (* Format.print_string ("\nSIL.Load rhs:" ^ sil_exp_to_string rhs ^ "\n"); *)
      exec_load_instr loc id typ rhs (sil_exp_to_expr rhs state) state
    | Sil.Store {e1 = lhs; typ = lhs_typ; e2 = rhs; loc} ->
      (* Format.print_string ("\nSIL store lhs:" ^ sil_exp_to_string lhs ^ "\n"); *)
      (* Format.print_string ("\nSIL store rhs:" ^ sil_exp_to_string rhs ^ "\n"); *)
      let lhs_expr = sil_exp_to_expr lhs state in
      let rhs_expr = sil_exp_to_expr rhs state in
      exec_store_instr loc lhs_typ lhs lhs_expr rhs_expr state
    | Sil.Call
      ( (ident, typ), Exp.Const (Const.Cfun procname), (actual, _) :: _, _loc, _ )
        when BuiltinDecl.(match_builtin malloc procname (Procname.to_string procname)) ->
          exec_malloc_instr ident typ (sil_exp_to_expr actual state) state
    | Sil.Call
      ( _, Exp.Const (Const.Cfun procname), (actual, _) :: _, loc, _ )
        when BuiltinDecl.(match_builtin free procname (Procname.to_string procname)) ->
          exec_free_instr loc actual (sil_exp_to_expr actual state) state
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
    if is_dereference_sil_exp rhs then begin match
      get_base_and_offset_from_expr rhs (expr_normalize rhs_expr state) state with
        Some (rhs_id, off) ->
          exec_load_deref loc lhs_id rhs_id off state
      | None ->
        (* TODO: should throw - if is_dereference_sil is true we have to find a base *)
        [{ state with
            status = Error;
            err_loc = Some loc;
            (* err_issue = TODO register new issue type *) }]
    end else
      assign_to_variable lhs_id rhs_expr state

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
      begin match eval_offset base expr state with
        Some offset -> Some (base, offset)
      | None -> Some (base, 0L) (* TODO revisit *)
      end
    | _ ->
      (* there should not be multiple pointers *)
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
  
  (** Ids [lhs_id] and [rhs_id] must be canonical!
    At this point does not support loading multiple cells,
    heap_pred_find_opt uses only id, not Var id + Const Int offset
    to match heap predicate, so the block might still be missing
    and we just found some other block at different offset TODO *)
  and exec_load_deref loc lhs_id rhs_id off state =
    let open Formula in
    let open State in
    let open Expr in
    match heap_pred_find_opt rhs_id state.current with
      Some PointsToBlock (src, size, block)
    | Some PointsToUniformBlock (src, size, block, _) ->
      let size' =
        match eval_expr_to_int64 size with
          Some i -> i
        | None -> Int64.max_value (* TODO fix me: should throw after we make sure this cannot happen *)
      in
      if (Int64.compare off size') > 0 || (Int64.compare off 0L) < 0 then
        (* Error: offset out of bounds *)
        [{ state with
            status = Error;
            err_loc = Some loc;
            (* err_issue = TODO register new issue type *) }]
      else
        if block.freed then
          (* Error: block is freed *)
          [{ state with
              status = Error;
              err_loc = Some loc;
              (* err_issue = TODO register new issue type *) }]
        else
          let new_src = expr_normalize (BinOp (Pplus, src, Const (Int off))) state in
          (* TODO: consider removing size from ExpPointsTo *)
          let pred = PointsToExp (new_src, Const (Int 0L), Var lhs_id) in
          let current = add_heap_pred pred state.current in
          [{ state with current }]
    | Some PointsToExp _
      (* Error: missing memory block *)
    | None ->
      (* Error: missing heap predicate *)
      let err_state = { state with
        status = Error;
        err_loc = Some loc;
        (* err_issue = TODO register new issue type *) }
      in
      let missing_block = {
      id = Id.fresh ();
      base = 0L;
      end_ = 0L; (* do we really need base, end_ ? *)
      freed = false; }
      in
      let missing_part = PointsToBlock (Var rhs_id, Const (Int Int64.max_value), missing_block) in
      let missing = add_heap_pred missing_part state.missing in
      let src = BinOp (Pplus, Var rhs_id, Const (Int off)) in
      let current_part = PointsToExp (src, Const (Int 0L), Var lhs_id) in
      (* TODO: consider removing size from ExpPointsTo *)
      let current = add_heap_pred current_part state.current in
      err_state :: [{ state with current = current; missing = missing }]

  and exec_store_instr loc _lhs_typ lhs lhs_expr rhs_expr state =
    let open State in
    let open Expr in
    if is_dereference_sil_exp lhs then
      let lhs_norm = expr_normalize lhs_expr state in
      begin match get_base_and_offset_from_expr lhs lhs_norm state with
        Some (lhs_id, off) ->
          exec_store_deref loc lhs_id off lhs_norm rhs_expr state
      | None ->
        (* TODO: should throw - if is_dereference_sil is true we have to find a base *)
        [{ state with
            status = Error;
            err_loc = Some loc;
            (* err_issue = TODO register new issue type *) }]
    end else
      let rhs_norm = expr_normalize rhs_expr state in
      begin match lhs_expr with
        Var id ->
        assign_to_variable id rhs_norm state
      | _ ->
        let lhs_norm = expr_normalize lhs_expr state in
        let exp = BinOp (Peq, lhs_norm, rhs_norm) in
        let current =
          { state.current with pure = exp :: state.current.pure }
        in [{ state with current }]
      end

  and exec_store_deref loc _lhs_id off lhs_norm rhs_expr state =
    let open State in
    let open Formula in
    let open Expr in
    match heap_pred_find_opt_block_points_to_by_dest lhs_norm state with
    | _, Some PointsToBlock (src, size, block)
    | _, Some PointsToUniformBlock (src, size, block, _) ->
      begin match has_error_exec_store loc src size off block.freed state with
        Some error -> error
      | None ->
        let rhs_norm = expr_normalize rhs_expr state in
        begin match lhs_norm with
        | Var id ->
          assign_to_variable id rhs_norm state
        | _ ->
          let exp = BinOp (Peq, lhs_norm, rhs_norm) in
          let current =
            { state.current with pure = exp :: state.current.pure }
          in
          [{ state with current }]
        end
      end
    | Some PointsToExp (src, _, _), None ->
      (* Error: missing memory block *)
      let missing_block = {
        id = Id.fresh ();
        base = 0L;
        end_ = 0L; (* do we really need base, end_ ? *)
        freed = false; }
      in
      let missing_block_src =
        match find_opt_ptr_base src state with
        | Some id -> Var id
        | None -> Var (Id.fresh ())
          (* 
          let id = Id.fresh () in
          let var = Var.of_id (Ident.create Ident.knormal id) in
          let vars = (var, id) :: state.vars in
          let types = VarIdMap.add id Typ.Pk_pointer state.types in
          *)
      in
      let missing_part =
        PointsToBlock (missing_block_src, Undef, missing_block)
      in
      let missing = add_heap_pred missing_part state.missing in
      let rhs_norm = expr_normalize rhs_expr state in
      begin match lhs_norm with
      | Var id ->
        assign_to_variable id rhs_norm { state with missing }
      | _ ->
        let exp = BinOp (Peq, lhs_norm, rhs_norm) in
        let current =
          { state.current with pure = exp :: state.current.pure }
        in
        [{ state with current; missing }]
      end
    | _ ->
      (* Error: missing heap predicate *)
      let missing_block = {
        id = Id.fresh ();
        base = 0L;
        end_ = 0L;
        freed = false;
      } in
      let missing_part = 
        PointsToBlock (Var (Id.fresh ()), Undef, missing_block)
      in
      let missing = add_heap_pred missing_part state.missing in
      let rhs_norm = expr_normalize rhs_expr state in
      begin match lhs_norm with
      | Var id ->
        assign_to_variable id rhs_norm { state with missing }
      | _ ->
        let exp = BinOp (Peq, lhs_norm, rhs_norm) in
        let current =
          { state.current with pure = exp :: state.current.pure }
        in
        [{ state with current; missing }]
      end
  
  and has_error_exec_store loc block_src_expr block_size_expr offset is_freed_block state =
    let open State in
    let src_offset =
      match find_opt_ptr_base block_src_expr state with
      | Some id ->
        eval_offset id block_src_expr state
      | None ->
        None
    in
    let size =
      eval_state_expr_to_int64_opt block_size_expr state
    in
    let abs_offset = Option.bind src_offset
      ~f:(fun x -> Some (Stdlib.Int64.add x offset))
    in
    let is_out_of_bounds = 
      match abs_offset, size with
      | Some off, None
        when (Int64.compare off 0L) < 0 ->
          true
      | Some off, Some s
        when (Int64.compare off 0L) < 0 ||
        (Int64.compare off s) > 0 ->
          true
      | _ ->
        false
    in
    if is_out_of_bounds then
      (* Error : offset out of bounds *)
      Some [{ state with
        status = Error;
        err_loc = Some loc;
        (* err_issue = TODO register new issue type *) }]
    else
      if is_freed_block then
        (* Error: block is freed *)
        Some [{ state with
          status = Error;
          err_loc = Some loc;
          (* err_issue = TODO register new issue type *) }]
      else
        None

  (** Finds a id of a variable inside [expr] using type information from [state]*)
  and find_opt_ptr_base expr state =
    let open State in
    match expr with
    | Expr.Var id ->
      begin match VarIdMap.find_opt id state.types with
      | Some typ ->
        if Typ.is_pointer typ then
          Some id
        else
          None
      | None ->
        None
      end
    | Expr.UnOp (_, e) ->
      find_opt_ptr_base e state
    | Expr.BinOp (_, e1, e2) ->
      begin match find_opt_ptr_base e1 state with
      | (Some _) as res -> res
      | None ->
        find_opt_ptr_base e2 state
      end
    | _ ->
      None


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
          status = Error;
          err_loc = Some loc;
          (* err_issue = register new issue *)}]
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

    (** Tries to extract size from Expr.t [e] using [state] *)
    and get_malloc_size_of_sil_exp e state =
      let open State in
      let open Expr in
      match e with
      | Var id ->
        begin
          match Formula.lookup_pure_const_exp_of_id id state.current.pure with
          | Some exp -> exp
          | None -> e
        end
      | _ -> e

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
          status = Error;
          err_loc = Some loc;
          (* err_issue = register new issue *) }
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
          status = Error;
          err_loc = Some loc;
          err_issue = Some IssueType.atlas_free_non_base_pointer }]
      else
        if is_freed_block then
          (* Error: double free *)
          Some [{ state with
            status = Error;
            err_loc = Some loc;
            err_issue = Some IssueType.atlas_double_free }]
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
                Error -> [state]
              | Ok ->
                exec_instr node analysis_data state instr
              ) states
            ) instrs
      in
      let ok_states, new_errors =
        Stdlib.List.partition (fun s ->
          match s.status with
            Ok -> true
          | Error -> false)
          outgoing
      in
      error_states := new_errors @ !error_states;
      if not (List.is_empty ok_states) then
        Node.get_succs node
        |> List.iter ~f:(fun succ ->
          add_states succ outgoing;
          Stdlib.Queue.add succ worklist)
    done;
    (!states_at, !error_states)