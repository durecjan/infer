
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
    let r = reporter_of_analysis analysis_data in
    let states = match instr with
    | Sil.Load { id = ident; e = rhs; typ = _; loc } ->
      (* Format.print_string ("\nSIL.Load rhs:" ^ sil_exp_to_string rhs ^ "\n"); *)
      let (rhs_expr, state') = sil_exp_to_expr rhs state in
      exec_load_instr loc ident rhs rhs_expr state'
    | Sil.Store {e1 = lhs; typ = _; e2 = rhs; loc} ->
      (* Format.print_string ("\nSIL store lhs:" ^ sil_exp_to_string lhs ^ "\n"); *)
      (* Format.print_string ("\nSIL store rhs:" ^ sil_exp_to_string rhs ^ "\n"); *)
      let (lhs', state') = sil_exp_to_expr lhs state in
      let (rhs', state') = sil_exp_to_expr rhs state' in
      exec_store_instr r loc lhs' rhs' state'
    | Sil.Call
      ( (ident, _), Exp.Const (Const.Cfun procname), (actual, _) :: _, _loc, _ )
        when BuiltinDecl.(match_builtin malloc procname (Procname.to_string procname)) ->
          let (actual', state') = sil_exp_to_expr actual state in
          exec_malloc_instr ident actual' state'
    | Sil.Call
      ( _, Exp.Const (Const.Cfun procname), (actual, _) :: _, loc, _ )
        when BuiltinDecl.(match_builtin free procname (Procname.to_string procname)) ->
          let (actual', state') = sil_exp_to_expr actual state in
          exec_free_instr r loc actual' state'
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

  and exec_load_instr loc ident rhs rhs_expr state =
    let open State in
    let open Formula in
    let open Expr in
    let lhs_var = Var.of_id ident in
    let (lhs_id, state) =
      (* TODO: always makes fresh i believe *)
      get_existing_canonical_or_mk_fresh_id_of_var lhs_var state
    in
    if is_dereference_sil_exp rhs then begin
      match get_base_and_offset_from_expr rhs_expr with
        Some (id, off) when is_heap_pred id state.current ->
          (* Ok : we found base, offset, heap_pread *)
          begin
            match heap_pred_find_block id state.current.spatial with
              Some { freed = false; end_ = size } ->
              (* Ok : we found base, offset, heap_pred, block with freed = false *)
              if (Int64.compare off size) > 0 || (Int64.compare off 0L) < 0 then
                (* Error: offset out of bounds *)
                [{ state with
                    status = Error;
                    err_loc = Some loc;
                    (* err_issue = TODO register new issue type *) }]
              else
                let dest = BinOp (Pplus, Var lhs_id, Const (Int off)) in
                let pred = PointsToExp (rhs_expr, (* TODO could be cell size? *) Const (Int 0L), dest) in
                let current = add_heap_pred pred state.current in
                [{ state with current }]
            | Some { freed = true } ->
              (* Error: block is freed *)
              [{ state with
                  status = Error;
                  err_loc = Some loc;
                  (* err_issue = TODO register new issue type *) }]
            | None ->
              (* Missing resource: memory block *)
              (* if is PointsTo dest then something? *)
              (* if is PointsTo src then something else? *)
              [state]
          end
      | Some (_base, _off) ->
        (* Missing resource: heap predicate *)
        (* add heap predicate PointsToBlock src = BinOp(Pplus, base, off) size = Expr.Undef dest = <new block> to state.missing *)
        (* add heap predicate like in the Ok case to state.current *)
        [state]
      | None ->
        (* Error: we found nothing in the provided sil *)
        [{ state with
            status = Error;
            err_loc = Some loc;
            (* err_issue = TODO register new issue type *) }]
    end else
      assign_to_variable lhs_id rhs_expr state

  and is_dereference_sil_exp exp =
    match exp with
      Exp.Var _ -> true
    | Exp.Lfield ({ exp = e }, _, _) -> is_dereference_sil_exp e
    | Exp.Lindex (e, _) -> is_dereference_sil_exp e
    | Exp.Cast (_, e) -> is_dereference_sil_exp e
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
        [{ state with subst = SubstMap.add lhs_id rhs_id state.subst }]
    | _ ->
      let exp = BinOp (Peq, Var lhs_id, rhs) in
      let current =
        { state.current with pure = exp :: state.current.pure }
      in
      [{ state with current }]

  and exec_store_instr r loc lhs rhs state =
    (*
    match lhs with 
      Var id 
    | Lfield ({ base = Var id }, _fieldname, _typ) 
    | Lindex (Var id, _offset_exp)
    -> DEREFERENCE!
    *)
    let open State in
    let open Formula in
    let open Expr in
    check_valid_deref r loc lhs state;
    check_valid_deref r loc rhs state;
    match lhs with
    | Var lhs_id ->
      assign_to_variable lhs_id rhs state
    | _ ->
      let exp = BinOp (Peq, lhs, rhs) in
      let current =
        { state.current with pure = exp :: state.current.pure }
      in
      [{ state with current }]

  and check_valid_deref _r _loc _e _state = (*
    let open State in
    let open Formula in
    (* Format.print_string ("CHECK_VALID_DEREF_EXP:\n" ^ (Expr.to_string state.vars e) ); *)
    let _ =
      match get_base_and_offset_from_expr e with
        None -> (* Format.print_string "\nCONST EXPRESSION\n"; *) () (* const expression *)
      | Some (id, _off)
        when not (is_heap_pred id state.current) -> 
        (* Format.print_string "\nASSIGNMENT\n"; *)() (* assignment *)
      | Some (id, _) ->
        begin
          (* Format.print_string "\nDEREF\n"; *)
          match heap_pred_find_block id state.current.spatial with
          | Some { freed = true } ->
            use_after_free r loc
          | _ -> (* Format.print_string "\nDID_NOT_FIND_MEM_BLOCK\n"; *)()
        end
    in *)
    ()

  and exec_malloc_instr ident actual state =
    let open State in
    let (id, state) = (* maybe this lookup is unnecessary? *)
      get_existing_canonical_or_mk_fresh_id_of_var (Var.of_id ident) state
    in
    let source = Expr.Var id in
    let size = get_malloc_size_of_sil_exp actual state in
    let open Formula in
    let block = {
      id = Id.fresh ();
      base = 0L;
      end_ = 0L; (* do we really need base, end_ ? *)
      freed = false;
    }
    in
    let open Expr in
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

  and exec_free_instr r loc actual state =
    match get_base_and_offset_from_expr actual with (* TODO does not handle variables with value of NULL - these should behave as Skip *)
      None -> [state] (* unknown free target *)
    | Some (base_id, offset) ->
      free_block r loc base_id offset state

  and exec_metadata_instr metadata state =
    let open Sil in
    match metadata with
    | VariableLifetimeBegins { pvar = _ ; typ = _; loc = _; is_cpp_structured_binding = _} ->
      [state]
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

    (** Tries to extract variable and integer offset from Expr.t [exp] *)
    and get_base_and_offset_from_expr exp =
      let open Expr in
      let rec traverse acc = function
      | Var id -> Some (id, acc)
      | BinOp (Pplus, e, Const (Int i)) | BinOp (Pplus, Const (Int i), e) ->
        traverse (Stdlib.Int64.add acc i) e
      | BinOp (Pminus, e, Const (Int i)) ->
        traverse (Stdlib.Int64.sub acc i) e
      | _ -> None
      in
      traverse 0L exp

    (** Marks block stored in pointer with [id] and offset [off] as freed. Reports any issues using [r] and [loc] *)
    and free_block r loc id off state =
      let open State in
      let open Formula in
      let open Expr in
      match take_heap_pred id state.current.spatial with
      | None ->
        begin (* might be an alias *)
          match heap_pred_find_src_of_dest id state.current with
            Some (Var id') -> free_block r loc id' off state
          | None | Some _ -> [state] (* unknown target memory block *)
        end
      | Some (PointsToBlock (source, size, block), rest) ->
        if block.freed then begin
          double_free r loc;
          [state]
        end else
          if not (Int64.equal off 0L) then begin
            free_non_base_pointer r loc;
            [state] (* note: probably also mark as freed ? *)
          end else
            let block' = { block with freed = true } in
            let spatial = 
              PointsToBlock (source, size, block') :: rest
            in
            [{ state with
              current = { state.current with spatial } }]
      | Some _ -> [state] (* TODO *)


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