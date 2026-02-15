
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

  let rec exec_instr state _node analysis_data instr =
    Format.fprintf Format.err_formatter "@[<h>%a;@]@;" (Sil.pp_instr ~print_types:false Pp.text) instr;
    Format.print_newline ();

    let open State in
    let r = reporter_of_analysis analysis_data in
    let state' = match instr with
    | Sil.Load { id = ident; e = rhs; typ = _; loc = _} ->
      (* Format.print_string ("\nSIL.Load rhs:" ^ sil_exp_to_string rhs ^ "\n"); *)
      let (rhs', state') = sil_exp_to_expr rhs state in
      exec_load_instr ident rhs' state'
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
    | Sil.Metadata metadata ->
      exec_metadata_instr metadata state
    | _ ->
      state
    in

    Format.print_string (State.to_string state');

    state'

  and exec_load_instr ident rhs state =
    let open State in
    let open Formula in
    let open Expr in
    let lhs_var = Var.of_id ident in
    let (lhs_id, state) =
      get_existing_canonical_or_mk_fresh_id_of_var lhs_var state
    in
    match get_base_and_offset_from_expr rhs with
      Some (id, _off) when is_heap_pred_source id state.formula ->
        let pred =
          PointsToExp (rhs, Const (Int 0L)(* cell size TODO *), Var lhs_id)
        in
        let formula = add_heap_pred pred state.formula in
        { state with formula }
    | _ -> assign_to_variable lhs_id rhs state

  and assign_to_variable lhs_id rhs state =
    let open Expr in
    let open State in
    match rhs with
    | Var rhs_id ->
      (* Both Ids already canonical *)
      if Id.equal lhs_id rhs_id then
        state
      else
        { state with subst = SubstMap.add lhs_id rhs_id state.subst }
    | _ ->
      let exp = BinOp (Peq, Var lhs_id, rhs) in
      let formula =
        { state.formula with pure = exp :: state.formula.pure }
      in
      { state with formula }

  and exec_store_instr r loc lhs rhs state =
    let open State in
    let open Formula in
    let open Expr in
    check_valid_deref r loc lhs state;
    match lhs with
    | Var lhs_id ->
      assign_to_variable lhs_id rhs state
    | _ ->
      let exp = BinOp (Peq, lhs, rhs) in
      let formula =
        { state.formula with pure = exp :: state.formula.pure }
      in
      { state with formula }

  and check_valid_deref r loc lhs state =
    let open State in
    let open Formula in
    let _ =
      match get_base_and_offset_from_expr lhs with
        None -> Logging.die InternalError "this should be unreachable"
      | Some (lhs_id, _off)
        when not (is_heap_pred_dest lhs_id state.formula) -> 
        ()
      | Some (lhs_id, _) ->
        begin
          match heap_pred_find_block lhs_id state.formula.spatial with
          | Some { freed = true } -> 
            use_after_free r loc
          | _ -> ()
        end
    in
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
      base = 0;
      end_ = 0; (* do we really need base, end_ ? *)
      freed = false;
    }
    in
    let open Expr in
    let { formula } = state in {
      state with
      formula = {
        spatial = PointsToBlock (source, size, block) :: formula.spatial;
        pure =
          BinOp (Peq, UnOp (Base, source), source) ::
          BinOp (Peq, UnOp (End, source), BinOp (Pplus, source, size)) ::
          formula.pure
      };
    }

  and exec_free_instr r loc actual state =
    match get_base_and_offset_from_expr actual with (* TODO does not handle variables with value of NULL - these should behave as Skip *)
      None -> state (* unknown free target *)
    | Some (base_id, offset) ->
      free_block r loc base_id offset state

  and exec_metadata_instr metadata state =
    let open Sil in
    match metadata with
    | VariableLifetimeBegins { pvar = _ ; typ = _; loc = _; is_cpp_structured_binding = _} ->
      state
    | Nullify (_pvar, _loc) ->
      state (* TODO *)
    | ExitScope (_var_list, _loc) ->
      state (* TODO - maybe when var id is present in the substitution map,
                we can remove it and re-shuffle the change through formula,
                making a new canonical id or removing the constraints *)
    | Skip | _ ->
      state

    (** Tries to extract size from Expr.t [e] using [state] *)
    and get_malloc_size_of_sil_exp e state =
      let open State in
      let open Expr in
      match e with
      | Var id ->
        begin
          match Formula.lookup_pure_const_exp_of_id id state.formula.pure with
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
      match take_heap_pred id state.formula.spatial with
      | None ->
        begin (* might be an alias *)
          match heap_pred_find_src_of_dest id state.formula with
            Some (Var id') -> free_block r loc id' off state
          | None | Some _ -> state (* unknown target memory block *)
        end
      | Some (PointsToBlock (source, size, block), rest) ->
        if block.freed then begin
          double_free r loc;
          state
        end else
          if not (Int64.equal off 0L) then begin
            free_non_base_pointer r loc;
            state (* note: probably also mark as freed ? *)
          end else
            let block' = { block with freed = true } in
            let spatial = 
              PointsToBlock (source, size, block') :: rest
            in
            { state with
              formula = { state.formula with spatial } }
      | Some _ -> state (* TODO *)


end

let run (analysis_data : IntraproceduralAnalysis.t) (state : State.t) =
  let proc_desc = analysis_data.proc_desc in
  let nodes = Procdesc.get_nodes proc_desc in
  List.fold_left
    ~f:(fun state node ->
        let instrs = Procdesc.Node.get_instrs node in
        Instrs.fold
          ~f:(fun state instr ->
            TransferFunctions2.exec_instr state node analysis_data instr)
          ~init:state
          instrs)
    ~init:state
    nodes