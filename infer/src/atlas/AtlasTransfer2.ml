
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

(*
let use_after_free (r: reporter) (loc: Location.t) =
  report r loc IssueType.atlas_use_after_free
    (Format.asprintf
      "usage of variable storing a value pointing to freed block")
*)

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

    let r = reporter_of_analysis analysis_data in
    let state' = match instr with
    | Sil.Load { id = ident; e = rhs; typ = _; loc = _} ->
      exec_load_instr ident rhs state
    | Sil.Store {e1 = lhs; typ = _; e2 = rhs; loc = _} ->
      exec_store_instr lhs rhs state
    | Sil.Call
      ( (ident, _), Exp.Const (Const.Cfun procname), (actual, _) :: _, _loc, _ )
        when BuiltinDecl.(match_builtin malloc procname (Procname.to_string procname)) ->
          exec_malloc_instr ident actual state
    | Sil.Call
      ( _, Exp.Const (Const.Cfun procname), (actual, _) :: _, loc, _ )
        when BuiltinDecl.(match_builtin free procname (Procname.to_string procname)) ->
          exec_free_instr r loc actual state
    | Sil.Metadata metadata ->
      exec_metadata_instr metadata state
    | _ ->
      state
    in

    Format.print_string (State.to_string state');

    state'

  and exec_load_instr ident rhs state =
    match rhs with
    | Exp.Lvar pvar | Exp.Cast (_, Exp.Lvar pvar) ->
      unify_vars (Var.of_id ident) (Var.of_pvar pvar) state
    (* | Lfield *)
    (* | Lindex *)
    | _ -> state
    
  and exec_store_instr lhs rhs state =
    match lhs, rhs with
    | Exp.Lvar pvar, Exp.Sizeof { nbytes = Some n }
    | Exp.Lvar pvar, Exp.Cast (_, Exp.Sizeof { nbytes = Some n }) ->
      assign_expr_to_var (Var.of_pvar pvar) (Expr.Const (Expr.Int (Int64.of_int n))) state
    | Exp.Lvar pvar, Exp.Cast (_, Exp.Const c)
    | Exp.Lvar pvar, Exp.Const c ->
      assign_expr_to_var (Var.of_pvar pvar) (get_expr_of_sil_exp_const c) state
    | Exp.Lvar pvar, Exp.Cast (_, Exp.Var ident) 
    | Exp.Lvar pvar, Exp.Var ident ->
      unify_vars (Var.of_pvar pvar) (Var.of_id ident) state
    (* | Sizeof { nbytes ; dynamic_length } -> *)
    (* | Lfield *)
    (* | Lindex *)
    | _ -> state

  and exec_malloc_instr ident actual state =
    let open State in
    let (id, state) =
      get_existing_canonical_or_mk_fresh_id_of_var (Var.of_id ident) state
    in
    let source = Expr.Var (id) in
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
          BinOp (Peq, UnOp (End, BinOp (Pplus, source, size)), source) ::
          formula.pure
      };
    }

  and exec_free_instr r loc actual state =
    match get_base_and_offset_from_sil actual with (* TODO does not handle variables with value of NULL - these should behave as Skip *)
    | None -> state (* unknown free target var *)
    | Some (base, offset) ->
      let open State in
      match get_variable_id base state with
      | None -> state (* unknown free target var id *)
      | Some id ->
        free_block r loc id offset state

  and exec_metadata_instr metadata state =
    let open Sil in
    match metadata with
    | VariableLifetimeBegins { pvar = _ ; typ = _; loc = _; is_cpp_structured_binding = _} ->
      state
    | Nullify (_pvar, _loc) ->
      state (* TODO *)
    | ExitScope (_var_list, _loc) ->
      state (* TODO *)
    | Skip | _ ->
      state

    (** Adds substitution [lhs_var] = [rhs_var] to [state] *)
    and unify_vars lhs_var rhs_var state =
      let open State in
      let (lhs_id, state) =
        get_existing_canonical_or_mk_fresh_id_of_var lhs_var state
      in
      match get_variable_id rhs_var state with
      | Some rhs_id ->
        subst_add ~from_:lhs_id ~to_:rhs_id state
      | None ->
        let (rhs_id, state) =
          get_existing_canonical_or_mk_fresh_id_of_var  rhs_var state
        in
        subst_add ~from_:lhs_id ~to_:rhs_id state

    (** Adds pure constraint [var] = [expr] to [state] *)
    and assign_expr_to_var var expr state =
      let open State in
      let (id, state) = 
        get_existing_canonical_or_mk_fresh_id_of_var var state
      in
      let open Expr in
      let e = BinOp (Peq, Var id, expr) in
      let formula =
        { state.formula with pure = e :: state.formula.pure }
      in
      { state with formula }

    (** Converts SIL Exp.t [const] to custom Expr.t interpretation *)
    and get_expr_of_sil_exp_const const =
      match const with
      | Const.Cint i -> Expr.Const (Int (Z.to_int64 (IntLit.to_big_int i)))
      | Const.Cstr s -> Expr.Const (String s)
      | Const.Cfloat f -> Expr.Const (Float f)
      | _ -> Expr.Undef

    (** Tries to extract size from SIL Exp.t [e] or from [state] *)
    and get_malloc_size_of_sil_exp e state =
      match e with
      | Exp.Lvar pvar | Exp.Cast (_ ,Exp.Lvar pvar) ->
        begin
          match get_const_expr_from_var (Var.of_pvar pvar) state with
          | Some size -> size
          | None -> Expr.Undef
        end
      | Exp.Var ident | Exp.Cast (_, Exp.Var ident) ->
        begin
          match get_const_expr_from_var (Var.of_id ident) state with
          | Some size -> size
          | None -> Expr.Undef
        end
      | Exp.Const c | Exp.Cast(_, Exp.Const c) ->
        get_expr_of_sil_exp_const c
      | Exp.Sizeof { nbytes = Some i} ->
        Expr.Const (Int (Int.to_int64 i))
      (* | Sizeof { nbytes ; dynamic_length } -> *)
      | _ -> Expr.Undef

    (** Tries to extract Expr.Const from [var] using [state] *)
    and get_const_expr_from_var var state =
      let open State in
      match get_variable_id var state with
      | Some id ->
        Formula.lookup_pure_const_exp_of_id id state.formula.pure
      | None -> Some Expr.Undef

    (** Tries to extract variable and integer offset from SIL [exp] *)
    and get_base_and_offset_from_sil exp =
      let rec traverse acc = function
      | Exp.Cast (_, e) ->
        traverse acc e
      | Exp.Var ident -> Some (Var.of_id ident, acc)
      | Exp.Lvar pvar -> Some (Var.of_pvar pvar, acc)
      | Exp.BinOp ((Binop.PlusA _ | Binop.PlusPI), e, Exp.Const (Const.Cint c))
      | Exp.BinOp ((Binop.PlusA _ | Binop.PlusPI), Exp.Const (Const.Cint c), e) ->
        traverse (Stdlib.Int64.add acc (Z.to_int64 (IntLit.to_big_int c))) e
      | Exp.BinOp ((Binop.MinusA _ | Binop.MinusPI), e, Exp.Const (Const.Cint c)) ->
        traverse (Stdlib.Int64.add acc (Z.to_int64 (IntLit.to_big_int c))) e
      | _ -> None
      in
      traverse 0L exp

    (** Marks block stored in pointer with [id] and offset [off] as freed. Reports any issues using [r] and [loc] *)
    and free_block r loc id off state =
      let open State in
      let open Formula in
      match take_heap_pred id state.formula.spatial with
      | None -> state (* unknown target memory block *)
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