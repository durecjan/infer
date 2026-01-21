open! IStd

module Domain = AtlasDomain

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

let double_free (r : reporter) (loc : Location.t) (block : Domain.BlockId.t) =
  report r loc IssueType.atlas_double_free
    (Format.asprintf
         "free called on already freed block (blockId=%a)"
         Domain.BlockId.pp block)

let free_non_base_pointer (r : reporter) (loc : Location.t) (block : Domain.BlockId.t) (offset : Domain.Address.t) =
  report r loc IssueType.atlas_free_non_base_pointer
    (Format.asprintf
         "free called with non-base pointer (blockId=%a, offset=%a)"
         Domain.BlockId.pp block
         Domain.Address.pp offset)

let use_after_free (r: reporter) (loc: Location.t) (var: Var.t) (block: Domain.BlockId.t) =
  report r loc IssueType.atlas_use_after_free
    (Format.asprintf
         "usage of variable (%a) storing a value pointing to freed block (blockId=%a)"
         Var.pp var
         Domain.BlockId.pp block)

let free_invalid_addr (r: reporter) (loc: Location.t) (value: Domain.Value.t) =
  report r loc IssueType.atlas_free_invalid_addr
    (Format.asprintf
          "free called with invalid address (value=%a)"
          Domain.Value.pp value)


let rec eval_exp (astate : Domain.t) (exp : Exp.t) : Domain.Value.t =
  match exp with
  | Exp.Const (Const.Cint c) ->
    (match IntLit.to_int c with
      | Some n -> Domain.Value.of_int n
      | None -> Domain.Value.Top)
  | Exp.Sizeof { typ = _; nbytes = Some n; dynamic_length = _; subtype = _; nullable = _ } ->
    Domain.Value.of_int n
  | Exp.Var id ->
    Domain.lookup_var (Var.of_id id) astate
  | Exp.Lvar pvar ->
    Domain.lookup_var (Var.of_pvar pvar) astate
  | Exp.Cast (_typ, e) ->
    eval_exp astate e
  | Exp.BinOp (op, e1, e2) ->
    let v1 = eval_exp astate e1 in
    let v2 = eval_exp astate e2 in
    Domain.Value.eval_binop op v1 v2
  | _ ->
    Domain.Value.Top


let exec_load_instr lhs rhs astate r loc =
  let value = eval_exp astate rhs in
    let var = Var.of_id lhs in
    begin
      match rhs, value with
      | Exp.Lvar pvar, Domain.Value.Ptr { block = block; _ }
        when Domain.is_freed block astate ->
          let err_var = Var.of_pvar pvar in
          use_after_free r loc err_var block ;
          Domain.store_var var value astate
      | _ ->
        Domain.store_var var value astate
    end


let exec_store_instr lhs rhs astate r loc =
  match lhs with
  | Exp.Lvar pvar ->
    let var = Var.of_pvar pvar in
    let value = eval_exp astate rhs in
    let lhs' = eval_exp astate lhs in
    begin
      match lhs' with
      | Domain.Value.Ptr { block = block; _ }
        when Domain.is_freed block astate ->
          use_after_free r loc var block ;
          Domain.store_var var value astate
      | _ ->
        Domain.store_var var value astate
    end
  | _ -> astate


let exec_malloc_instr lhs actual astate =
  let size = eval_exp astate actual in
  let astate', ptr = Domain.alloc_block size astate in
  let var = Var.of_id lhs in
  Domain.store_var var ptr astate'


let exec_free_instr actual astate r loc =
  match eval_exp astate actual with
  | Domain.Value.Ptr { block; offset }
    when Domain.Address.equal offset (Domain.Address.NonTop 0)
    || Domain.Address.equal offset Domain.Address.Top ->
      if Domain.is_freed block astate then
        begin
          double_free r loc block ;
          astate
        end
      else 
        Domain.free_block block astate
  | Domain.Value.Ptr { block; offset } ->
    free_non_base_pointer r loc block offset ;
    Domain.free_block block astate
  | Domain.Value.Int 0 ->
    astate (* free(NULL) *)
  | Domain.Value.Int i ->
    free_invalid_addr r loc (Domain.Value.Int i) ;
    astate
  | Domain.Value.Top ->
    astate (* we do not know anything *)


module TransferFunctions = struct
  module CFG = ProcCfg.Normal
  module Domain = Domain

  type instr = Sil.instr

  let exec_instr astate node (analysis_data : IntraproceduralAnalysis.t) instr =
    Format.printf
      "@[<v2>Atlas BEFORE instr at %a:@,%a@]@."
      Procdesc.Node.pp node
      Domain.pp astate ;

    let r = reporter_of_analysis analysis_data in
    let astate' =
      match instr with
      | Sil.Load { id = lhs; e = rhs; typ = _lhs_typ; loc = loc} ->
        exec_load_instr lhs rhs astate r loc
      | Sil.Store {e1= lhs; typ= _lhs_typ; e2= rhs; loc= loc} ->
        exec_store_instr lhs rhs astate r loc
      | Sil.Call
        ( (id, _), Exp.Const (Const.Cfun procname), (actual, _) :: _, _, _ )
          when BuiltinDecl.(match_builtin malloc procname (Procname.to_string procname)) ->
            exec_malloc_instr id actual astate
      | Sil.Call
        ( _, Exp.Const (Const.Cfun procname), (actual, _) :: _, loc, _ )
          when BuiltinDecl.(match_builtin free procname (Procname.to_string procname)) ->
            exec_free_instr actual astate r loc
      | _ ->
        astate
    in

    Format.printf
      "@[<v2>Atlas AFTER instr:@,%a@]@."
      Domain.pp astate' ;
    Format.print_newline ();

    astate'
end

let run (analysis_data : IntraproceduralAnalysis.t) (astate : AtlasDomain.t) =
  let proc_desc = analysis_data.proc_desc in
  let nodes = Procdesc.get_nodes proc_desc in
  List.fold_left
    ~f:(fun state node ->
        let instrs = Procdesc.Node.get_instrs node in
        Instrs.fold
          ~f:(fun state instr ->
            TransferFunctions.exec_instr state node analysis_data instr)
          ~init:state
          instrs)
    ~init:astate
    nodes