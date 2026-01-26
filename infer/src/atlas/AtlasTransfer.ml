open! IStd

module Domain = AtlasDomain
module Address = Domain.Address
module BlockId = Domain.BlockId
module Value = Domain.Value
module ExpEvalRes = Domain.ExpEvalRes

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


let double_free (r : reporter) (loc : Location.t) (block : BlockId.t) =
  report r loc IssueType.atlas_double_free
    (Format.asprintf
      "free called on already freed block (blockId=%a)"
      BlockId.pp block)

let free_non_base_pointer (r : reporter) (loc : Location.t) (block : BlockId.t) (offset : Address.t) =
  report r loc IssueType.atlas_free_non_base_pointer
    (Format.asprintf
      "free called with non-base pointer (blockId=%a, offset=%a)"
      BlockId.pp block
      Address.pp offset)

let use_after_free (r: reporter) (loc: Location.t) (var: Var.t) (block: BlockId.t) =
  report r loc IssueType.atlas_use_after_free
    (Format.asprintf
      "usage of variable (%a) storing a value pointing to freed block (blockId=%a)"
      Var.pp var
      BlockId.pp block)

let free_invalid_addr (r: reporter) (loc: Location.t) (value: Value.t) =
  report r loc IssueType.atlas_free_invalid_addr
    (Format.asprintf
      "free called with invalid address (value=%a)"
      Value.pp value)

let ptr_sub_different_blocks (r: reporter) (loc: Location.t) =
  report r loc IssueType.atlas_ptr_sub_different_blocks
    (Format.asprintf
      "subtraction of pointers which point to different memory blocks")

let ptr_comparison_error (r: reporter) (loc: Location.t) =
  report r loc IssueType.atlas_ptr_comparison_error
    (Format.asprintf
      "invalid pointer comparison")


let handle_exp_eval_res (r : reporter) (loc : Location.t) (res: ExpEvalRes.t) : Domain.Value.t option =
  match res with
  | Ok v -> Some v
  | PtrSubDifferentBlocks ->
    ptr_sub_different_blocks r loc ;
    None
  | PtrComparisonError ->
    ptr_comparison_error r loc ;
    None
  | Unknown ->
    None


let exec_load_instr lhs rhs astate r loc =
  let value = Domain.eval_exp astate rhs in
  let var = Var.of_id lhs in
  match handle_exp_eval_res r loc value with
  | Some v ->
    begin
      match v with
      | Ptr { block; _ }
        when Domain.is_freed block astate ->
          let err_var =
            match rhs with
            | Exp.Lvar pvar -> Var.of_pvar pvar
            | _ -> Var.of_id lhs
          in
          use_after_free r loc err_var block
      | _ -> ()
    end ;
    Domain.store_var var v astate
  | None ->
    Domain.store_var var Value.Top astate


let exec_store_instr lhs rhs astate r loc =
  match lhs with
  | Exp.Lvar pvar ->
    let var = Var.of_pvar pvar in
    let value = Domain.eval_exp astate rhs in
    let lhs' = Domain.eval_exp astate lhs in
    begin
      match handle_exp_eval_res r loc value with
      | Some v ->
        begin
          match handle_exp_eval_res r loc lhs' with
          | Some Value.Ptr { block }
            when Domain.is_freed block astate ->
              use_after_free r loc var block
          | _ -> ()
        end ;
        Domain.store_var var v astate
      | None ->
        Domain.store_var var Value.Top astate
    end
  (* Lfield *)
  (* Lindex *)
  (* nested dereferences *)
  | _ -> astate


let exec_malloc_instr lhs actual astate r loc =
  let size = Domain.eval_exp astate actual in
  let size_value = 
    match handle_exp_eval_res r loc size with
    | Some v -> v
    | None -> Value.Top
  in
  let astate', ptr = Domain.alloc_block size_value astate in
  let var = Var.of_id lhs in
  Domain.store_var var ptr astate'


let exec_free_instr actual astate r loc =
  let result = Domain.eval_exp astate actual in
  match handle_exp_eval_res r loc result with
  | Some Value.Ptr { block; offset }
    when Address.equal offset (Address.NonTop 0)
    || Address.equal offset Address.Top ->
      if Domain.is_freed block astate then (
        double_free r loc block ;
        astate)
      else
        Domain.free_block block astate
  | Some Value.Ptr { block; offset } ->
    free_non_base_pointer r loc block offset ;
    Domain.free_block block astate
  | Some Value.Int 0 ->
    astate (* free(NULL) *)
  | Some Value.Int i ->
    free_invalid_addr r loc (Value.Int i) ;
    astate
  | Some Value.Top ->
    astate (* we do not know anything *)
  | None -> astate


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
      | Sil.Load { id = lhs; e = rhs; typ = _typ; loc = loc} ->
        exec_load_instr lhs rhs astate r loc
      | Sil.Store {e1 = lhs; typ = _typ; e2 = rhs; loc = loc} ->
        exec_store_instr lhs rhs astate r loc
      | Sil.Call
        ( (id, _), Exp.Const (Const.Cfun procname), (actual, _) :: _, loc, _ )
          when BuiltinDecl.(match_builtin malloc procname (Procname.to_string procname)) ->
            exec_malloc_instr id actual astate r loc
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