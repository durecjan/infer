open! IStd

module Analyzer =
  AbstractInterpreter.MakeDisjunctive
    (AtlasTransfer.TransferFunctions)
    (struct
      let join_policy = TransferFunctions.UnderApproximateAfter 64
      let widen_policy = TransferFunctions.UnderApproximateAfterNumIterations 5
    end)

let checker (analysis_data : IntraproceduralAnalysis.t) : unit =
  let init_state = AtlasState.empty analysis_data in
  let initial = ([init_state], AtlasDomain.NonDisjDomain.bottom) in
  let proc_name = Procdesc.get_proc_name analysis_data.proc_desc in
  match Analyzer.compute_post analysis_data ~initial analysis_data.proc_desc with
  | Some (final_domain, _non_disj) ->
    let final_states, err_states =
      List.partition_tf final_domain ~f:(fun s ->
        match s.AtlasState.status with
        | AtlasState.Ok -> true
        | AtlasState.Error _ -> false)
    in
    (* Deduplicate states using alpha-equality *)
    let dedup states =
      List.fold states ~init:[] ~f:(fun acc s ->
        if List.exists acc ~f:(fun s' -> AtlasDomain.state_alpha_equal s s') then acc
        else s :: acc)
      |> List.rev
    in
    let final_states = dedup final_states in
    let err_states = dedup err_states in
    Format.printf
      "@[<v2>Atlas finished procedure %a@]@."
      Procname.pp proc_name;
    Format.print_string (
      "\n================\n" ^
      "[FINAL STATES] :\n" ^
      "================\n" ^
      String.concat (
        List.map
          ~f:(fun state -> AtlasState.to_string state)
          final_states));
    Format.print_string (
      "[ERROR STATES] :\n" ^
      "================\n" ^
      String.concat (
        List.map
          ~f:(fun state -> AtlasState.to_string state)
          err_states))
  | None ->
    Format.printf
      "Atlas: compute_post returned None for %a@."
      Procname.pp proc_name
