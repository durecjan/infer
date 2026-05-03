open! IStd

module Analyzer =
  AbstractInterpreter.MakeDisjunctive
    (AtlasTransfer.TransferFunctions)
    (struct
      let join_policy = TransferFunctions.UnderApproximateAfter Config.atlas_max_disjuncts
      let widen_policy =
        TransferFunctions.UnderApproximateAfterNumIterations Config.atlas_widen_threshold
    end)

let checker (analysis_data : IntraproceduralAnalysis.t) : unit =
  let proc_name = Procdesc.get_proc_name analysis_data.proc_desc in
  (* Optional procname filter: when [--atlas-procname NAME] is set, skip every
     procedure whose name does not match exactly. *)
  let skip = match Config.atlas_procname_filter with
    | Some target -> not (String.equal target (Procname.to_string proc_name))
    | None -> false
  in
  if skip then () else
  let init_state = AtlasState.empty analysis_data in
  let initial = ([init_state], AtlasDomain.NonDisjDomain.bottom) in
  match Analyzer.compute_post analysis_data ~initial analysis_data.proc_desc with
  | Some (final_domain, _non_disj) ->
    (* Deduplicate states using alpha-equality, preserving arrival order. *)
    let states =
      List.fold final_domain ~init:[] ~f:(fun acc s ->
        if List.exists acc ~f:(fun s' -> AtlasDomain.state_alpha_equal s s') then acc
        else s :: acc)
      |> List.rev
    in
    Format.print_string (
      "\nAtlas finished procedure " ^ Procname.to_string proc_name ^ "\n");
    List.iter states ~f:(fun state ->
      Format.print_string (AtlasState.to_string state));
    Format.print_string "\n================\n[SUMMARY]:\n================\n";
    if List.is_empty states then Format.print_string "RESULT_UNKNOWN";
    let errors = List.filter states ~f:(fun s ->
      match s.AtlasState.status with
      | AtlasState.Ok -> false
      | AtlasState.Error _ -> true)
    in
    if not (List.is_empty errors) then begin
      List.iter errors ~f:(fun s ->
        match s.AtlasState.status with
        | AtlasState.Error (msg, loc, _instr) ->
          let open Location in
          Format.print_string (
            "RESULT_FALSE=" ^ msg ^
            " LOCATION=[line " ^ Int.to_string loc.line ^
            "; column " ^ Int.to_string loc.col ^ "]\n")
        | AtlasState.Ok -> ())
    end else if not (List.is_empty states) then
      Format.print_string "RESULT_TRUE";
  | None ->
    Format.print_string (
      "Atlas: compute_post returned None for " ^ Procname.to_string proc_name ^ "\n")
