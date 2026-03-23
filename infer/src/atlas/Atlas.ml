open! IStd

let checker (analysis_data : IntraproceduralAnalysis.t) : unit =
  let init_state = AtlasState.empty analysis_data in
  let states, err_states = AtlasTransfer.run analysis_data init_state in
  let proc_name = Procdesc.get_proc_name analysis_data.proc_desc in
  Format.printf
    "@[<v2>Atlas finished procedure %a@]@."
    Procname.pp proc_name;

  let final_state =
    match states |> List.hd with
    | Some s -> AtlasState.to_string s
    | None -> ""
  in
  Format.print_string (
    "\n================\n" ^
    "[FINAL STATE] :\n" ^
    "================\n" ^
    final_state);
  Format.print_string (
    "\nERROR STATES :\n" ^
    "================\n" ^
    String.concat (
      List.map
        ~f:(fun state -> AtlasState.to_string state)
        err_states));

