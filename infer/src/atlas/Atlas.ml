open! IStd

let checker (analysis_data : IntraproceduralAnalysis.t) : unit =
  let init_state = AtlasState.empty analysis_data in
  let final_states, err_states = AtlasTransfer.run analysis_data init_state in
  let proc_name = Procdesc.get_proc_name analysis_data.proc_desc in
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
        err_states));

