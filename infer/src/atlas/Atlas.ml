open! IStd

let checker (analysis_data : IntraproceduralAnalysis.t) : unit =
  let init_state = AtlasState.empty in
  let _final_state = AtlasTransfer2.run analysis_data init_state in
  let proc_name = Procdesc.get_proc_name analysis_data.proc_desc in
  Format.printf
    "@[<v2>Atlas finished procedure %a@]@."
    Procname.pp proc_name
