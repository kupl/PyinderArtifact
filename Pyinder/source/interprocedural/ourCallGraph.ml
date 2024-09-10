open Core

module DefineCall = CallGraph.DefineCallGraphSharedMemory

module OurCallGraph = struct
  type t = {
    call_graph : CallGraph.WholeProgramCallGraph.t;
    define_call_graphs : DefineCall.t;
  }

  let create () = {
    call_graph = CallGraph.WholeProgramCallGraph.empty;
    define_call_graphs = DefineCall.empty;
  }

  let find { call_graph; _ } source =
    Target.Map.find call_graph source

  let find_callee_locations { define_call_graphs; _ } caller callee =
    let opt = DefineCall.get define_call_graphs ~callable:caller in
    match opt with 
    | Some define_call ->
      let locations = CallGraph.DefineCallGraph.get_keys_of_target define_call callee in
      locations
    | None -> []


  let create_callgraph call_graph define_call_graphs =
    { call_graph; define_call_graphs; }

  let pp formatter { call_graph; _ } =
    Format.fprintf formatter "%a" CallGraph.WholeProgramCallGraph.pp call_graph;
end

let our_callgraph = ref (OurCallGraph.create ());;