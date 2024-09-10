open Core

module OurCallGraph : sig
  type t = {
    call_graph : CallGraph.WholeProgramCallGraph.t;
    define_call_graphs : CallGraph.DefineCallGraphSharedMemory.t;
  }

  val create : unit -> t

  val find : t -> Target.t -> Target.t list option

  val find_callee_locations : t -> Target.t -> Target.t -> Ast.Location.t list

  val create_callgraph : CallGraph.WholeProgramCallGraph.t -> CallGraph.DefineCallGraphSharedMemory.t -> t

  val pp : Format.formatter -> t -> unit
end

val our_callgraph : OurCallGraph.t ref