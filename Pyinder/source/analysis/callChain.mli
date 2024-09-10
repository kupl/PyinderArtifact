open Ast

type t = Reference.t Location.Map.t [@@deriving compare, sexp, equal]

val empty : t

val length : t -> int

val join : t -> t -> t

val set_callee : location:Location.t -> callee:Reference.t -> t -> t

val get_callee : location:Location.t -> t -> Reference.t option

val get_callee_chain : t -> Reference.t list
