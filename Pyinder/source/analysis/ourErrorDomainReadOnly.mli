open Ast
open Core

module ReferenceMap : Map.S with type Key.t = Reference.t


module OurErrorListReadOnly : sig
    type t = Ppx_sexp_conv_lib.Sexp.t ReferenceMap.t [@@deriving sexp]
  
    val empty : t

    val set : key:Reference.t -> data:Ppx_sexp_conv_lib.Sexp.t -> t -> t

end