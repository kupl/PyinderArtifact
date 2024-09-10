open Ast
open Core

module ReferenceMap = Map.Make (Reference)


module OurErrorListReadOnly = struct
  type t = Ppx_sexp_conv_lib.Sexp.t ReferenceMap.t [@@deriving sexp]

  let empty = ReferenceMap.empty
  
  let set ~key ~(data:Ppx_sexp_conv_lib.Sexp.t) t = ReferenceMap.set t ~key ~data
end