open Ast
open Core
module OurErrorListReadOnly = OurErrorDomainReadOnly.OurErrorListReadOnly
module Error = AnalysisError

module LocationMap : Map.S with type Key.t = Location.WithModule.t

module OurErrorList : sig
    type error_with_ignore = {
        error : Error.t;
        ignore : bool
    } [@@deriving sexp]

    type t = error_with_ignore LocationMap.t [@@deriving sexp]

    val empty : t
    
    val equal : t -> t -> bool

    val set : key:Location.WithModule.t -> data:error_with_ignore -> t -> t

    val get : key:Location.WithModule.t -> t -> error_with_ignore option

    val add : join:(Type.t -> Type.t -> Type.t) -> errors:Error.t list -> ignore_lines:Ignore.t list -> t -> t

    val num : t -> int

    val inter_error: t -> t -> t

    val merge_error: t -> t -> t

    val cause_analysis : global_resolution:GlobalResolution.t -> t -> OurDomain.OurSummary.t -> t * t * (Type.t Reference.Map.t) Reference.Map.t

    (* val get_repeated_errors : t -> Reference.t list -> t *)
end

type errors = Error.t list [@@deriving sexp]

val read_only :  OurErrorList.t -> OurErrorListReadOnly.t
  
val get_errors : key:Reference.t -> OurErrorListReadOnly.t -> errors
  

val our_errors : OurErrorList.t ref