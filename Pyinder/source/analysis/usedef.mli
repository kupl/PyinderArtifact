open Ast
open Core
open OurDomain

module TypeSet : Set.S with type Elt.t = Type.t

module type UsedefState = sig
  type t [@@deriving show, sexp]

  val bottom : t

  val less_or_equal : left:t -> right:t -> bool

  val equal : t -> t -> bool

  val join : t -> t -> t

  val widen : previous:t -> next:t -> iteration:int -> t

  val get_used_before_defined : t -> TypeSet.t Reference.Map.t

  val get_defined : t -> TypeSet.t Reference.Map.t

  val get_used_after_defined : t -> TypeSet.t Reference.Map.t

  val to_vartypeset : t -> VarTypeSet.t

  val is_defined : t -> Reference.t -> bool

  val is_undefined : t -> Reference.t -> bool

  val forward : func_name:Reference.t -> statement_key:int -> post_info:(Resolution.t * Resolution.t) -> get_usedef_state_of_func:(Reference.t -> VarTypeSet.t) -> t -> statement:Statement.t -> t

  val backward : statement_key:int -> t -> statement:Statement.t -> t
end


module UsedefState : sig
  
  module VarSet : sig
    type t = Reference.Set.t
  end

  type usedef
  type t = {
    used_before_defined: TypeSet.t Reference.Map.t;
    defined: TypeSet.t Reference.Map.t;
    check_used: TypeSet.t Reference.Map.t;
    used_after_defined: TypeSet.t Reference.Map.t;
    total: TypeSet.t Reference.Map.t;
    usedef_table: usedef Reference.Map.t;
  } 

  val create : t

  include UsedefState with type t := t
end 



module type UsedefFixpoint = sig
  type state

  type t = {
    usedef_tables: state Int.Table.t (* state Int.Table.t *)
  }
  [@@deriving show, sexp, equal]

  val entry : t -> state option

  val normal_exit : t -> state option

  val exit : t -> state option

  val empty : t

  val get_usedef_tables : t -> state Int.Table.t

  val find : t -> int -> state option

  val find_usedef_table_of_location : t -> Cfg.t -> Location.t -> state option

  val forward : func_name:Reference.t -> cfg:Cfg.t -> post_info:(Resolution.t option * Resolution.t option) Int.Map.t -> initial:state -> 
    get_usedef_state_of_func:(Reference.t -> VarTypeSet.t) -> t

  val forward_for_exception : cfg:Cfg.t -> post_info:(Resolution.t option * Resolution.t option) Int.Map.t -> initial:state -> 
    get_usedef_state_of_func:(Reference.t -> VarTypeSet.t) -> t

  val backward : cfg:Cfg.t -> initial:state -> t

  (*
  val equal : f:(state -> state -> bool) -> t -> t -> bool
*)
end


module Make (State : UsedefState) : UsedefFixpoint with type state = State.t 

module UsedefStruct : UsedefFixpoint with type state = (UsedefState.t)


(*
module Make (State : UsedefState) :sig
  type state  = State.t 
  type t [@@deriving sexp]
end

module UsedefStruct : sig 
  include module type of Make (UsedefState) 
end*)