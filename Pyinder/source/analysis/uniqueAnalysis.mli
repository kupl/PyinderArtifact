open Ast
open Core

module type UniqueState = sig
  type t [@@deriving show, sexp]

  val bottom : t

  val less_or_equal : left:t -> right:t -> bool

  val equal : t -> t -> bool

  val join : t -> t -> t

  val widen : previous:t -> next:t -> iteration:int -> t

  val forward : statement_key:int -> t -> statement:Statement.t -> t

  val backward : statement_key:int -> t -> statement:Statement.t -> t
end


module UniqueState : sig
  
  module VarSet : sig
    type t = Reference.Set.t
  end

  type condtion_var_set =
    | True of VarSet.t
    | False of VarSet.t
  [@@deriving sexp, equal]

  type t = { 
    relation_var_map : VarSet.t Reference.Map.t;
    conditions : condtion_var_set Int.Map.t
  } [@@deriving sexp, equal]

  val get_all_relative_variables : reference:Reference.t -> t -> VarSet.t
  
  include UniqueState with type t := t
end 

module type UniqueFixpoint = sig
  type state

  type t = {
    pre_variables: state Int.Table.t;
    post_variables: state Int.Table.t;
    pre_statements: state Location.Table.t;
  } [@@deriving show, sexp, equal]

  val join : t -> t -> t

  val entry : t -> state option

  val normal_exit : t -> state option

  val exit : t -> state option

  val empty : t

  val find : t -> int -> state option

  val find_pre_statements_of_location : t -> Location.t -> (state * Location.t) option

  val forward : cfg:Cfg.t -> initial:state -> t

  val backward : cfg:Cfg.t -> initial:state -> t

  (*
  val equal : f:(state -> state -> bool) -> t -> t -> bool
*)
end


module Make (State : UniqueState) : UniqueFixpoint with type state = State.t 

module UniqueStruct : UniqueFixpoint with type state = (UniqueState.t)


(*
module Make (State : UsedefState) :sig
  type state  = State.t 
  type t [@@deriving sexp]
end

module UsedefStruct : sig 
  include module type of Make (UsedefState) 
end*)