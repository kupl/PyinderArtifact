(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Core
open Ast

module type PossibleState = sig
  type t [@@deriving show]

  (*
  val top_to_bottom : t -> t
  
  val set_possibleconditions : t -> t -> t

  val update_possible : t -> t -> Reference.t -> t
  *)
  val is_reachable : t -> bool

  val get_resolution : t -> Resolution.t option

  val bottom : t

  val less_or_equal : left:t -> right:t -> bool

  val join : t -> t -> t

  val widen : previous:t -> next:t -> iteration:int -> t

  (*

  val join_possible : t -> t -> t

  val widen_possible : previous:t -> next:t -> iteration:int -> t
*)  
  val forward : statement_key:int -> context:AstContext.t -> t -> statement:Statement.t -> t

  val backward : statement_key:int -> t -> statement:Statement.t -> t
end

module type PossibleFixpoint = sig
  type state

  type t = {
    preconditions: state Int.Table.t;
    postconditions: state Int.Table.t;
  }
  [@@deriving show]

  val entry : t -> state option

  val normal_exit : t -> state option

  val exit : t -> state option

  val post_info : t -> (* (Refinement.Store.t * Refinement.Store.t) *) (Resolution.t option * Resolution.t option) Int.Map.t

  (*
  val exit_possible : t -> state option
  *)
  val forward : cfg:Cfg.t -> initial:state -> Reference.t -> t

  val backward : cfg:Cfg.t -> initial:state -> t

  val equal : f:(state -> state -> bool) -> t -> t -> bool
end

module Make (State : PossibleState) : PossibleFixpoint with type state = State.t
