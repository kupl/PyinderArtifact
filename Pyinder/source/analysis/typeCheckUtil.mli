(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Ast
open Statement

module Error = AnalysisError

module LocalErrorMap : sig
  type t

  val empty : unit -> t

  val set : statement_key:int -> errors:Error.t list -> t -> unit

  val append : statement_key:int -> error:Error.t -> t -> unit

  val all_errors : t -> Error.t list
end

module type Context = sig
  val qualifier : Reference.t

  val debug : bool

  val constraint_solving_style : Configuration.Analysis.constraint_solving_style

  val define : Define.t Node.t

  (* Where to store local annotations during the fixpoint. `None` discards them. *)
  val resolution_fixpoint : LocalAnnotationMap.t option

  (* Where to store errors found during the fixpoint. `None` discards them. *)
  val error_map : LocalErrorMap.t option

  module Builder : Callgraph.Builder
end

module type OurContext = sig
  val qualifier : Reference.t

  val debug : bool

  val constraint_solving_style : Configuration.Analysis.constraint_solving_style

  val define : Define.t Node.t

  (* Where to store local annotations during the fixpoint. `None` discards them. *)
  val resolution_fixpoint : LocalAnnotationMap.t option

  (* Where to store errors found during the fixpoint. `None` discards them. *)
  val error_map : LocalErrorMap.t option

  val our_summary : OurDomain.OurSummary.t ref

  val entry_arg_types : OurDomain.ArgTypes.t ref

  val ignore_lines : Ignore.t list

  module Builder : Callgraph.Builder
end

(*
module type OurSignature = sig
  type t =
  | Unreachable
  | Value of Resolution.t
  [@@deriving eq]

  val create : resolution:Resolution.t -> t

  val unreachable : t

  val resolution : t -> Resolution.t option

  val initial : resolution:Resolution.t -> t

  val forward_statement : resolution:Resolution.t -> statement:statement Node.t -> t * Error.t list

  val parse_and_check_annotation
    :  ?bind_variables:bool ->
    resolution:Resolution.t ->
    Expression.t ->
    Error.t list * Type.t

  include PossibleFixpoint.PossibleState with type t := t
end
*)