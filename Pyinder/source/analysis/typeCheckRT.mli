(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open TypeCheckUtil
open Ast
open Expression
open Statement

module Error = AnalysisError

val unpack_callable_and_self_argument
  :  signature_select:
       (arguments:AttributeResolution.Argument.t list ->
       callable:Type.Callable.t ->
       self_argument:Type.t option ->
       SignatureSelectionTypes.instantiated_return_annotation) ->
  global_resolution:GlobalResolution.t ->
  Type.t ->
  TypeOperation.callable_and_self_argument option

module type RTSignature = sig
  type t =
  | Unreachable
  | Value of Resolution.t
  [@@deriving eq]


  val create : resolution:Resolution.t -> t

  val unreachable : t

  val resolution : t -> Resolution.t option

  val initial : resolution:Resolution.t -> t

  val forward_statement : resolution:Resolution.t -> at_resolution:Resolution.t option -> statement:statement Node.t -> t * Error.t list

  val forward_statement_first : resolution:Resolution.t -> at_resolution:Resolution.t option -> statement:statement Node.t -> t * Error.t list

  val parse_and_check_annotation
    :  ?bind_variables:bool ->
    resolution:Resolution.t ->
    Expression.t ->
    Error.t list * Type.t

  include PossibleFixpoint.PossibleState with type t := t
end

module TypeCheckRT (Context : OurContext) : RTSignature
