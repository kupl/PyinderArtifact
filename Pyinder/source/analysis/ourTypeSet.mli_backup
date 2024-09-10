(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)


open Ast
open Ast.Util
open AttributeAnalysis
open OurDomain
open Refinement

module ClassTableResolution : sig
  include ClassTable

  val join_with_merge_class_var_type : type_join:(Type.t -> Type.t -> Type.t) -> t -> Reference.t -> string -> Refinement.Store.t -> t
end

module ArgTypesResolution : sig
  include ArgTypes

  val import_from_resolution : join:(Type.t -> Type.t -> Type.t) -> Resolution.t -> ArgTypes.t

  val export_to_resolution : t -> Resolution.t -> Resolution.t

  val join_to_resolution : join:(Type.t -> Type.t -> Type.t) -> t -> Resolution.t -> Resolution.t

  (* val callable_to_arg_types : 
    self_argument:Type.t option -> 
    arguments:AttributeResolution.Argument.t list ->
    Type.Callable.t ->
    ArgTypes.t *)
    
end

module FunctionTableResolution : sig
  include FunctionTable
end

module OurSummaryResolution : sig
  include OurSummary

  type t = OurSummary.t

  val store_to_return_var_type : ?class_param:string -> t -> Reference.t -> ArgTypes.t -> Store.t -> t

  val get_type_of_class_attribute : t -> Reference.t -> string -> Type.t

  val get_self_attributes_tree : t -> Reference.t -> Unit.t Identifier.Map.Tree.t

  val add_parent_attributes : t -> AttributeStorage.t -> Reference.t -> string -> t
(*
  val search_suspicious_variable : t -> store_combine:(Store.t -> Unit.t Reference.Map.t) -> Reference.t -> Refinement.Unit.t Reference.Map.t list
*)
  val find_class_of_attributes : successors:(string -> string list) -> t -> Reference.t -> AttributeStorage.t -> Reference.t LocInsensitiveExpMap.t 
end

