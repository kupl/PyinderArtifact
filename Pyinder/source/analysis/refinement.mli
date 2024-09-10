(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Ast

module Unit : sig
  type t [@@deriving sexp, eq, show]

  val empty : t

  val top : t

  val create : Annotation.t -> t

  val create_all : Annotation.t option -> t Identifier.Map.Tree.t -> t

  val create_mutable : Type.t -> t

  val base : t -> Annotation.t option

  val attributes : t -> t Identifier.Map.Tree.t

  val set_base : t -> base:Annotation.t -> t

  val set_annotation
    :  ?wipe_subtree:bool ->
    attribute_path:Reference.t ->
    annotation:Annotation.t ->
    t ->
    t

  val get_annotation : attribute_path:Reference.t -> t -> Annotation.t option

  val less_or_equal : global_resolution:GlobalResolution.t -> left:t -> right:t -> bool

  val join : global_resolution:GlobalResolution.t -> t -> t -> t

  val meet : global_resolution:GlobalResolution.t -> t -> t -> t
end

module Store : sig
  type t = {
    annotations: Unit.t Reference.Map.t;
    temporary_annotations: Unit.t Reference.Map.t;
  }
  [@@deriving sexp, eq, show]

  val empty : t

  val set_temporary_annotations : t -> Unit.t Reference.Map.t -> t

  val set_annotations : t -> Unit.t Reference.Map.t -> t  

  val to_yojson : Format.formatter -> t -> unit

  val has_temporary_annotation : name:Reference.t -> t -> bool

  val has_nontemporary_annotation : name:Reference.t -> t -> bool

  val get_base : name:Reference.t -> t -> Annotation.t option

  val get_base_of_anno : name:Reference.t -> t -> Annotation.t option


  val get_attributes : name:Reference.t -> t -> Unit.t Identifier.Map.Tree.t

  val get_annotation_of_anno : name:Reference.t -> attribute_path:Reference.t -> t -> Annotation.t option

  val get_annotation_of_temp : name:Reference.t -> attribute_path:Reference.t -> t -> Annotation.t option

  val get_annotation : name:Reference.t -> attribute_path:Reference.t -> t -> Annotation.t option

  val set_base : ?temporary:bool -> name:Reference.t -> base:Annotation.t -> t -> t

  val new_as_base : ?temporary:bool -> name:Reference.t -> base:Annotation.t -> t -> t

  val set_annotation
    :  ?temporary:bool ->
    ?wipe_subtree:bool ->
    name:Reference.t ->
    attribute_path:Reference.t ->
    base:Annotation.t option ->
    annotation:Annotation.t ->
    t ->
    t

  val less_or_equal : global_resolution:GlobalResolution.t -> left:t -> right:t -> bool

  val less_or_equal_monotone : left:t -> right:t -> bool

  val meet : global_resolution:GlobalResolution.t -> t -> t -> t

  val outer_join : global_resolution:GlobalResolution.t -> t -> t -> t

  val outer_widen
    :  global_resolution:GlobalResolution.t ->
    iteration:int ->
    widening_threshold:int ->
    t ->
    t ->
    t

  val join_with_merge : global_resolution:GlobalResolution.t -> t -> t -> t

  val widen_with_merge 
  :  global_resolution:GlobalResolution.t ->
    iteration:int ->
    widening_threshold:int ->
    t ->
    t ->
    t

  val update_existing : old_store:t -> new_store:t -> t

  val update_with_filter
    :  old_store:t ->
    new_store:t ->
    filter:(Reference.t -> Annotation.t -> bool) ->
    t

  val remain_new : old_store:t -> new_store:t -> t

  val update_self : global_resolution:GlobalResolution.t -> t -> t

  val fold_map : f:(key:Reference.t -> data:Unit.t -> Unit.t Reference.Map.t -> Unit.t Reference.Map.t) -> t -> t -> t

  val update_from_top_to_unknown : t -> t

  val update_possible : global_resolution:GlobalResolution.t -> t -> t -> t

  val combine_join_with_merge : global_resolution:GlobalResolution.t -> t -> Unit.t Reference.Map.t

  val make_map_function_of_types : t -> (Annotation.t option -> 'a list option) -> (string list * 'a option) list

  val top_to_unknown : t -> t

  val add_unknown : t -> t

  val update_self_attributes_tree : global_resolution:GlobalResolution.t -> t -> Unit.t Identifier.Map.Tree.t -> Unit.t Identifier.Map.Tree.t -> Reference.t -> t
end
