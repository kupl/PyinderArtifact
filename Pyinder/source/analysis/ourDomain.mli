(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

 open Ast
(*open Usedef*)
open Core
open AttributeAnalysis

val on_any : bool ref
val on_dataflow : bool ref
val on_class_var : bool ref
val on_attribute : bool ref
val type_sensitive : bool ref
val ignore_error : bool ref
val baseline : bool ref

val debug : bool ref

val skip_reference_map : (Type.t Reference.Map.t) ref

module ReferenceHash : sig
    type key = Ast.Reference.t
    type ('a, 'b) hashtbl = ('a, 'b) Core_kernel__.Hashtbl.t
    type 'b t = (key, 'b) hashtbl
    val sexp_of_t :
      ('b -> Ppx_sexp_conv_lib.Sexp.t) -> 'b t -> Ppx_sexp_conv_lib.Sexp.t
    type ('a, 'b) t_ = 'b t
    type 'a key_ = key
    val hashable : key Core_kernel__.Hashtbl_intf.Hashable.t
    val invariant :
      'a Base__.Invariant_intf.inv -> 'a t Base__.Invariant_intf.inv
    val create :
      (key, 'b, unit -> 'b t)
      Core_kernel__.Hashtbl_intf.create_options_without_hashable
    val of_alist :
      (key, 'b, (key * 'b) list -> [ `Duplicate_key of key | `Ok of 'b t ])
      Core_kernel__.Hashtbl_intf.create_options_without_hashable
    val of_alist_report_all_dups :
      (key, 'b,
       (key * 'b) list -> [ `Duplicate_keys of key list | `Ok of 'b t ])
      Core_kernel__.Hashtbl_intf.create_options_without_hashable
    val of_alist_or_error :
      (key, 'b, (key * 'b) list -> 'b t Base__.Or_error.t)
      Core_kernel__.Hashtbl_intf.create_options_without_hashable
    val of_alist_exn :
      (key, 'b, (key * 'b) list -> 'b t)
      Core_kernel__.Hashtbl_intf.create_options_without_hashable
    val of_alist_multi :
      (key, 'b list, (key * 'b) list -> 'b list t)
      Core_kernel__.Hashtbl_intf.create_options_without_hashable
    val create_mapped :
      (key, 'b,
       get_key:('r -> key) ->
       get_data:('r -> 'b) ->
       'r list -> [ `Duplicate_keys of key list | `Ok of 'b t ])
      Core_kernel__.Hashtbl_intf.create_options_without_hashable
    val create_with_key :
      (key, 'r,
       get_key:('r -> key) ->
       'r list -> [ `Duplicate_keys of key list | `Ok of 'r t ])
      Core_kernel__.Hashtbl_intf.create_options_without_hashable
    val create_with_key_or_error :
      (key, 'r, get_key:('r -> key) -> 'r list -> 'r t Base__.Or_error.t)
      Core_kernel__.Hashtbl_intf.create_options_without_hashable
    val create_with_key_exn :
      (key, 'r, get_key:('r -> key) -> 'r list -> 'r t)
      Core_kernel__.Hashtbl_intf.create_options_without_hashable
    val group :
      (key, 'b,
       get_key:('r -> key) ->
       get_data:('r -> 'b) -> combine:('b -> 'b -> 'b) -> 'r list -> 'b t)
      Core_kernel__.Hashtbl_intf.create_options_without_hashable
    val sexp_of_key : 'a t -> key -> Base__.Sexp.t
    val clear : 'a t -> unit
    val copy : 'b t -> 'b t
    val fold : 'b t -> init:'c -> f:(key:key -> data:'b -> 'c -> 'c) -> 'c
    val iter_keys : 'a t -> f:(key -> unit) -> unit
    val iter : 'b t -> f:('b -> unit) -> unit
    val iteri : 'b t -> f:(key:key -> data:'b -> unit) -> unit
    val existsi : 'b t -> f:(key:key -> data:'b -> bool) -> bool
    val exists : 'b t -> f:('b -> bool) -> bool
    val for_alli : 'b t -> f:(key:key -> data:'b -> bool) -> bool
    val for_all : 'b t -> f:('b -> bool) -> bool
    val counti : 'b t -> f:(key:key -> data:'b -> bool) -> int
    val count : 'b t -> f:('b -> bool) -> int
    val length : 'a t -> int
    val is_empty : 'a t -> bool
    val mem : 'a t -> key -> bool
    val remove : 'a t -> key -> unit
    val choose : 'b t -> (key * 'b) option
    val choose_exn : 'b t -> key * 'b
    val set : 'b t -> key:key -> data:'b -> unit
    val add : 'b t -> key:key -> data:'b -> [ `Duplicate | `Ok ]
    val add_exn : 'b t -> key:key -> data:'b -> unit
    val change : 'b t -> key -> f:('b option -> 'b option) -> unit
    val update : 'b t -> key -> f:('b option -> 'b) -> unit
    val map : 'b t -> f:('b -> 'c) -> 'c t
    val mapi : 'b t -> f:(key:key -> data:'b -> 'c) -> 'c t
    val filter_map : 'b t -> f:('b -> 'c option) -> 'c t
    val filter_mapi : 'b t -> f:(key:key -> data:'b -> 'c option) -> 'c t
    val filter_keys : 'b t -> f:(key -> bool) -> 'b t
    val filter : 'b t -> f:('b -> bool) -> 'b t
    val filteri : 'b t -> f:(key:key -> data:'b -> bool) -> 'b t
    val partition_map :
      'b t -> f:('b -> ('c, 'd) Base__.Either.t) -> 'c t * 'd t
    val partition_mapi :
      'b t ->
      f:(key:key -> data:'b -> ('c, 'd) Base__.Either.t) -> 'c t * 'd t
    val partition_tf : 'b t -> f:('b -> bool) -> 'b t * 'b t
    val partitioni_tf : 'b t -> f:(key:key -> data:'b -> bool) -> 'b t * 'b t
    val find_or_add : 'b t -> key -> default:(unit -> 'b) -> 'b
    val findi_or_add : 'b t -> key -> default:(key -> 'b) -> 'b
    val find : 'b t -> key -> 'b option
    val find_exn : 'b t -> key -> 'b
    val find_and_call :
      'b t -> key -> if_found:('b -> 'c) -> if_not_found:(key -> 'c) -> 'c
    val find_and_call1 :
      'b t ->
      key ->
      a:'d ->
      if_found:('b -> 'd -> 'c) -> if_not_found:(key -> 'd -> 'c) -> 'c
    val find_and_call2 :
      'b t ->
      key ->
      a:'d ->
      b:'e ->
      if_found:('b -> 'd -> 'e -> 'c) ->
      if_not_found:(key -> 'd -> 'e -> 'c) -> 'c
    val findi_and_call :
      'b t ->
      key ->
      if_found:(key:key -> data:'b -> 'c) -> if_not_found:(key -> 'c) -> 'c
    val findi_and_call1 :
      'b t ->
      key ->
      a:'d ->
      if_found:(key:key -> data:'b -> 'd -> 'c) ->
      if_not_found:(key -> 'd -> 'c) -> 'c
    val findi_and_call2 :
      'b t ->
      key ->
      a:'d ->
      b:'e ->
      if_found:(key:key -> data:'b -> 'd -> 'e -> 'c) ->
      if_not_found:(key -> 'd -> 'e -> 'c) -> 'c
    val find_and_remove : 'b t -> key -> 'b option
    val merge :
      'a t ->
      'b t ->
      f:(key:key ->
         [ `Both of 'a * 'b | `Left of 'a | `Right of 'b ] -> 'c option) ->
      'c t
    val merge_into :
      src:'a t ->
      dst:'b t ->
      f:(key:key ->
         'a -> 'b option -> 'b Base__.Hashtbl_intf.Merge_into_action.t) ->
      unit
    val keys : 'a t -> key list
    val data : 'b t -> 'b list
    val filter_keys_inplace : 'a t -> f:(key -> bool) -> unit
    val filter_inplace : 'b t -> f:('b -> bool) -> unit
    val filteri_inplace : 'b t -> f:(key:key -> data:'b -> bool) -> unit
    val map_inplace : 'b t -> f:('b -> 'b) -> unit
    val mapi_inplace : 'b t -> f:(key:key -> data:'b -> 'b) -> unit
    val filter_map_inplace : 'b t -> f:('b -> 'b option) -> unit
    val filter_mapi_inplace :
      'b t -> f:(key:key -> data:'b -> 'b option) -> unit
    val equal : ('b -> 'b -> bool) -> 'b t -> 'b t -> bool
    val similar : ('b1 -> 'b2 -> bool) -> 'b1 t -> 'b2 t -> bool
    val to_alist : 'b t -> (key * 'b) list
    val validate :
      name:(key -> string) ->
      'b Base__.Validate.check -> 'b t Base__.Validate.check
    val incr : ?by:int -> ?remove_if_zero:bool -> int t -> key -> unit
    val decr : ?by:int -> ?remove_if_zero:bool -> int t -> key -> unit
    val add_multi : 'b list t -> key:key -> data:'b -> unit
    val remove_multi : 'a list t -> key -> unit
    val find_multi : 'b list t -> key -> 'b list
    module Provide_of_sexp = Ast.Reference.Table.Provide_of_sexp
    module Provide_bin_io = Ast.Reference.Table.Provide_bin_io
    val t_of_sexp :
      (Ppx_sexp_conv_lib.Sexp.t -> 'a__002_) ->
      Ppx_sexp_conv_lib.Sexp.t -> 'a__002_ t
end

module TypeFromFuncs : sig
  type t = Reference.Set.t Type.Map.t

  val empty : t

  val set : t -> key:Type.t -> data:Reference.Set.t -> t

  val fold : t -> init:'a -> f:(key:Type.t -> data:Reference.Set.t -> 'a -> 'a) -> 'a

  val existsi : t -> f:(key:Type.t -> data:Reference.Set.t -> bool) -> bool

  val get_type : type_join:(Type.t -> Type.t -> Type.t) -> t -> Type.t option

  val get_all_callees : t -> Reference.Set.t

  val get_callees : typ:Type.t -> less_or_equal:(left:Type.t -> right:Type.t -> bool) -> t -> Reference.Set.t

  val join : t -> t -> t
end

module ReferenceSet = Reference.Set

module ReferenceMap : sig
  include Map.S with type Key.t = Reference.t

  val join : data_join:('a -> 'a -> 'a) -> equal:('a -> 'a -> bool) -> 'a t -> 'a t -> 'a t

  val join_var_from_funcs : TypeFromFuncs.t t -> TypeFromFuncs.t t -> TypeFromFuncs.t t

  val diff : Type.t t -> Type.t t -> ReferenceSet.t
end

module TypeSet : Set.S with type Elt.t = Type.t

module VarTypeSet : sig
  type t = TypeSet.t Reference.Map.t [@@deriving sexp, compare, equal]

  val empty : t

  val pp : Format.formatter -> t -> unit

  val join : t -> t -> t

  val fold : t -> init:'a -> f:(key:Reference.t -> data:TypeSet.t -> 'a -> 'a) -> 'a

  val set : t -> key:Reference.t -> data:TypeSet.t -> t
end


module IdentifierMap : Map.S with type Key.t = Identifier.t

module CallerSet = ReferenceSet
module ClassMap = ReferenceMap
module FunctionMap = ReferenceMap

module ClassHash = ReferenceHash
module FunctionHash = ReferenceHash

module AttrsSet : Set.S with type Elt.t = String.t


module StubInfo : sig
  type info = {
    attribute_set: AttrsSet.t;
    call_set: AttributeAnalysis.CallSet.t Identifier.Map.t;
  }

  type t = info Identifier.Map.t

  val empty : t

  val pp : Format.formatter -> t -> unit

  val is_empty : t -> bool

  val create : unit -> t
end

module ClassAttributes: sig
  type t = {
    attributes: AttrsSet.t;
    properties: AttrsSet.t;
    methods: AttributeAnalysis.CallSet.t Identifier.Map.t;
  }

  val get_class_property : t -> AttrsSet.t

  val is_used_attr : t -> string -> bool

  val str_attributes : unit -> t
  (*
  val is_subset_with_total_attributes : t -> AttrsSet.t -> bool
  *)
end

module ClassSummary: sig
  type t = {
    class_var_type: TypeFromFuncs.t ReferenceMap.t;
    temp_class_var_type: TypeFromFuncs.t ReferenceMap.t;
    join_temp_class_var_type: TypeFromFuncs.t ReferenceMap.t;
    seen_var_type: Reference.Set.t ReferenceMap.t;
    class_attributes: ClassAttributes.t;
    usage_attributes: AttributeStorage.t;
    change_set: ReferenceSet.t;
    (* should_analysis: bool; *)
  }

  val join : type_join:(Type.t -> Type.t -> Type.t) -> t -> t -> t

  val get_class_var_type : t -> TypeFromFuncs.t ReferenceMap.t

  val get_temp_class_var_type : t -> TypeFromFuncs.t ReferenceMap.t

  val get_properties : t -> AttrsSet.t

  val pp_class_var_type : Format.formatter -> t -> unit

  val pp : Format.formatter -> t -> unit
end

module type ClassTable = sig
  type t = ClassSummary.t ClassHash.t 
end

module ClassTable: sig
  type t = ClassSummary.t ClassHash.t 

  val find_default : t -> Reference.t -> ClassSummary.t

  val add : class_name:Reference.t -> data:'a -> f:(ClassSummary.t -> 'a -> ClassSummary.t) -> t -> unit

  val get : class_name:Reference.t -> f:(ClassSummary.t -> 'a) -> t -> 'a

  val get_class_var_type : t -> Reference.t -> TypeFromFuncs.t ReferenceMap.t

  val get_temp_class_var_type : t -> Reference.t -> TypeFromFuncs.t ReferenceMap.t

  val pp : Format.formatter -> t -> unit
end

module type ArgTypes = sig
  type t = Type.t IdentifierMap.t
end


module ArgTypes : sig
  type t = Type.t IdentifierMap.t [@@deriving compare, sexp]

  val empty : t

  val map : f:(Type.t -> Type.t) -> t -> t

  val is_empty : t -> bool

  val filter_keys : t -> f:(string -> bool) -> t

  val mem : t -> string -> bool

  val add_arg_type : join:(Type.t -> Type.t -> Type.t) -> t -> string -> Type.t -> t

  val join: type_join:(Type.t -> Type.t -> Type.t) -> t -> t -> t

  val less_or_equal: less_or_equal:(Type.t -> Type.t -> bool) -> t -> t-> bool

  val pp : Format.formatter -> t -> unit

  val get_type : t -> Identifier.t -> Type.t

  val make_arg_types : (Identifier.t * Type.t) list -> t
end

module ArgTypesKey : sig
  type t = Reference.t * (Identifier.t * Type.t) list [@@deriving compare, sexp, hash, show]

  val to_key : Reference.t -> ArgTypes.t -> t

  val from_key : t -> Reference.t * ArgTypes.t
end


module Signatures : sig
  type return_info = {
    return_var_type: Type.t ReferenceMap.t; (* Return 했을 때의 parameter 정보 *)
    return_type: Type.t; (* Function의 Return Type *)
    should_analysis: bool;
    caller_analysis: bool;
    caller_set : ReferenceSet.t;
  } [@@deriving sexp, equal]

  module ArgTypesMap : Map.S with type Key.t = ArgTypes.t

  type t = return_info ArgTypesMap.t (* Argumets의 Type*)
  [@@deriving sexp, equal]

  val yojson_of_t : t -> Yojson.Safe.json

  val get_return_var_type : t -> ArgTypes.t -> Type.t ReferenceMap.t

  val set_return_var_type : t -> ArgTypes.t -> Type.t ReferenceMap.t -> t
end

module type FunctionSummary = sig
  type t = {
    signatures: Signatures.t;
    (* arg_types: ArgTypes.t; (* Argumets의 Input Type *)
    arg_annotation: ArgTypes.t; (* Argument Annotation *)
    return_var_type: Type.t ReferenceMap.t; (* Return 했을 때의 parameter 정보 *)
    return_type: Type.t; (* Function의 Return Type *) *)
    callers: CallerSet.t;
    return_annotation: Type.t;
    usage_attributes : AttributeStorage.t;
    unique_analysis : UniqueAnalysis.UniqueStruct.t;
    usedef_defined: VarTypeSet.t;
    call_chain: CallChain.t;
    unknown_decorator : bool;
    (*usedef_tables: UsedefStruct.t option;*)
  }
(*   type t = {
    arg_types: ArgTypes.t; (* Argumets의 Type*)
    arg_annotation : ArgTypes.t;
    return_var_type: Type.t ReferenceMap.t; (* Return 했을 때의 parameter 정보 *)
    return_type: Type.t; (* Function의 Return Type *)
    callers: CallerSet.t;
    usage_attributes : AttributeStorage.t;
    (*usedef_tables: UsedefStruct.t option;*)
  } *)

  val add_return_var_type : t -> ArgTypes.t -> Reference.t -> Type.t -> t
end

module ExpressionMap : Map.S with type Key.t = Expression.t

module FunctionSummary : sig
(*   type t = {
    arg_types : ArgTypes.t;
    arg_annotation : ArgTypes.t;
    return_var_type : Type.t ReferenceMap.t;
    return_type : Type.t;
    callers: CallerSet.t;
    usage_attributes : AttributeStorage.t;
    (*usedef_tables : UsedefStruct.t option;*)
  } *)
  
  type t = {
    signatures: Signatures.t;
    preprocess: Type.t ExpressionMap.t;
    (* arg_types: ArgTypes.t; (* Argumets의 Input Type *)
    arg_annotation: ArgTypes.t; (* Argument Annotation *)
    return_var_type: Type.t ReferenceMap.t; (* Return 했을 때의 parameter 정보 *)
    return_type: Type.t; (* Function의 Return Type *) *)
    param_varset: Reference.Set.t Identifier.Map.t;
    callers: CallerSet.t;
    return_annotation: Type.t;
    usage_attributes : AttributeStorage.t;
    unique_analysis : UniqueAnalysis.UniqueStruct.t;
    usedef_defined: VarTypeSet.t;
    call_chain: CallChain.t;
    unknown_decorator : bool;
    (*usedef_tables: UsedefStruct.t option;*)
  }

  val empty : t

  val get_signatures : t -> Type.t Signatures.ArgTypesMap.t

  val get_call_chain : t -> CallChain.t

  val add_return_var_type : t -> ArgTypes.t -> Reference.t -> Type.t -> t
end

module type FunctionTable = sig
  type t = FunctionSummary.t FunctionHash.t
end

module FunctionTable : sig
  type t = FunctionSummary.t FunctionHash.t

  val get_return_type : type_join:(Type.t -> Type.t -> Type.t) -> less_or_equal:(left:Type.t -> right:Type.t -> bool) -> ?property:bool -> t -> Reference.t -> ArgTypes.t -> Type.t
end

module type OurSummary = sig
  type t = {
    class_table : ClassTable.t;
    function_table : FunctionTable.t;
    stub_info : StubInfo.t;
    recheck_info: (Type.t Reference.Map.t) Reference.Map.t;
    errors: Ppx_sexp_conv_lib.Sexp.t;
  }
end

module OurSummary : sig
  type t = {
    class_table : ClassTable.t;
    function_table : FunctionTable.t;
    stub_info : StubInfo.t;
    recheck_info: (Type.t Reference.Map.t) Reference.Map.t;
    errors: Ppx_sexp_conv_lib.Sexp.t;
  }
  [@@deriving equal, sexp]

  val empty : ?size:int -> unit -> t

  val set_errors : t -> Ppx_sexp_conv_lib.Sexp.t -> t

  val get_errors : t -> Ppx_sexp_conv_lib.Sexp.t

  val set_recheck_info: t -> (Type.t Reference.Map.t) Reference.Map.t -> t

  val get_recheck_info: t -> (Type.t Reference.Map.t) Reference.Map.t

  val set_skip_reference_map : define_name:Reference.t -> t -> unit

  val update_check_preprocess : define:Reference.t -> type_join:(Type.t -> Type.t -> Type.t) -> prev:t -> t -> unit

  val update_default_value : prev:t -> t -> unit

  val update : type_join:(Type.t -> Type.t -> Type.t) -> prev:t -> t -> unit

  val join : type_join:(Type.t -> Type.t -> Type.t) -> t -> t -> unit

  (*val join_return_type : type_join:(Type.t -> Type.t -> Type.t) -> t -> Reference.t -> Type.t -> t*)

  val pp_class : Format.formatter -> t -> unit

  val pp_func : Format.formatter -> t -> unit

  val pp : Format.formatter -> t -> unit

  (*val copy : t -> t*)

  val find_signature : t -> Reference.t -> ArgTypes.t -> (* Signatures.t *) Signatures.return_info option

  val filter_seen_var : class_name:Reference.t -> func_name:Reference.t -> var_set:Reference.Set.t -> t -> Reference.Set.t

  val add_param_varset : t -> Reference.t -> Reference.Set.t Identifier.Map.t -> unit

  val get_param_varset : t -> Reference.t -> Reference.Set.t Identifier.Map.t

  val add_new_signature : join:(Type.t -> Type.t -> Type.t) -> ?caller_name:Reference.t -> t -> Reference.t -> ArgTypes.t -> unit

(*   val add_arg_types : join:(Type.t -> Type.t -> Type.t) -> t -> Reference.t -> (Identifier.t * Type.t) list -> t *)

  val add_usage_attributes : ?class_name:Reference.t -> ?class_var:string -> t -> Reference.t -> AttributeStorage.t -> unit

  val add_caller : t -> caller:Reference.t -> Reference.t -> unit

  val add_return_annotation : t -> Reference.t -> Type.t -> unit

  val add_return_type : type_join:(Type.t -> Type.t -> Type.t) -> t -> Reference.t -> ArgTypes.t -> Type.t -> unit

(*   val set_arg_types : t -> Reference.t -> ArgTypes.t -> t

  val set_arg_annotation : t -> Reference.t -> ArgTypes.t -> t *)

  val set_return_var_type : t -> Reference.t -> ArgTypes.t -> Type.t ReferenceMap.t -> unit

  val set_return_type : t -> Reference.t -> ArgTypes.t -> Type.t -> unit

  val set_preprocess : t -> Reference.t -> Expression.t -> Type.t -> unit

  val set_callers : t -> Reference.t -> CallerSet.t -> unit

  val set_usage_attributes : t -> Reference.t -> AttributeStorage.t -> unit

  val set_unique_analysis : t -> Reference.t -> UniqueAnalysis.UniqueStruct.t -> unit

  val set_usedef_defined : t -> Reference.t -> VarTypeSet.t -> unit

  val set_call_chain : t -> Reference.t -> CallChain.t -> unit

  val set_unknown_decorator : t -> Reference.t -> unit
  (*
  val set_usedef_tables : t -> Reference.t -> UsedefStruct.t option -> t
*)
  val get_class_vars : t -> Reference.Set.t Reference.Map.t

  val get_class_table : t -> ClassTable.t

  val get_function_table : t -> FunctionTable.t

  (*
  val get_usedef_tables : t -> Reference.t -> UsedefStruct.t option
*)
(*   val get_arg_types : t -> Reference.t -> ArgTypes.t

  val get_arg_annotation : t -> Reference.t -> ArgTypes.t *)

  val get_return_var_type : t -> Reference.t -> ArgTypes.t -> Type.t ReferenceMap.t

  val get_return_type : type_join:(Type.t -> Type.t -> Type.t) -> less_or_equal:(left:Type.t -> right:Type.t -> bool) -> t -> Reference.t -> ArgTypes.t -> Type.t

  val get_callers : t -> Reference.t -> CallerSet.t

  val get_usage_attributes_from_func : t -> Reference.t -> AttributeStorage.t

  val get_preprocess : t -> Reference.t -> Type.t ExpressionMap.t

  val get_unique_analysis : t -> Reference.t -> UniqueAnalysis.UniqueStruct.t

  val get_usedef_defined : t -> Reference.t -> VarTypeSet.t

  val get_unknown_decorator : t -> Reference.t -> bool

  val get_callable : join:(Type.t -> Type.t -> Type.t) -> less_or_equal:(left:Type.t -> right:Type.t -> bool) -> successors:(string -> string list) -> t -> ArgTypes.t -> Type.Callable.t -> Type.Callable.t

  val get_callable_return_type : type_join:(Type.t -> Type.t -> Type.t) -> successors:(string -> string list) -> t -> ArgTypes.t -> Type.Callable.t -> Type.t
  
  val add_class_attribute : t -> Reference.t -> string -> unit

  val add_class_property : t -> Reference.t -> string -> unit

  val add_class_method : t -> Reference.t -> AttributeAnalysis.CallInfo.t -> string -> unit

  val set_class_summary : t -> Reference.t -> ClassSummary.t -> unit

  val update_unseen_temp_class_var_type : type_join:(Type.t -> Type.t -> Type.t) -> updated_vars:Reference.Set.t Reference.Map.t -> t -> unit

  val update_unseen_temp_class_var_type_to_unknown : t -> unit

  val update_unseen_temp_class_var_type_to_var : t -> unit

  val set_all_class_var_type_to_empty : t -> unit

  val set_all_temp_class_var_type_from_join : t -> unit

  val set_all_join_temp_class_var_type_to_empty : t -> unit

  val set_class_table : t -> ClassTable.t -> t

  val set_stub_info : t -> StubInfo.t -> t

  val get_class_summary : t -> Reference.t -> ClassSummary.t

  val get_usage_attributes_from_class : t -> Reference.t -> AttributeStorage.t

  val get_analysis_arg_types : t -> Reference.t -> ArgTypes.t list

  val get_all_arg_types : type_join:(Type.t -> Type.t -> Type.t) -> t -> Reference.t -> ArgTypes.t

  val get_module_var_type : t -> Reference.t -> string -> Type.t

  val get_class_property : t -> Reference.t -> AttrsSet.t

  val check_attr : attr:string -> t -> Reference.t -> bool

  val change_analysis : t -> unit

  val end_analysis : t -> Reference.t -> ArgTypes.t -> unit

  val change_analysis_of_func : t -> Reference.t -> unit

  val change_analysis_to_false_of_func : t -> Reference.t -> unit

  val get_skip_set : t -> ReferenceSet.t

  val has_analysis : t -> bool

  val get_functions_of_class : t -> Reference.t list list

  val add_implicit_to_join : t -> Reference.t -> Reference.t -> Type.t -> unit
end

val global_summary : string

val is_func_model_exist : unit -> bool

val set_data_path : Configuration.Analysis.t -> unit

val our_model : OurSummary.t ref

val our_summary : OurSummary.t ref

val stub_info : StubInfo.t ref

val is_search_mode : string -> bool

val is_inference_mode : string -> bool

val is_last_inference_mode : string -> bool

val is_error_mode : string -> bool

val is_recheck_mode : string -> bool

val is_check_preprocess_mode : string -> bool

val is_preprocess : bool ref

val save_mode : string -> unit

val load_mode : unit -> string

val save_summary : OurSummary.t -> Reference.t -> unit

val save_global_summary : unit -> unit

val load_summary : Reference.t -> OurSummary.t

val load_global_summary : unit -> OurSummary.t

val load_global_summary_cache : unit -> unit

val load_all_summary_test : unit -> unit

(* val load_all_summary : ?use_cache:bool -> type_join:(Type.t -> Type.t -> Type.t) -> skip_set:Reference.Set.t -> OurSummary.t -> unit
 *)
val load_specific_file : unit -> unit

val select_our_model : Reference.t -> OurSummary.t

val is_first : bool ref

val all_defines : Reference.t list ref

(* val deubg : bool ref *)

(* module OurDomainReadOnly : sig

  type t

  val create : OurSummary.t -> t
end *)