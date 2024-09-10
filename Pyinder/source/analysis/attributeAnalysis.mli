open Core
open Ast
open Ast.Util
open Expression
open Statement

(*
module LocInsensitiveExpression : sig
  include module type of struct
    include Expression
  end
end
*)
module SkipMap = LocInsensitiveExpMap

module CallInfo : sig
  type t = {
    position: int;
    default: Identifier.Set.t;
    star: bool;
    double_star: bool;
  } [@@deriving sexp, equal, compare]

  val empty : t

  val calculate : signature:t -> t -> float

  val of_arguments : Call.Argument.t list -> t

  val of_parameters : Parameter.t list -> t

  val pp : Format.formatter -> t -> unit

  val is_corresponding : signature:t -> t -> bool

  val is_more_corresponding : signature:t -> t -> bool
end

module CallSet : Set.S with type Elt.t = CallInfo.t

module AttributeStorage :
  sig
    type data_set = {
      attribute_set : Identifier.Set.t;
      call_set : CallSet.t Identifier.Map.t;
    } [@@deriving sexp, equal, compare]
    
    type t = data_set LocInsensitiveExpMap.t
    [@@deriving sexp, equal, compare]

    val empty : t
    val map : t -> f:(data_set -> 'a) -> 'a LocInsensitiveExpMap.t
    val mapi : t -> f:(key:SkipMap.Key.t -> data:data_set -> 'a) -> 'a LocInsensitiveExpMap.t
    val get_all_attributes : t -> Identifier.Set.t
    val get_single_class_param : t -> t
    val filter_keys : t -> f:(LocInsensitiveExp.t -> bool) -> t
    val filter_higher_items : ?num_item:int -> t -> t
    val filter_single_class_param : class_param:string -> t -> t
    val get_reference_list : t -> Reference.t list
    val pp_identifier_set : Format.formatter -> Identifier.Set.t -> unit
    val pp_data_set : Format.formatter -> data_set -> unit
    val pp :
      Format.formatter -> t -> unit
    val add_attribute :
      Expression.t ->
      Identifier.Set.Elt.t ->
      t ->
      t
    val add_prefix : t -> prefix:Reference.t -> t
    val filter_by_prefix : t -> prefix:Reference.t -> t
    val filter_class_var : t -> prefix:Reference.t -> t
    val join : t -> t -> t
  end
val forward_expression_list :
  (AttributeStorage.t * String.Set.t SkipMap.t) ->
  exp_list:expression Node.t list ->
    (AttributeStorage.t * String.Set.t SkipMap.t)
val forward_expression :
  ?is_assign:bool ->
  expression:expression Node.t ->
  (AttributeStorage.t * String.Set.t SkipMap.t) ->
    (AttributeStorage.t * String.Set.t SkipMap.t)
val forward_statement :
(AttributeStorage.t * String.Set.t SkipMap.t) ->
    statement:statement Node.t ->
      (AttributeStorage.t * String.Set.t SkipMap.t)
