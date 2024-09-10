open Ast

module ReferenceHash = struct
  include Reference.Table
end
(* open Core
open Ast

open AttributeAnalysis
(*
open Usedef
exception NotEqualException;;
*)
module ReferenceSet = Reference.Set

module StringSet = Set.Make (String)
module AttrsSet = StringSet

module ReferenceHash = struct
  include Hashtbl.Make (Reference)

  let empty = create ()
  let join_type ~type_join left right =
    merge_into ~src:left ~dst:right ~f:(fun ~key:_ src dst ->
      match dst with
      | Some v -> Set_to (type_join src v)
      | _ -> Set_to src
    )
    (* merge left right ~f:(fun ~key:_ data ->
      match data with
      | `Both (left, right) -> if Type.equal left right then Some left else (
        try
          Some (type_join left right)
        with
        | (* ClassHierarchy.Untracked *) _ -> Log.dump "%a\n%a\n" Type.pp left Type.pp right; Some (Type.union_join left right)
      )
      | `Left data | `Right data -> Some data
    ) *)

  let join ~data_join ~equal left right =
    (* let timer = Timer.start () in
    let t_list = ref [] in *)
    merge_into ~src:left ~dst:right ~f:(fun ~key:_ src dst ->
      match dst with 
      | Some v -> if equal src v then Set_to v else Set_to (data_join src v)
      | _ -> Set_to src
    )

  let pp ~data_pp format t =
    iteri ~f:(fun ~key ~data ->
      Format.fprintf format "%a => %a\n" Reference.pp key data_pp data
    ) t
end


module ClassHash = ReferenceHash

let weaken_typ typ =
  let weaken_typ = Type.weaken_literals typ in
  let weaken_typ =
    match weaken_typ with
    | Type.IntExpression _ -> Type.Primitive "int"
    | _ -> weaken_typ
  in
  weaken_typ



module type ArgTypes = sig
  type t = Type.t Identifier.Table.t
end



module ArgTypes = struct
  include Identifier.Table
  type t = Type.t Identifier.Table.t [@@deriving sexp, equal]

  let empty = create ()

  let set_arg_type t ident typ =
    let modified_typ = weaken_typ typ in
    let exn_typ = find t ident |> Option.value ~default:modified_typ in
    match exn_typ with
    | Bottom | Any | Top -> ()
    | _ ->
      set ~key:ident ~data:modified_typ t

  let add_arg_type ~join t ident typ =
    let modified_typ = weaken_typ typ in
    let exn_typ = find t ident |> Option.value ~default:modified_typ in
    match exn_typ with
    | Bottom | Any | Top -> ()
    | _ ->
      set ~key:ident ~data:(join modified_typ exn_typ) t

  let join ~type_join left right =
    merge_into ~src:left ~dst:right ~f:(fun ~key:_ src dst ->
      match dst with
      | None -> Set_to src
      | Some v -> 
        try
          Set_to (type_join src v)
        with
        | (* ClassHierarchy.Untracked *) _ -> Log.dump "%a\n%a\n" Type.pp src Type.pp v; Set_to (Type.union_join src v)
    ) 

  let pp format t =
    iteri ~f:(fun ~key ~data ->
      Format.fprintf format "%a -> %a \n" Identifier.pp key Type.pp data;
    ) t

  let get_type t ident =
    find t ident |> Option.value ~default:Type.Unknown

  let make_arg_types arg_typ_list =
    List.fold arg_typ_list ~init:empty ~f:(fun arg_types (arg, typ) -> set_arg_type arg_types arg typ; arg_types)
end

module ClassAttributes = struct
  type t = {
    attributes: AttrsSet.t;
    properties: AttrsSet.t;
    methods: AttributeAnalysis.CallSet.t Identifier.Table.t;
  } [@@deriving sexp, equal]

  let empty = {
    attributes=AttrsSet.empty;
    properties=AttrsSet.empty;
    methods=Identifier.Table.create ();
  }
  
  let pp_attrs_set format attrs_set =
    let attrs_string = (AttrsSet.fold attrs_set ~init:"{" ~f:(fun acc attr ->
      acc ^ ", " ^ attr
    )) ^ "}"
  in
  Format.fprintf format "%s" attrs_string

  let pp_method_set format method_set =
    let attrs_string = (Identifier.Table.fold method_set ~init:"{" ~f:(fun ~key:method_ ~data:_ acc ->
      acc ^ ", " ^ method_
    )) ^ "}"
  in
  Format.fprintf format "%s" attrs_string

  let pp format { attributes; properties; methods; } =
    Format.fprintf format "
      [[ Attributes ]]\n%a\n
      [[ Properties ]]\n%a\n
      [[ Methods ]]\n%a\n
    "
    pp_attrs_set attributes pp_attrs_set properties pp_method_set methods

  let join left right =
    Identifier.Table.merge_into ~src:left.methods ~dst:right.methods ~f:(fun ~key:_ src dst ->
      match dst with
      | Some v -> Set_to (AttributeAnalysis.CallSet.union src v)
      | _ -> Set_to src
    );

    {
      attributes=AttrsSet.union left.attributes right.attributes;
      properties=AttrsSet.union left.properties right.properties;
      methods=right.methods;
    }

  let add_attribute ({ attributes; _} as t) attr =
    { t with attributes=AttrsSet.add attributes attr }

  let add_property ({ properties; _} as t) prop =
    { t with properties=AttrsSet.add properties prop }

  let add_method ~call_info { methods; _ } meth =
    let call_set = 
      Identifier.Table.find methods meth 
      |> Option.value ~default:AttributeAnalysis.CallSet.empty
    in
    Identifier.Table.set methods ~key:meth ~data:(AttributeAnalysis.CallSet.add call_set call_info)

  let is_used_attr { attributes; properties; methods; } attr =
    let methods = AttrsSet.of_list (Identifier.Table.keys methods) in
    AttrsSet.exists (AttrsSet.union_list [attributes; properties; methods;]) ~f:(fun elem -> String.equal elem attr)
    (*
  let total_attributes { attributes; properties; methods; } =
    AttrsSet.union_list [attributes; properties; methods;]


  let is_subset_with_total_attributes t attributes =
    AttrsSet.is_subset attributes ~of_:(total_attributes t)
    *)
end 

module ClassSummary = struct
  type t = {
    class_var_type: Type.t ReferenceHash.t;
    class_attributes: ClassAttributes.t;
    usage_attributes: AttributeStorage.t;
  } [@@deriving sexp, equal]

  let empty = {
    class_var_type=ReferenceHash.empty;
    class_attributes=ClassAttributes.empty;
    usage_attributes=AttributeStorage.empty;
  }
  let get_class_var_type { class_var_type; _ } = class_var_type

  let get_usage_attributes { usage_attributes; _ } = usage_attributes

  let add_attribute ({ class_attributes; _} as t) attr =
    let class_attributes = ClassAttributes.add_attribute class_attributes attr in
    { t with class_attributes }

  let add_property ({ class_attributes; _} as t) property =
    let class_attributes = ClassAttributes.add_property class_attributes property in
    { t with class_attributes }

  let add_method ~call_info { class_attributes; _} meth =
    ClassAttributes.add_method class_attributes ~call_info meth

  let add_usage_attributes ({ usage_attributes; _ } as t) storage =
    { t with usage_attributes=AttributeStorage.join usage_attributes storage }

  let join ~type_join left right =
    ReferenceHash.join_type left.class_var_type right.class_var_type ~type_join;
    {
      class_var_type = right.class_var_type;
      class_attributes = ClassAttributes.join left.class_attributes right.class_attributes;
      usage_attributes = AttributeStorage.join left.usage_attributes right.usage_attributes;
    }

  let pp_class_var_type format { class_var_type; _ } =
      Format.fprintf format "[[[ Class Variable Type ]]] \n%a\n" (ReferenceHash.pp ~data_pp:Type.pp) class_var_type 

  let pp_class_info format { class_attributes; _ } =
      Format.fprintf format "[[[ Class Info ]]] \n%a\n" ClassAttributes.pp class_attributes

  let pp_usage_attributes format { usage_attributes; _ } =
      Format.fprintf format "[[[ Class Usage Attrs ]]] \n%a\n" AttributeStorage.pp usage_attributes

  let pp format t =
    Format.fprintf format "%a\n%a\n%a" pp_class_var_type t pp_class_info t pp_usage_attributes t
end

module type ClassTable = sig
  type t = ClassSummary.t ClassHash.t 
end

module ClassTable = struct
  type t = ClassSummary.t ClassHash.t [@@deriving sexp, equal]

  let empty = ClassHash.empty

  let find_default t name = ClassHash.find t name |> Option.value ~default:ClassSummary.empty 


  let add ~class_name ~data ~f t =
    let class_info = find_default t class_name in
    ClassHash.set t ~key:class_name ~data:(f class_info data)

  let add_attribute t class_name attr = add t ~class_name ~data:attr ~f:ClassSummary.add_attribute

  let add_property t class_name property = add t ~class_name ~data:property ~f:ClassSummary.add_property

  let add_method ~call_info t class_name meth = add t ~class_name ~data:meth ~f:(ClassSummary.add_method ~call_info)

  let add_usage_attributes t class_name storage = add t ~class_name ~data:storage ~f:ClassSummary.add_usage_attributes

  let set_class_info t class_name class_info =
    ClassHash.set t ~key:class_name ~data:class_info

  let get ~class_name ~f t = 
    let class_info = find_default t class_name in
    f class_info

  let get_class_info t class_name = get t ~class_name ~f:(fun x -> x)

  let get_class_var_type t class_name = get t ~class_name ~f:ClassSummary.get_class_var_type

  let get_usage_attributes t class_name = get t ~class_name ~f:ClassSummary.get_usage_attributes

  let join ~type_join left right =
    ClassMap.join left right ~equal:ClassSummary.equal ~data_join:(ClassSummary.join ~type_join)

  let pp format t =
    ClassMap.iteri ~f:(fun ~key ~data ->
      Format.fprintf format "[[[ Class : %a ]]] \n%a\n" Reference.pp key ClassSummary.pp data
    ) t

  let get_analysis_set ~get_functions prev next =
    ClassMap.fold2 prev next ~init:ReferenceSet.empty ~f:(fun ~key ~data ref_set ->
      match data with
      | `Right _ -> 
        get_functions key |> ReferenceSet.union ref_set
      | `Both (prev, next) -> 
        (
        if not (ClassSummary.equal prev next)
        then get_functions key
        else ReferenceSet.empty
        ) |> ReferenceSet.union ref_set 
      | `Left _ -> failwith "Why prev is bigger?"
    )
end

module FunctionSumary = struct
  type t = {
    arg_types: ArgTypes.t;
  } [@@deriving sexp, equal]
end

module FunctionTable = struct
  type t = FunctionSumary.t ReferenceHash.t
end *)