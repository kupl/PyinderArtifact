open Core
open Ast
open Ast.Util
open AttributeAnalysis
open OurDomain

let ( >>| ) = Option.( >>| )

module Store = Refinement.Store
module Unit = Refinement.Unit

(*
module VarType = struct
  type t = Reference.t * Type.t [@@deriving sexp, compare]
end

module StringSet = Set.Make (String)
module VarTypeMap = struct 
  include Map.Make (VarType)
  
  let join left right ~f =
    let merge_f ~key:_ data = 
      (match data with
      | `Left v | `Right v -> Some v
      | `Both (v1, v2) -> Some (f v1 v2)
      )
    in
    merge left right ~f:merge_f
  
end

module FunctionSet = ReferenceSet
module StoreMap = ReferenceMap
module ClassMap = ReferenceMap

module AttrsSet = StringSet
*)


module ClassSummaryResolution = struct
  include ClassSummary

  (*
  let extract_element_type store =
    (*Format.printf "[[[ BEFORE EXTRACT ELEMENT ]]] \n\n%a\n\n" Refinement.Store.pp store;*)
    let filter_element_type (typ: Type.t) =
      
      match typ with
      | Bottom | Any | Top -> false
      | _ -> true
      
    in
    let rec fold_unit u =
      let base = 
        match Refinement.Unit.base u with
        | Some base -> 
          if filter_element_type base.annotation then Some base else None
        | None -> None
      in
      let attributes = 
        Map.Tree.fold (Refinement.Unit.attributes u) ~init:(Identifier.Map.Tree.empty) ~f:(fun ~key ~data u ->
          Identifier.Map.Tree.set u ~key ~data:(fold_unit data)
        )
      in
      Refinement.Unit.create_all base attributes
    in
    let store = Refinement.Store.fold_map ~f:(fun ~key:reference ~data:unit store ->
      (*Format.printf "[ ITER ] \n\n%a \n\n%a \n\n" Reference.pp reference Refinement.Unit.pp unit;*)
      Reference.Map.set store ~key:reference ~data:(fold_unit unit)
    ) Refinement.Store.empty store
    in
    let x = Refinement.Store.update_with_filter ~old_store:Refinement.Store.empty ~new_store:store ~filter:(fun _ typ -> 
      (*Format.printf "%a \n\n%a \n\n" Reference.pp reference Annotation.pp typ;*)
        (match typ.annotation with
        | Bottom | Any | Top -> false
        | _ -> true
        )
    )
    in
    (*Format.printf "[ After Extract ] \n\n%a \n\n" Refinement.Store.pp x;*)
    x
  *)

  let get_type_of_class_attribute ~attribute { class_var_type; _ } =
    let name = Reference.create attribute in
    ReferenceMap.find class_var_type name |> Option.value ~default:Type.Unknown

  let get_self_attributes_tree t =
    (*let name = Reference.create "$parameter$self" in*)
    let reference_map = 
      get_class_var_type t
    in
    ReferenceMap.fold ~init:Unit.empty ~f:(fun ~key ~data sofar ->
        Unit.set_annotation ~attribute_path:key ~annotation:(Annotation.create_mutable data) sofar
    ) reference_map
    |> Unit.attributes

  let add_class_var_type ~type_join class_var_type reference typ =
    ReferenceMap.update class_var_type reference ~f:(fun origin ->
      origin |> Option.value ~default:Type.Bottom |> type_join typ
    )

  let add_parent_attributes ({ class_attributes; usage_attributes; _ } as t) storage =
    let storage = 
      AttributeStorage.filter_keys storage ~f:(fun key -> 
        match Expression.get_identifier_base key with
        | Some base -> ClassAttributes.is_used_attr class_attributes base
        | _ -> false
      ) 
    in
    { t with usage_attributes=AttributeStorage.join usage_attributes storage }
    
  let join_with_merge_class_var_type ~type_join ({ class_var_type; _ } as t) class_param (method_postcondition: Refinement.Store.t) =
    (*
    여기서 postcondition의 변수 하나하나를 저장한다   
    *)


    let filter_keys = Reference.create class_param in

    let rec attribute_fold ~base_reference ~attributes class_var_type =
      Identifier.Map.Tree.fold ~init:class_var_type ~f:(fun ~key ~data class_var_type ->
        unit_fold ~unit:data ~base_reference:(Reference.combine base_reference (Reference.create key)) class_var_type
      ) attributes
    
    and unit_fold ~unit ~base_reference class_var_type =
      let typ = unit |> Refinement.Unit.base >>| Annotation.annotation |> Option.value ~default:Type.Unknown in
      let class_var_type = add_class_var_type ~type_join class_var_type base_reference typ in
      attribute_fold ~base_reference ~attributes:(unit |> Refinement.Unit.attributes) class_var_type
    in 
    
    let annotation_fold annotation class_var_type =
      Reference.Map.fold ~init:class_var_type ~f:(fun ~key ~data class_var_type ->
        if Reference.is_prefix ~prefix:filter_keys key then (
          let x = unit_fold ~unit:data ~base_reference:Reference.empty class_var_type in
          x
        )
        else
          class_var_type
      ) annotation
    in

    let class_var_type = 
      let x =
      ReferenceMap.empty
      |> annotation_fold method_postcondition.annotations
      |> annotation_fold method_postcondition.temporary_annotations
      in

      x
      |> ReferenceMap.join ~equal:Type.equal ~data_join:type_join class_var_type
    in

    ClassSummary.{ t with class_var_type }

end

module ClassTableResolution = struct
  include ClassTable

  let add_parent_attributes t class_name storage = add t ~class_name ~data:storage ~f:ClassSummaryResolution.add_parent_attributes

  let get_type_of_class_attribute t class_name attribute = get t ~class_name ~f:(ClassSummaryResolution.get_type_of_class_attribute ~attribute)

  let get_self_attributes_tree t class_name = get t ~class_name ~f:ClassSummaryResolution.get_self_attributes_tree

  let join_with_merge_class_var_type ~type_join t class_name class_param method_postcondition =
    let class_summary = find_default t class_name in
    let data = ClassSummaryResolution.join_with_merge_class_var_type ~type_join class_summary class_param method_postcondition in
    ClassMap.set ~key:class_name ~data t

  let find_classes_from_attributes t { AttributeStorage.attribute_set; call_set; } =
    let attribute_set = Identifier.Set.fold attribute_set ~init:AttrsSet.empty ~f:(fun acc attr -> AttrsSet.add acc attr) in

    let more_accurate =
      ClassMap.fold t ~init:[] ~f:(fun ~key ~data:{ ClassSummary.class_attributes={ attributes; properties; methods }; _ } candidate_classes ->
        let field_set = AttrsSet.union_list [attributes; properties; (AttrsSet.of_list (Identifier.Map.keys methods))] in
        let field_flag = AttrsSet.is_subset attribute_set ~of_:field_set in
        let method_flag = Identifier.Map.fold2 call_set methods ~init:true ~f:(fun ~key:_ ~data flag ->
          flag &&  
          (match data with
          | `Both (left, right) ->
            CallSet.fold left ~init:true ~f:(fun flag call_info -> 
              flag &&  
              CallSet.exists right ~f:(fun signature -> CallInfo.is_more_corresponding ~signature call_info)
            )
          | `Right _ -> true
          | `Left _ -> false
          )
        )
        in
  
  
        if field_flag && method_flag
        then (key::candidate_classes)
        else candidate_classes
      )
    in

    if List.is_empty more_accurate then
      ClassMap.fold t ~init:[] ~f:(fun ~key ~data:{ ClassSummary.class_attributes={ attributes; properties; methods }; _ } candidate_classes ->
        let field_set = AttrsSet.union_list [attributes; properties; (AttrsSet.of_list (Identifier.Map.keys methods))] in
        let field_flag = AttrsSet.is_subset attribute_set ~of_:field_set in
        let method_flag = Identifier.Map.fold2 call_set methods ~init:true ~f:(fun ~key:_ ~data flag ->
          flag &&  
          (match data with
          | `Both (left, right) ->
            CallSet.fold left ~init:true ~f:(fun flag call_info -> 
              flag &&  
              CallSet.exists right ~f:(fun signature -> CallInfo.is_corresponding ~signature call_info)
            )
          | `Right _ -> true
          | `Left _ -> false
          )
        )
        in


        if field_flag && method_flag
        then (key::candidate_classes)
        else candidate_classes
      )
    else more_accurate
end

module ArgTypesResolution = struct
  include ArgTypes
  let import_from_resolution ~join resolution =
    let annotation_store = Resolution.get_annotation_store resolution in

    let iter_base annotation arg_types =
      Reference.Map.fold annotation ~init:arg_types ~f:(fun ~key ~data arg_types ->
        match data |> Unit.base with
        | Some annotation when Reference.is_parameter key -> 
          let x = ArgTypes.add_arg_type ~join arg_types (key |> Reference.show) (Annotation.annotation annotation) in
          x
        | _ -> arg_types
      )
    in

    let x =
    ArgTypes.empty
    |> iter_base annotation_store.annotations
    |> iter_base annotation_store.temporary_annotations
    in
    x


  let export_to_resolution t resolution = 
    IdentifierMap.fold ~f:(fun ~key ~data resolution ->
        Resolution.new_local resolution ~reference:(Reference.create key) ~annotation:(Annotation.create_immutable data)
    ) t ~init:resolution

  let join_to_resolution ~join t resolution = 
    IdentifierMap.fold ~f:(fun ~key ~data resolution ->
      let reference = Reference.create key in
      let old_type = Resolution.resolve_reference resolution reference in
      let new_type = join data old_type in
      Resolution.refine_local resolution ~reference ~annotation:(Annotation.create_mutable new_type)
    ) t ~init:resolution

(*   let callable_to_arg_types ~self_argument ~(arguments: AttributeResolution.Argument.t list) (callable: Type.Callable.t) =
    let params = callable.implementation.parameters in
    let param_list = 
    (match params with
    | Defined defined_param_list ->
      List.fold defined_param_list ~init:[] ~f:(fun acc param ->
        (match param with
        | PositionalOnly s -> (String.concat ["__pyinder_"; string_of_int s.index; "__"])::acc
        | Named n -> n.name::acc
        | _ -> (*print_endline "Other Param";*) acc
        )
      )
    | _ -> (*print_endline "No defined";*) []
    )
    in
    let param_list = List.rev param_list in
      let param_type_init, revise_index = 
      (match self_argument with
      | Some t -> if List.length param_list == 0 then [], 1 else [(List.nth_exn param_list 0,t)], 1
      | None -> (*Log.dump "No Self";*) [], 0
      )
    in

    let param_type_list = List.foldi arguments ~init:param_type_init ~f:(fun idx acc arg ->
      if List.length param_list <= (idx+revise_index) then acc
      else
      (match arg.kind with
      | SingleStar | DoubleStar -> (*print_endline "This is Star Arg";*) acc
      | Named s ->  
        (s.value, arg.resolved)::acc
      | Positional -> 
        (List.nth_exn param_list (idx+revise_index), arg.resolved)::acc
      )
    )
    in

    let param_type_list = List.rev param_type_list in

    let save_param_type_list =
      (match self_argument with
      | Some _ -> 
        if List.length param_list == 0 
        then param_type_list 
        else 
          let _, no_self_param = List.split_n param_type_list 1 in
          no_self_param
      | None -> param_type_list
      )
    in

    ArgTypes.make_arg_types save_param_type_list *)


end

module FunctionSummaryResolution = struct
  include FunctionSummary

  let store_to_return_var_type ?class_param ({ signatures; _ } as t) arg_types (store: Refinement.Store.t) =
    let return_var_type = Signatures.get_return_var_type signatures arg_types in

    let class_param = class_param |> Option.value ~default:"" |> Reference.create in
    (* parameter만 *)
    let rec attribute_fold ~base_reference ~attributes return_var_type =
      
      Identifier.Map.Tree.fold ~init:return_var_type ~f:(fun ~key ~data return_var_type ->
        unit_fold ~unit:data ~base_reference:(Reference.combine base_reference (Reference.create key)) return_var_type
      ) attributes
    
    and unit_fold ~unit ~base_reference return_var_type =
      let typ = unit |> Refinement.Unit.base >>| Annotation.annotation |> Option.value ~default:Type.Unknown in
      let return_var_type = 
        if Reference.equal class_param base_reference then return_var_type
        else ReferenceMap.set return_var_type ~key:base_reference ~data:typ 
      in
      attribute_fold ~base_reference ~attributes:(unit |> Refinement.Unit.attributes) return_var_type
    in 
    
    let annotation_fold annotation return_var_type =
      Reference.Map.fold ~init:return_var_type ~f:(fun ~key ~data return_var_type ->
        if Reference.is_parameter key then
          let x = unit_fold ~unit:data ~base_reference:key return_var_type in
          x
        else
          return_var_type
      ) annotation
    in

    let return_var_type = 
      let x =
      return_var_type
      |> annotation_fold store.annotations
      |> annotation_fold store.temporary_annotations
      in
      x
    in

    let signatures = Signatures.set_return_var_type signatures arg_types return_var_type in

    FunctionSummary.{ t with signatures; }

  let find_class_of_attributes ~successors ~class_table ?(debug=false) { usage_attributes; _ } parent_usage_attributes =

    let _ = debug in
    (* have to make proper filter *)
    let extract_class classes =
      let classes = List.map classes ~f:Reference.show in
      let filtered_classes =
        let get_childish classes =
          let result =
            List.find classes ~f:(fun cls ->
              let class_successors = cls::(successors cls) in
              List.for_all classes ~f:(fun origin -> 
                List.exists class_successors ~f:(String.equal origin)
              )
            )
          in
          
          match result with
          | Some child -> Some [child]
          | _ -> None
        in

        match get_childish classes with
        | Some c -> c (* Get Childish Class *)
        | _ -> (* Get Parents *)
          let parents = 
            List.fold classes ~init:classes ~f:(fun parents cls ->
              let class_successors = cls::(successors cls) in

              List.filter parents ~f:(fun parent ->
                List.exists class_successors ~f:(String.equal parent)  
              )

              (* List.fold class_successors ~init:false ~f:(fun acc suc ->
                acc || (List.exists classes ~f:(String.equal suc))  
              ) |> not *)
            )
          in
          parents
          |> get_childish
          |> Option.value ~default:parents
      in

      if List.length filtered_classes > 1 then (
        None
      )
      else if List.length filtered_classes = 1 then (
        List.nth_exn filtered_classes 0 |> Reference.create |> Option.some
      )
      else (
       None
      )
    in
    let usage_attributes =
      parent_usage_attributes
      |> AttributeStorage.join usage_attributes
    in
    
    
    
    AttributeStorage.mapi usage_attributes ~f:(fun ~key ~data:attributes -> 
        let _ = key in
        attributes
        |> ClassTableResolution.find_classes_from_attributes class_table
        |> extract_class

    )
    |> LocInsensitiveExpMap.filter_map ~f:(fun v -> 
      match v with
      | Some v -> Some v
      | _ -> v  
    )

end

module FunctionTableResolution = struct
  include FunctionTable

  let store_to_return_var_type ?class_param t func_name arg_types (store: Refinement.Store.t) =
    let func_summary = FunctionMap.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionMap.set t ~key:func_name ~data:(FunctionSummaryResolution.store_to_return_var_type ?class_param func_summary arg_types store)

  let find_class_of_attributes ~successors ~class_table (t: t) func_name parent_usage_attributes =
    let func_summary = FunctionMap.find t func_name |> Option.value ~default:FunctionSummary.empty in
    let debug = 
      String.is_substring (Reference.show func_name) ~substring:"_write_col_header"
    in
    FunctionSummaryResolution.find_class_of_attributes ~successors ~class_table ~debug func_summary parent_usage_attributes

end

module OurSummaryResolution = struct
  include OurSummary

  let store_to_return_var_type ?class_param ({ function_table; _ } as t) func_name arg_types store = 
    { t with function_table=FunctionTableResolution.store_to_return_var_type ?class_param function_table func_name arg_types store; }

  let get_type_of_class_attribute { class_table; _ } class_name attribute = ClassTableResolution.get_type_of_class_attribute class_table class_name attribute
  
  let get_self_attributes_tree { class_table; _ } class_name = ClassTableResolution.get_self_attributes_tree class_table class_name

  let add_parent_attributes ({ class_table; _ } as t) storage class_name class_var =
    (* 이거 짜야 댕 *)
    let filtered_storage = AttributeStorage.filter_by_prefix storage ~prefix:(Reference.create class_var) in
    let class_table = ClassTableResolution.add_parent_attributes class_table class_name filtered_storage in
    { t with class_table; }


  (*
  let search_suspicious_variable t ~store_combine parent =
    (*let usedef_table = get_usedef_table t func_name |> Option.value ~default:UsedefState.bottom in*)
    let possible_condition = ClassTableResolution.get_class_var_type t.class_table parent in
    let total_annotation = store_combine possible_condition in
    
    (* split each variables and types *)
    let f ~key ~data sofar = 
      let rec split_attrs (target_unit: Refinement.Unit.t)  = 
        let cand_attrs = Identifier.Map.Tree.fold (Refinement.Unit.attributes target_unit) ~init:[] ~f:(fun ~key:attr ~data:inner_unit cand -> 
          let cand_attrs = split_attrs inner_unit in
          cand@(List.map cand_attrs ~f:(fun cand_attr -> Identifier.Map.Tree.add Identifier.Map.Tree.empty ~key:attr ~data:cand_attr))
        )
        in
        if List.is_empty cand_attrs 
        then 
          let new_base_list =
            let new_anno_list =
              match (Refinement.Unit.base target_unit) with
              | None -> [None]
              | Some anno ->
                (match Annotation.annotation anno with
                | Type.Union t_list ->  List.map t_list ~f:(fun t -> Some (Annotation.create_mutable t))
                | _ -> [Some anno]
                )
            in
            List.map new_anno_list ~f:(fun new_anno -> Refinement.Unit.create_all new_anno Identifier.Map.Tree.empty)
          in
          new_base_list
        else
        List.map cand_attrs ~f:(fun cand_attr -> 
          match cand_attr with
          | `Duplicate -> raise DuplicateException
          | `Ok cand_attr -> 
          (*  
          Identifier.Map.Tree.iteri cand_attr ~f:(fun ~key ~data -> Log.dump "cand_attr %s >>> %a" key Refinement.Unit.pp data);
          *)
            Refinement.Unit.create_all (Refinement.Unit.base target_unit) cand_attr)
      in
      let candidates = split_attrs data in
      sofar@(List.map candidates ~f:(fun cand -> Reference.Map.set Reference.Map.empty ~key ~data:cand ))
    in

    let candidates = Reference.Map.fold total_annotation ~init:[] ~f:f in
    (*
    List.iter candidates ~f:(fun cand -> Reference.Map.iteri cand ~f:(fun ~key ~data -> Format.printf "%a -> %a\n" Reference.pp key Refinement.Unit.pp data));
    *)
    candidates
  *)

  let find_class_of_attributes ~successors { class_table; function_table; } func_name parent_usage_attributes  =
    FunctionTableResolution.find_class_of_attributes ~successors ~class_table function_table func_name parent_usage_attributes
end

