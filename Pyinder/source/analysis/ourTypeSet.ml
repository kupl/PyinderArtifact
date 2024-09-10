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

  let get_type_of_class_attribute ~function_table ~class_name ~attribute ~type_join ~less_or_equal { class_var_type; class_attributes; _ } =
    let name = Reference.create attribute in
    let properties = ClassAttributes.get_class_property class_attributes in

    if AttrsSet.mem properties attribute then (
      
      let reference = Reference.combine class_name name in
      (* let x = (FunctionTable.get_return_type ~less_or_equal ~property:true function_table reference ArgTypes.empty) in *)
      (* Log.dump "HMM? %a => %a (%a)" Reference.pp reference Type.pp x Reference.pp reference; *)
      Some (FunctionTable.get_return_type ~type_join ~less_or_equal ~property:true function_table reference ArgTypes.empty)
    ) else (
      let type_from_funcs_opt =
        ReferenceMap.find class_var_type name
      in 
      match type_from_funcs_opt with
      | Some v -> TypeFromFuncs.get_type ~type_join v
      | None -> None
    )

  let get_self_attributes_tree ~type_join t =
    (*let name = Reference.create "$parameter$self" in*)
    let reference_map = 
      get_class_var_type t
    in
    ReferenceMap.fold ~init:Unit.empty ~f:(fun ~key ~data sofar ->
      let data = TypeFromFuncs.get_type ~type_join data in
      match data with
      | Some data ->
        Unit.set_annotation ~attribute_path:key ~annotation:(Annotation.create_mutable data) sofar
      | _ -> sofar
    ) reference_map
    |> Unit.attributes

  let get_temp_self_attributes_tree ~type_join t =
      (*let name = Reference.create "$parameter$self" in*)
      let reference_map = 
        get_temp_class_var_type t
      in
      ReferenceMap.fold ~init:Unit.empty ~f:(fun ~key ~data sofar ->
        let data = TypeFromFuncs.get_type ~type_join data in
        match data with
        | Some data ->
          Unit.set_annotation ~attribute_path:key ~annotation:(Annotation.create_mutable data) sofar
        | _ -> sofar
      ) reference_map
      |> Unit.attributes

  let add_class_var_type ~type_join class_var_type reference typ =
    ReferenceMap.update class_var_type reference ~f:(fun origin ->
      let _ = origin, type_join in
      typ
      (* origin |> Option.value ~default:Type.Bottom |> type_join typ *)
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
    
  let join_with_merge_class_var_type ~define ~type_join ~less_or_equal ~properties ~(usedef_table: Usedef.UsedefState.t) 
    ~final_summary:{ temp_class_var_type=final_temp_class_var_type; _ }
    ({ class_var_type; temp_class_var_type; _ } as t) class_param (method_postcondition: Refinement.Store.t) =

    let _ = define, properties, method_postcondition in
    let _ = add_class_var_type in

    let filter_keys = Reference.create class_param in

    let check_properties reference =
      AttrsSet.exists properties ~f:(fun p -> 
        if Reference.is_self reference || Reference.is_cls reference then
          String.equal p (Reference.drop_head reference |> Reference.show)
        else
          String.equal p (Reference.show reference)
      )
    in

    let check_class_variable reference =
      (Reference.is_prefix ~prefix:filter_keys reference) || Reference.is_self reference || Reference.is_cls reference
    in

    let make_var_from_funcs ~key result_type =
      let result_type = Type.our_dict_to_dict result_type in
      let callees = 
        ReferenceMap.find final_temp_class_var_type key
        |> Option.value ~default:TypeFromFuncs.empty
        |> TypeFromFuncs.get_callees ~typ:result_type ~less_or_equal
      in
      TypeFromFuncs.set TypeFromFuncs.empty ~key:result_type ~data:callees
    in

    let make_temp_var_from_funcs ~define result_type =
      let result_type = Type.our_dict_to_dict result_type in

      TypeFromFuncs.set TypeFromFuncs.empty ~key:result_type ~data:(Reference.Set.singleton define)
    in


    let new_class_var_type =
      let update_check_used =
        Reference.Map.fold usedef_table.check_used ~init:ReferenceMap.empty ~f:(fun ~key ~data acc ->
          (* Log.dump "TEST : %a =>" Reference.pp key;
          Usedef.TypeSet.iter data ~f:(fun t -> Log.dump "::: %a" Type.pp t); *)
          if check_properties key then (
            acc
          )
          else if check_class_variable key then
            let key = Reference.drop_head key in
            let data = make_var_from_funcs ~key (Usedef.TypeSet.fold data ~init:Type.Bottom ~f:(fun acc t -> type_join acc t)) in
            ReferenceMap.set acc ~key ~data
          else
            acc
        )
      in

      let update_before =
        Reference.Map.fold usedef_table.used_before_defined ~init:update_check_used ~f:(fun ~key ~data acc ->
          (* Log.dump "TEST : %a =>" Reference.pp key;
          Usedef.TypeSet.iter data ~f:(fun t -> Log.dump "::: %a" Type.pp t); *)
          if check_properties key then (
            acc
          )
          else if check_class_variable key then
            let key = Reference.drop_head key in
            let data = make_var_from_funcs ~key (Usedef.TypeSet.fold data ~init:Type.Bottom ~f:(fun acc t -> type_join acc t)) in

            ReferenceMap.set acc ~key ~data
          else
            acc
        )
      in

      let update_after =
        Reference.Map.fold usedef_table.used_after_defined ~init:update_before ~f:(fun ~key ~data acc ->
          (* Log.dump "TEST : %a =>" Reference.pp key;
          Usedef.TypeSet.iter data ~f:(fun t -> Log.dump "::: %a" Type.pp t); *)
          if check_properties key then (
            acc
          )
          else if check_class_variable key then
            let key = Reference.drop_head key in
            let data = make_var_from_funcs ~key (Usedef.TypeSet.fold data ~init:Type.Bottom ~f:(fun acc t -> type_join acc t)) in
            ReferenceMap.set acc ~key ~data
          else
            acc
        )
      in

      update_after
      |> ReferenceMap.join_var_from_funcs class_var_type
      (* |> ReferenceMap.join_var_from_funcs ~equal:Type.equal ~data_join:type_join class_var_type *)
    in

    let new_temp_class_var_type =
      Reference.Map.fold usedef_table.defined ~init:ReferenceMap.empty ~f:(fun ~key ~data acc ->
        if check_properties key then (
          acc
        )
        else if check_class_variable key then
          let key = Reference.drop_head key in
          let data = make_temp_var_from_funcs ~define (Usedef.TypeSet.fold data ~init:Type.Bottom ~f:(fun acc t -> type_join acc t)) in
          ReferenceMap.set acc ~key ~data
          (* ReferenceMap.set acc ~key:(Reference.drop_head key) ~data:(Usedef.TypeSet.fold data ~init:Type.Bottom ~f:(fun acc t -> type_join acc t))   *)
        else
          acc
      )
      |> ReferenceMap.join_var_from_funcs temp_class_var_type
      (* |> ReferenceMap.join ~equal:Type.equal ~data_join:type_join temp_class_var_type *)
    in

    (* let new_class_var_type = ReferenceMap.map new_class_var_type ~f:Type.our_dict_to_dict in
    let new_temp_class_var_type = ReferenceMap.map new_temp_class_var_type ~f:Type.our_dict_to_dict in *)

    ClassSummary.{ t with class_var_type=new_class_var_type; temp_class_var_type=new_temp_class_var_type; }
    (*     (*
    여기서 postcondition의 변수 하나하나를 저장한다   
    *)
    let check_properties reference =
      AttrsSet.exists properties ~f:(String.equal (Reference.show reference))
    in

    (* let check_usedef_defined reference =
      Reference.Set.exists usedef_table.defined ~f:(fun ref ->
        Reference.is_self ref &&
        Reference.is_contain ~base:(Reference.drop_head ref) ~target:reference
      )
    in *)
    let no_check _ _ = true in

    let check_usedef_used reference _ =
      (* sedef.VarTypeSet.iter usedef_table ~f:(fun (ref, _) ->
        Log.dump "TEST %a" Reference.pp ref;  
      );
      Log.dump "OHOH %a" Reference.pp reference; *)

      Reference.Map.existsi usedef_table.used_after_defined ~f:(fun ~key:ref ~data:_ ->
        Reference.is_self ref &&
        Reference.equal (Reference.drop_head ref) reference
        (* Reference.is_contain ~base:(Reference.drop_head ref) ~target:reference *)
      )
      (* ||
      Reference.Set.exists usedef_table.used_after_defined ~f:(fun ref ->
        Reference.is_self ref &&
        Reference.is_contain ~base:(Reference.drop_head ref) ~target:reference
      ) *)
    in

    let check_usedef_used_type reference typ =
        Reference.Map.existsi usedef_table.used_after_defined ~f:(fun ~key:ref ~data:ref_typ ->
          Reference.is_self ref &&
          Reference.equal (Reference.drop_head ref) reference &&
          Usedef.TypeSet.mem ref_typ typ
         (*  Reference.is_contain ~base:(Reference.drop_head ref) ~target:reference *)
        )
      (* ||
      Reference.Set.exists usedef_table.used_after_defined ~f:(fun ref ->
        Reference.is_self ref &&
        Reference.is_contain ~base:(Reference.drop_head ref) ~target:reference
      ) *)
    in

    let filter_keys = Reference.create class_param in

    let rec attribute_fold ~base_reference ~attributes ?check_usedef class_var_type =
      Identifier.Map.Tree.fold ~init:class_var_type ~f:(fun ~key ~data class_var_type ->
        unit_fold ~unit:data ~base_reference:(Reference.combine base_reference (Reference.create key)) ?check_usedef class_var_type
      ) attributes
    
    and unit_fold ~unit ~base_reference ?check_usedef class_var_type =
      let typ = unit |> Refinement.Unit.base >>| Annotation.annotation |> Option.value ~default:Type.Unknown in
      let class_var_type = 
        if check_properties base_reference then class_var_type
        else (
          match check_usedef with
          | Some check_usedef ->   
            if check_usedef base_reference typ
            then (
              add_class_var_type ~type_join class_var_type base_reference typ 
            )
            else class_var_type 
          | _ -> add_class_var_type ~type_join class_var_type base_reference typ 
        )
      in
      attribute_fold ~base_reference ~attributes:(unit |> Refinement.Unit.attributes) ?check_usedef class_var_type
    in 
    
    let annotation_fold ?check_usedef annotation class_var_type =
      Reference.Map.fold ~init:class_var_type ~f:(fun ~key ~data class_var_type ->
        if Reference.is_prefix ~prefix:filter_keys key then (
          let x = unit_fold ~unit:data ~base_reference:Reference.empty ?check_usedef class_var_type in
          x
        )
        else
          class_var_type
      ) annotation
    in

    let new_class_var_type = 
      let x =
      ReferenceMap.empty
      |> annotation_fold ~check_usedef:no_check method_postcondition.annotations
      |> annotation_fold ~check_usedef:check_usedef_used method_postcondition.temporary_annotations
      in

      if String.is_substring (Reference.show define) ~substring:"homeassistant.helpers.entity_component.EntityComponent"
      then
        ReferenceMap.iteri x ~f:(fun ~key ~data -> Log.dump "%a ====> %a" Reference.pp key Type.pp data);

      x
      |> ReferenceMap.join ~equal:Type.equal ~data_join:type_join class_var_type
    in

    let new_temp_class_var_type =
      let x =
        ReferenceMap.empty
        (* |> annotation_fold ~check_usedef:check_usedef_defined method_postcondition.annotations *)
        |> annotation_fold ~check_usedef:check_usedef_used_type method_postcondition.temporary_annotations
        in
  
        (* ReferenceMap.iteri x ~f:(fun ~key ~data -> Log.dump "%a ====> %a" Reference.pp key Type.pp data); *)
  
        x
        |> ReferenceMap.join ~equal:Type.equal ~data_join:type_join temp_class_var_type
    in

    (* let change_set = ReferenceMap.diff class_var_type new_class_var_type |> ReferenceSet.union change_set in *)

    ClassSummary.{ t with class_var_type=new_class_var_type; temp_class_var_type=new_temp_class_var_type; }
 *)
    let filter_used_variable ~used_variable { class_var_type; temp_class_var_type; _ } =
      Reference.Map.fold used_variable ~init:Reference.Map.empty ~f:(fun ~key ~data:used_types acc -> 

        (* Log.dump "TEST %a" Reference.pp key; *)

        let temp_type_from_funcs = 
          ReferenceMap.find temp_class_var_type key
          |> Option.value ~default:TypeFromFuncs.empty
        in

        let type_from_funcs = 
          ReferenceMap.find class_var_type key
          |> Option.value ~default:TypeFromFuncs.empty
        in

        let type_map =
          TypeFromFuncs.fold temp_type_from_funcs ~init:Type.Map.empty ~f:(fun ~key:typ ~data:funcs acc ->

            (* Log.dump "HMM? %a %b" Type.pp typ (Reference.Set.is_empty funcs); *)
            
            let check_flag =
              Usedef.TypeSet.exists used_types ~f:(fun t -> 
                (* Log.dump "USED : %a" Type.pp t; *)
                let t = Type.filter_unknown t |> Type.weaken_union in
                let typ = Type.filter_unknown typ |> Type.weaken_union in
                Type.can_union t ~f:(Type.equal typ) || Type.can_union typ ~f:(Type.equal t)
              ) && not (Reference.Set.is_empty funcs)
            in

            (* Log.dump "CHECK %b" check_flag; *)

            if check_flag then
              let origin_functions = funcs in
              let defined_functions = Reference.Set.empty in

              let defined_functions = 
                TypeFromFuncs.fold type_from_funcs ~init:defined_functions ~f:(fun ~key:other_typ ~data:other_funcs defined_functions ->
                  let other_typ = Type.weaken_union other_typ in
                  let typ = Type.weaken_union typ in
                  if Type.can_union typ ~f:(Type.equal other_typ) || Type.can_union other_typ ~f:(Type.equal typ) then
                    defined_functions
                  else
                    Reference.Set.diff other_funcs origin_functions
                    |> Reference.Set.union defined_functions
                )
              in

              let defined_functions = 
                TypeFromFuncs.fold temp_type_from_funcs ~init:defined_functions ~f:(fun ~key:other_typ ~data:other_funcs defined_functions ->
                  let other_typ = Type.weaken_union other_typ in
                  let typ = Type.weaken_union typ in
                  if Type.can_union typ ~f:(Type.equal other_typ) || Type.can_union other_typ ~f:(Type.equal typ) then
                    defined_functions
                  else
                    Reference.Set.diff other_funcs origin_functions
                    |> Reference.Set.union defined_functions
                )
              in

              (* Reference.Set.iter defined_functions ~f:(fun ref -> Log.dump "DEFINED %a" Reference.pp ref);
              Reference.Set.iter origin_functions ~f:(fun ref -> Log.dump "ORIGIN %a" Reference.pp ref);
 *)
              Type.Map.set ~key:typ ~data:(defined_functions, origin_functions) acc
            else
              acc
          )
        in

        (* Type.Map.iteri type_map ~f:(fun ~key ~data:_ ->
          Log.dump "OK? %a" Type.pp key;
        ); *)

        (* let type_map_filter = 
          Type.Map.filter_keys type_map ~f:(fun t ->
            Log.dump "WHY?";
            TypeFromFuncs.existsi type_from_funcs ~f:(fun ~key:other_typ ~data:_ ->
              Log.dump "%a vs %a" Type.pp other_typ Type.pp t;
              let other_typ = Type.weaken_union other_typ in
              let t = Type.weaken_union t in
              Type.can_union other_typ ~f:(Type.equal t)
            )
            |> not
          )
        in *)

        let type_map_filter = type_map in

        (* Type.Map.iteri type_map_filter ~f:(fun ~key ~data:_ ->
          Log.dump "WHAT? %a" Type.pp key;
        ); *)

        Reference.Map.set acc ~key ~data:type_map_filter

        (* let origin_functions =
          
          |> TypeFromFuncs.get_all_callees
        in

        (match ReferenceMap.find class_var_type key with
        | Some var_from_funcs ->
          let type_to_reference_set_map =
            Usedef.TypeSet.fold data ~init:Type.Map.empty ~f:(fun acc t ->
              let filtered_typ, defined_functions, origin_functions = 
                TypeFromFuncs.fold var_from_funcs ~init:(t, Reference.Set.empty, origin_functions) ~f:(fun ~key:typ ~data:funcs (origin_t, defined_functions, origin_functions) ->
                  if Type.can_union t ~f:(Type.equal typ) then
                    Type.filter_type origin_t ~f:(Type.equal typ), Reference.Set.union funcs defined_functions, Reference.Set.diff origin_functions funcs
                  else
                    origin_t, defined_functions, origin_functions
                )
              in

              Type.Map.set acc ~key:filtered_typ ~data:(defined_functions, origin_functions)
            )
          in

          (* let filtered_type_set, defined_functions =
            Usedef.TypeSet.fold data ~init:(TypeSet.empty, Reference.Set.empty) 
            TypeFromFuncs.fold var_from_funcs ~init:(data, Reference.Set.empty) ~f:(fun ~key:typ ~data:funcs (type_set, defined_functions) ->
              if Type.can_union data ~f:(Type.equal typ) then
                (Type.filter_type type_set ~f:(Type.equal typ), Reference.Set.union funcs defined_functions)
              else
                (type_set, defined_functions)
            )
          in *)

          Reference.Map.set acc ~key ~data:type_to_reference_set_map

        | None -> acc
        ) *)
      )

  let update_test_passed_used_variable ~test_passed_used_variable ~end_define ({ class_var_type; seen_var_type; _ } as t) =
    let class_var_type = 
      Reference.Map.fold test_passed_used_variable ~init:class_var_type ~f:(fun ~key ~data acc ->
        let type_from_funcs = 
          Type.Map.fold data ~init:TypeFromFuncs.empty ~f:(fun ~key:typ ~data:(_, origin_functions) acc ->
            TypeFromFuncs.set acc ~key:typ ~data:origin_functions
          )
        in

        let data = 
          ReferenceMap.find class_var_type key |> Option.value ~default:TypeFromFuncs.empty 
          |> TypeFromFuncs.join type_from_funcs
        in

        ReferenceMap.set acc ~key ~data
      )
    in

    let seen_var_type =
      Reference.Map.fold test_passed_used_variable ~init:seen_var_type ~f:(fun ~key ~data acc ->
        (* let data =
          let refset = ReferenceMap.find acc end_define |> Option.value ~default:Reference.Set.empty in
          Reference.Set.add refset key
        in
        
        ReferenceMap.set acc ~key:end_define ~data *)

        (* Log.dump "Update : %a" Reference.pp key; *)

        if Type.Map.is_empty data then acc
        else (
          ReferenceMap.update acc end_define ~f:(fun origin ->
            let origin = Option.value ~default:Reference.Set.empty origin in
            Reference.Set.add origin key
          )
        )
      )
    in

    { t with class_var_type; seen_var_type; }
end

module ClassTableResolution = struct
  include ClassTable

  let add_parent_attributes t class_name storage = add t ~class_name ~data:storage ~f:ClassSummaryResolution.add_parent_attributes

  let get_type_of_class_attribute ~type_join ~less_or_equal ~function_table t class_name attribute = get t ~class_name ~f:(
    ClassSummaryResolution.get_type_of_class_attribute ~function_table ~class_name ~attribute ~type_join ~less_or_equal)

  let get_self_attributes_tree ~type_join t class_name = get t ~class_name ~f:(ClassSummaryResolution.get_self_attributes_tree ~type_join)

  let get_temp_self_attributes_tree ~type_join t class_name = get t ~class_name ~f:(ClassSummaryResolution.get_temp_self_attributes_tree ~type_join)
  let join_with_merge_class_var_type ~type_join ~less_or_equal ~define ~properties ~usedef_table ~final_class_table t class_name class_param method_postcondition =
    let class_summary = find_default t class_name in
    let final_summary = find_default final_class_table class_name in
    let data = ClassSummaryResolution.join_with_merge_class_var_type ~define ~type_join ~less_or_equal ~properties ~usedef_table ~final_summary class_summary class_param method_postcondition in
    ClassHash.set ~key:class_name ~data t

  let find_default_type_from_attributes ~key ~default_type:{ OurDomain.ClassAttributes.attributes; properties; methods } { AttributeStorage.attribute_set; call_set; } =
    let attribute_set = Identifier.Set.fold attribute_set ~init:AttrsSet.empty ~f:(fun acc attr -> AttrsSet.add acc attr) in

    let field_set = AttrsSet.union_list [attributes; properties; (AttrsSet.of_list (Identifier.Map.keys methods))] in
    let field_flag = AttrsSet.is_subset attribute_set ~of_:field_set in
    let method_flag () = Identifier.Map.fold2 call_set methods ~init:true ~f:(fun ~key:_ ~data flag ->
      flag &&  
      (match data with
      | `Both (left, right) ->
        CallSet.fold left ~init:true ~f:(fun flag call_info -> 
          flag &&  
          CallSet.exists right ~f:(fun signature -> 
            (* Log.dump "%a\n ==> \n%a" CallInfo.pp signature CallInfo.pp call_info; *)
            CallInfo.is_more_corresponding ~signature call_info)
        )
      | `Right _ -> true
      | `Left _ -> false
      )
    )
    in


    if field_flag && method_flag ()
    then [key]
    else []

  let calculate_classes ~key t { AttributeStorage.attribute_set; call_set; } =
    let attribute_set = Identifier.Set.fold attribute_set ~init:AttrsSet.empty ~f:(fun acc attr -> AttrsSet.add acc attr) in

    let stub_info = !(OurDomain.our_model).stub_info in

    (* Log.dump "HMM? %b" (OurDomain.StubInfo.is_empty stub_info); *)

    let best_score = 
      Identifier.Map.fold stub_info ~init:(-1.0) ~f:(fun ~key:_ ~data score ->
        (* let should_analysis = 
          match candidate_class with
          | Some cls -> List.exists (successors (Reference.show cls)) ~f:(String.equal (Reference.show key))
          | None -> true
        in *)
        let { StubInfo.attribute_set=stub_attribute_set; call_set=stub_call_set; } = data in

        (* if should_analysis then ( *)
        let field_set = AttrsSet.union_list [stub_attribute_set; (AttrsSet.of_list (Identifier.Map.keys stub_call_set))] in
        let field_flag = AttrsSet.is_subset attribute_set ~of_:field_set in

        (* AttrsSet.iter field_set ~f:(fun f -> Log.dump "FIELD : %s" f); *)
        let iter_stub_info () = Identifier.Map.fold stub_call_set ~init:(-1.0) ~f:(fun ~key:right_key ~data:right score ->
          let calc_method () = Identifier.Map.fold call_set ~init:(false, 0.0) ~f:(fun ~key:left_key ~data:left (flag, score) ->
            if String.equal left_key right_key then (
              let check = 
                CallSet.for_all left ~f:(fun call_info -> 
                  CallSet.exists right ~f:(fun signature -> 
                    (* Log.dump "%a\n ==> \n%a" CallInfo.pp signature CallInfo.pp call_info; *)
                    CallInfo.is_corresponding ~signature call_info
                  )
                )
              in

              if check
              then (
                true,
                CallSet.fold ~init:score left ~f:(fun score call_info -> 
                  CallSet.fold right ~init:score ~f:(fun score signature -> 
                    (* Log.dump "%a\n ==> \n%a" CallInfo.pp signature CallInfo.pp call_info; *)
                    if CallInfo.is_corresponding ~signature call_info
                    then score +. (CallInfo.calculate ~signature call_info)
                    else score
                  )
                )
              )
              else (flag, score)
            )
            else (
              (flag, score)
            )
          )
          in

          let (flag, cur_score) = calc_method () in
          if flag 
          then Float.max score cur_score
          else score
        )
        in


        if field_flag then (
          let cur_score = iter_stub_info () in
          Float.max score cur_score
        )
        else score
        (* ) else (
          candidate_class
        ) *)
      )
    in

    let find_score = 
      match ClassHash.find t key with
      | Some { ClassSummary.class_attributes={ methods; _ }; _ } ->
        Identifier.Map.fold2 call_set methods ~init:0.0 ~f:(fun ~key:_ ~data score ->
          (match data with
          | `Both (left, right) ->
            CallSet.fold ~init:score left ~f:(fun score call_info -> 
              CallSet.fold right ~init:score ~f:(fun score signature -> 
                (* Log.dump "%a\n ==> \n%a" CallInfo.pp signature CallInfo.pp call_info; *)
                if CallInfo.is_corresponding ~signature call_info
                then (
                  score +. (CallInfo.calculate ~signature call_info)
                )
                else (

                  score
                )
              )
            )
          | `Right _ -> score
          | `Left _ -> score
          )
        )
      | None -> 0.0
    in

    let result = Float.(>) find_score best_score in

    (* if not result then
      Log.dump "%.3f %.3f" find_score best_score; *)

    result
    (*
    ClassHash.fold t ~init:[] ~f:(fun ~key ~data:{ ClassSummary.class_attributes={ attributes; properties; methods }; _ } candidate_class ->
      (* let should_analysis = 
        match candidate_class with
        | Some cls -> List.exists (successors (Reference.show cls)) ~f:(String.equal (Reference.show key))
        | None -> true
      in *)

      (* if should_analysis then ( *)
      let field_set = AttrsSet.union_list [attributes; properties; (AttrsSet.of_list (Identifier.Map.keys methods))] in
      let field_flag = AttrsSet.is_subset attribute_set ~of_:field_set in

      let method_flag () = Identifier.Map.fold2 call_set methods ~init:true ~f:(fun ~key:_ ~data flag ->
        flag &&  
        (match data with
        | `Both (left, right) ->
          CallSet.for_all left ~f:(fun call_info -> 
            CallSet.exists right ~f:(fun signature -> 
              (* Log.dump "%a\n ==> \n%a" CallInfo.pp signature CallInfo.pp call_info; *)
              CallInfo.is_corresponding ~signature call_info)
          )
        | `Right _ -> true
        | `Left _ -> false
        )
      )
      in


      if field_flag && method_flag ()
      then key::candidate_class
      else candidate_class
      (* ) else (
        candidate_class
      ) *)
    )*)

  let find_classes_from_attributes ~key ~successors t { AttributeStorage.attribute_set; call_set; } =
    let _ = key, successors in
    let default_attributes = 
      ["add"; "get"; "append"; "extend"; "__getitem__"; "__setitem__"; "update"; "keys"; "values"; "items";     
      ]
      |> List.fold ~init:Identifier.Set.empty ~f:(fun acc t -> Identifier.Set.add acc t)
    in

    let call_attributes = 
      Identifier.Map.keys call_set 
      |> List.fold ~init:Identifier.Set.empty ~f:(fun acc t -> Identifier.Set.add acc t)
    in

    let all_attributes = Identifier.Set.union attribute_set call_attributes in
    let stub_info = !(OurDomain.our_model).stub_info in

    if false (* || true *) then (* For Baseline => True *)
      let attribute_set = Identifier.Set.fold all_attributes ~init:AttrsSet.empty ~f:(fun acc attr -> AttrsSet.add acc attr) in

      let class_set =
        ClassHash.fold t ~init:Reference.Set.empty ~f:(fun ~key ~data:{ ClassSummary.class_attributes={ attributes; properties; methods }; _ } candidate_class ->
        (* let should_analysis = 
          match candidate_class with
          | Some cls -> List.exists (successors (Reference.show cls)) ~f:(String.equal (Reference.show key))
          | None -> true
        in *)

        (* if should_analysis then ( *)
        let field_set = AttrsSet.union_list [attributes; properties; (AttrsSet.of_list (Identifier.Map.keys methods))] in
        let field_flag = AttrsSet.is_subset attribute_set ~of_:field_set in

        let method_flag () = Identifier.Map.fold2 call_set methods ~init:true ~f:(fun ~key:_ ~data flag ->
          flag &&  
          (match data with
          | `Both (left, right) ->
            CallSet.for_all left ~f:(fun call_info -> 
              CallSet.exists right ~f:(fun signature -> 
                (* Log.dump "%a\n ==> \n%a" CallInfo.pp signature CallInfo.pp call_info; *)
                CallInfo.is_corresponding ~signature call_info)
            )
          | `Right _ -> true
          | `Left _ -> false
          )
        )
        in
  
  
        if field_flag && method_flag ()
        then (
          Reference.Set.add candidate_class key
        )
        else candidate_class
        (* ) else (
          candidate_class
        ) *)
      )
      in

      (* if not (Identifier.Map.is_empty call_set) then (
        List.iter more_accurate ~f:(fun c -> Log.dump "%a ==> %a" Expression.pp key Reference.pp c);
      ); *)


      let class_set =
        if Reference.Set.is_empty class_set then
          ClassHash.fold t ~init:Reference.Set.empty ~f:(fun ~key ~data:{ ClassSummary.class_attributes={ attributes; properties; methods }; _ } candidate_class ->
            (* let should_analysis = 
              match candidate_class with
              | Some cls -> List.exists (successors (Reference.show cls)) ~f:(String.equal (Reference.show key))
              | None -> true
            in *)

            (* if should_analysis then ( *)
            let field_set = AttrsSet.union_list [attributes; properties; (AttrsSet.of_list (Identifier.Map.keys methods))] in
            let field_flag = AttrsSet.is_subset attribute_set ~of_:field_set in

            let method_flag () = Identifier.Map.fold2 call_set methods ~init:true ~f:(fun ~key:_ ~data flag ->
              flag &&  
              (match data with
              | `Both (left, right) ->
                CallSet.for_all left ~f:(fun call_info -> 
                  CallSet.exists right ~f:(fun signature -> 
                    (* Log.dump "%a\n ==> \n%a" CallInfo.pp signature CallInfo.pp call_info; *)
                    CallInfo.is_corresponding ~signature call_info)
                )
              | `Right _ -> true
              | `Left _ -> false
              )
            )
            in
      
      
            if field_flag && method_flag ()
            then (
              Reference.Set.add candidate_class key
            )
            else candidate_class
            (* ) else (
              candidate_class
            ) *)
          )
        else
          class_set
      (* if List.is_empty more_accurate then
        ClassHash.fold t ~init:[] ~f:(fun ~key ~data:{ ClassSummary.class_attributes={ attributes; properties; methods }; _ } candidate_class ->
          (* let should_analysis = 
            match candidate_class with
            | Some cls -> List.exists (successors (Reference.show cls)) ~f:(String.equal (Reference.show key))
            | None -> true
          in *)

          (* if should_analysis then (
 *)
          let field_set = AttrsSet.union_list [attributes; properties; (AttrsSet.of_list (Identifier.Map.keys methods))] in
          let field_flag = AttrsSet.is_subset attribute_set ~of_:field_set in
          let method_flag () = Identifier.Map.fold2 call_set methods ~init:true ~f:(fun ~key:_ ~data flag ->
            flag &&  
            (match data with
            | `Both (left, right) ->
              CallSet.for_all left ~f:(fun call_info -> 
                CallSet.exists right ~f:(fun signature -> CallInfo.is_corresponding ~signature call_info)
              )
            | `Right _ -> true
            | `Left _ -> false
            )
          )
          in


          if field_flag && method_flag ()
          then key::candidate_class
          else candidate_class
          (* ) else (
            candidate_class
          ) *)
        )
      else more_accurate *)
      in

      let stub_classes = 
        Identifier.Map.fold stub_info ~init:Identifier.Set.empty ~f:(fun ~key ~data class_set ->
          (* let should_analysis = 
            match candidate_class with
            | Some cls -> List.exists (successors (Reference.show cls)) ~f:(String.equal (Reference.show key))
            | None -> true
          in *)
          let { StubInfo.attribute_set=stub_attribute_set; call_set=stub_call_set; } = data in
          let field_set = AttrsSet.union_list [stub_attribute_set; (AttrsSet.of_list (Identifier.Map.keys stub_call_set))] in
          let field_flag = AttrsSet.is_subset attribute_set ~of_:field_set in


          let iter_stub_info () = Identifier.Map.fold stub_call_set ~init:true ~f:(fun ~key:right_key ~data:right flag ->
            let calc_method () = Identifier.Map.fold call_set ~init:flag ~f:(fun ~key:left_key ~data:left flag ->
              if String.equal left_key right_key then (
                let check = 
                  CallSet.for_all left ~f:(fun call_info -> 
                    CallSet.exists right ~f:(fun signature -> 
                      (* Log.dump "%a\n ==> \n%a" CallInfo.pp signature CallInfo.pp call_info; *)
                      CallInfo.is_corresponding ~signature call_info
                    )
                  )
                in

                if check
                then (
                  flag
                )
                else false
              )
              else (
                flag
              )
            )
            in

            if calc_method () then
              flag
            else
              false
          )
        in

        if field_flag && (iter_stub_info ())
        then 
          Identifier.Set.add class_set key
        else 
          class_set
      )
      in

      let stub_classes = Identifier.Set.fold stub_classes ~init:Reference.Set.empty ~f:(fun acc t -> Reference.Set.add acc (Reference.create t)) in
      let _ = stub_classes in
      Reference.Set.to_list class_set
      (* Reference.Set.to_list (Reference.Set.union class_set stub_classes) *)

    else if Identifier.Set.is_empty (Identifier.Set.diff all_attributes default_attributes)
    then
      []
    else ( 
      
      (* let timer = Timer.start () in *)

      let attribute_set = Identifier.Set.fold all_attributes ~init:AttrsSet.empty ~f:(fun acc attr -> AttrsSet.add acc attr) in

      let class_set, score =
        ClassHash.fold t ~init:(Reference.Set.empty, -1.0) ~f:(fun ~key ~data:{ ClassSummary.class_attributes={ attributes; properties; methods }; _ } (candidate_class, score) ->
          (* let should_analysis = 
            match candidate_class with
            | Some cls -> List.exists (successors (Reference.show cls)) ~f:(String.equal (Reference.show key))
            | None -> true
          in *)

          (* if should_analysis then ( *)
          let field_set = AttrsSet.union_list [attributes; properties; (AttrsSet.of_list (Identifier.Map.keys methods))] in
          let field_flag = AttrsSet.is_subset attribute_set ~of_:field_set in

          let method_flag () = Identifier.Map.fold2 call_set methods ~init:true ~f:(fun ~key:_ ~data flag ->
            flag &&  
            (match data with
            | `Both (left, right) ->
              CallSet.for_all left ~f:(fun call_info -> 
                CallSet.exists right ~f:(fun signature -> 
                  (* Log.dump "%a\n ==> \n%a" CallInfo.pp signature CallInfo.pp call_info; *)
                  CallInfo.is_more_corresponding ~signature call_info)
              )
            | `Right _ -> true
            | `Left _ -> false
            )
          )
          in
    
    
          if field_flag && method_flag ()
          then (
            let cur_score = Identifier.Map.fold2 call_set methods ~init:(0.0) ~f:(fun ~key:_ ~data score ->
              (match data with
              | `Both (left, right) ->
                CallSet.fold left ~init:score ~f:(fun score call_info ->
                  CallSet.fold right ~init:score ~f:(fun score signature -> 
                    (* Log.dump "%a\n ==> \n%a" CallInfo.pp signature CallInfo.pp call_info; *)
                    if CallInfo.is_corresponding ~signature call_info
                    then score +. (CallInfo.calculate ~signature call_info)
                    else score
                  )
                )
              | `Right _ -> score
              | `Left _ -> score
              )
            )
            in

            if Float.(>) cur_score score then
              Reference.Set.singleton key, cur_score
            else if Float.(=) cur_score score then
              (Reference.Set.add candidate_class key, score)
            else
              (candidate_class, score)
          )
          else (candidate_class, score)
          (* ) else (
            candidate_class
          ) *)
        )
      in

      (* let t1 = Timer.stop_in_sec timer in
      let first = class_set in *)

      (* if not (Identifier.Map.is_empty call_set) then (
        List.iter more_accurate ~f:(fun c -> Log.dump "%a ==> %a" Expression.pp key Reference.pp c);
      ); *)


      let class_set, score =
        if false && Reference.Set.is_empty class_set then
          ClassHash.fold t ~init:(Reference.Set.empty, -1.0) ~f:(fun ~key ~data:{ ClassSummary.class_attributes={ attributes; properties; methods }; _ } (candidate_class, score) ->
            (* let should_analysis = 
              match candidate_class with
              | Some cls -> List.exists (successors (Reference.show cls)) ~f:(String.equal (Reference.show key))
              | None -> true
            in *)

            (* if should_analysis then ( *)
            let field_set = AttrsSet.union_list [attributes; properties; (AttrsSet.of_list (Identifier.Map.keys methods))] in
            let field_flag = AttrsSet.is_subset attribute_set ~of_:field_set in

            let method_flag () = Identifier.Map.fold2 call_set methods ~init:true ~f:(fun ~key:_ ~data flag ->
              flag &&  
              (match data with
              | `Both (left, right) ->
                CallSet.for_all left ~f:(fun call_info -> 
                  CallSet.exists right ~f:(fun signature -> 
                    (* Log.dump "%a\n ==> \n%a" CallInfo.pp signature CallInfo.pp call_info; *)
                    CallInfo.is_corresponding ~signature call_info)
                )
              | `Right _ -> true
              | `Left _ -> false
              )
            )
            in
      
      
            if field_flag && method_flag ()
            then (
              let cur_score = Identifier.Map.fold2 call_set methods ~init:(0.0) ~f:(fun ~key:_ ~data score ->
                (match data with
                | `Both (left, right) ->
                  CallSet.fold left ~init:score ~f:(fun score call_info ->
                    CallSet.fold right ~init:score ~f:(fun score signature -> 
                      (* Log.dump "%a\n ==> \n%a" CallInfo.pp signature CallInfo.pp call_info; *)
                      if CallInfo.is_corresponding ~signature call_info
                      then score +. (CallInfo.calculate ~signature call_info)
                      else score
                    )
                  )
                | `Right _ -> score
                | `Left _ -> score
                )
              )
              in

              if Float.(>) cur_score score then
                Reference.Set.singleton key, cur_score
              else if Float.(=) cur_score score then
                (Reference.Set.add candidate_class key, score)
              else
                (candidate_class, score)
            )
            else (candidate_class, score)
            (* ) else (
              candidate_class
            ) *)
          )
        else
          class_set, score
        (* if List.is_empty more_accurate then
          ClassHash.fold t ~init:[] ~f:(fun ~key ~data:{ ClassSummary.class_attributes={ attributes; properties; methods }; _ } candidate_class ->
            (* let should_analysis = 
              match candidate_class with
              | Some cls -> List.exists (successors (Reference.show cls)) ~f:(String.equal (Reference.show key))
              | None -> true
            in *)

            (* if should_analysis then (
  *)
            let field_set = AttrsSet.union_list [attributes; properties; (AttrsSet.of_list (Identifier.Map.keys methods))] in
            let field_flag = AttrsSet.is_subset attribute_set ~of_:field_set in
            let method_flag () = Identifier.Map.fold2 call_set methods ~init:true ~f:(fun ~key:_ ~data flag ->
              flag &&  
              (match data with
              | `Both (left, right) ->
                CallSet.for_all left ~f:(fun call_info -> 
                  CallSet.exists right ~f:(fun signature -> CallInfo.is_corresponding ~signature call_info)
                )
              | `Right _ -> true
              | `Left _ -> false
              )
            )
            in


            if field_flag && method_flag ()
            then key::candidate_class
            else candidate_class
            (* ) else (
              candidate_class
            ) *)
          )
        else more_accurate *)
      in

      (* let t2 = Timer.stop_in_sec timer in
      let second = class_set in *)

      let stub_classes, stub_score = 
        if ReferenceSet.is_empty class_set then (
          Identifier.Set.empty, -1.0
        ) else (
          Identifier.Map.fold stub_info ~init:(Identifier.Set.empty, -1.0) ~f:(fun ~key ~data (class_set, score) ->
            (* let should_analysis = 
              match candidate_class with
              | Some cls -> List.exists (successors (Reference.show cls)) ~f:(String.equal (Reference.show key))
              | None -> true
            in *)
            let { StubInfo.attribute_set=stub_attribute_set; call_set=stub_call_set; } = data in
            let field_set = AttrsSet.union_list [stub_attribute_set; (AttrsSet.of_list (Identifier.Map.keys stub_call_set))] in
            let field_flag = AttrsSet.is_subset attribute_set ~of_:field_set in


            let iter_stub_info () = Identifier.Map.fold stub_call_set ~init:(true, 0.0) ~f:(fun ~key:right_key ~data:right (flag, score) ->
              let calc_method () = Identifier.Map.fold call_set ~init:(flag, score) ~f:(fun ~key:left_key ~data:left (flag, score) ->
                if String.equal left_key right_key then (
                  let check = 
                    CallSet.for_all left ~f:(fun call_info -> 
                      CallSet.exists right ~f:(fun signature -> 
                        (* Log.dump "%a\n ==> \n%a" CallInfo.pp signature CallInfo.pp call_info; *)
                        CallInfo.is_corresponding ~signature call_info
                      )
                    )
                  in

                  if check
                  then (
                    flag,
                    CallSet.fold ~init:score left ~f:(fun score call_info -> 
                      CallSet.fold right ~init:score ~f:(fun score signature -> 
                        (* Log.dump "%a\n ==> \n%a" CallInfo.pp signature CallInfo.pp call_info; *)
                        if CallInfo.is_corresponding ~signature call_info
                        then score +. (CallInfo.calculate ~signature call_info)
                        else score
                      )
                    )
                  )
                  else (false, score)
                )
                else (
                  (flag, score)
                )
              )
              in

              let (calc_flag, cur_score) = calc_method () in
              if calc_flag then
                (flag, cur_score)
              else
                (false, 0.0)
            )
            in

            if field_flag 
            then 
              let (flag, cur_score) = iter_stub_info () in
              if flag then (
                if (Float.(>) score cur_score) then
                  (class_set, score)
                else if (Float.(=) score cur_score) then
                  (Identifier.Set.add class_set key, score)
                else (Identifier.Set.singleton key, cur_score)
              ) else
                (class_set, score)
            else 
              (class_set, score)
          )
        )
      in

      (* let t3 = Timer.stop_in_sec timer in *)

      (* if Float.(>.) t3 0.1 then
        Log.dump "Time : %.3f %.3f %.3f (%i => %i)" t1 t2 t3 (ReferenceSet.length first) (ReferenceSet.length second); *)

      if Float.(>) score stub_score then (
        Reference.Set.to_list class_set
      )
      else if Float.(=) score stub_score then
        if Identifier.Set.length stub_classes = 1 then (
          Reference.Set.to_list class_set
        )
        else
          []
      else
        []
      (* if not (Identifier.Map.is_empty call_set) then (
        List.iter more_accurate ~f:(fun c -> Log.dump "%a ==> %a" Expression.pp key Reference.pp c);
      ); *)
    (*  match x with
      | Some x -> [x]
      | None -> []
      ) *)
    )

  (* let update_seen_path ~function_table t =
    ClassHash.mapi_inplace t ~f:(fun ~key:_ ~data ->
      ClassSummaryResolution.update_seen_path ~function_table data
    )   *)
    
  let filter_used_variable ~class_name ~used_variable final_class_table =
    let final_summary = find_default final_class_table class_name in
    ClassSummaryResolution.filter_used_variable final_summary ~used_variable

  let update_test_passed_used_variable ~class_name ~test_passed_used_variable ~end_define t =
    let class_summary = find_default t class_name in
    let data = ClassSummaryResolution.update_test_passed_used_variable class_summary ~test_passed_used_variable ~end_define in
    ClassHash.set t ~key:class_name ~data

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

      let new_type = 
        match old_type with
        | Unknown -> data
        | _ -> join data old_type
      in

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

  let store_to_return_var_type ?usedef_table ?class_param ?(local=false) ({ signatures; _ } as t) arg_types (store: Refinement.Store.t) =
    
    
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
        if Option.is_some usedef_table then
          if Reference.equal class_param base_reference 
          then return_var_type
          else ReferenceMap.set return_var_type ~key:base_reference ~data:typ 
        else
          if Reference.equal class_param base_reference
          then return_var_type
          else ReferenceMap.set return_var_type ~key:base_reference ~data:typ 
      in
      attribute_fold ~base_reference ~attributes:(unit |> Refinement.Unit.attributes) return_var_type
    in 
    
    let annotation_fold annotation return_var_type =
      Reference.Map.fold ~init:return_var_type ~f:(fun ~key ~data return_var_type ->
        if local || (Reference.is_local key) then
          let key = Reference.delocalize key |> Reference.drop_head in
          let x = unit_fold ~unit:data ~base_reference:key return_var_type in
          x
        else if (not local) && Reference.is_parameter key then
          let x = unit_fold ~unit:data ~base_reference:key return_var_type in
          x
        else
          return_var_type
      ) annotation
    in

    let return_var_type = 
      let x =
      return_var_type
      (* |> annotation_fold store.annotations *)
      |> annotation_fold store.annotations
      |> annotation_fold store.temporary_annotations
      in
      x
    in

    let signatures = Signatures.set_return_var_type signatures arg_types return_var_type in

    FunctionSummary.{ t with signatures; }

  let find_default_type_of_attributes t =
    ClassTableResolution.find_default_type_from_attributes ~key:(Reference.create "str") ~default_type:(OurDomain.ClassAttributes.str_attributes ()) t
    |> (function
    | [t] -> let _ = t in None
    | _ -> None
    )

  let find_class_of_attributes ~successors ~class_table ~func_name ?(debug=false) { usage_attributes; _ } parent_usage_attributes =

    let _ = debug, func_name in
    (* have to make proper filter *)
    let extract_class ~key ~attributes classes =
      let _ = key in
      (* if debug then (
        List.iter classes ~f:(fun c -> Log.dump "BEFORE : %a" Reference.pp c);
      ); *)
      let classes = List.map classes ~f:Reference.show in


      (* Before *)
      (* let filtered_classes =
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
      in *)

      let filtered_classes = 
        if List.length classes = 1 then
          classes
        else
          List.filter classes ~f:(fun cls ->
            let class_successors = cls::(successors cls) in
            List.exists classes ~f:(fun origin -> 
              not (String.equal origin cls) &&
              List.exists class_successors ~f:(String.equal origin)
            )
            |> not  
          )
      in

      (* if debug then
        List.iter filtered_classes ~f:(fun c -> Log.dump "TEST : %s" c); *)
      if false (* || true *) then  (* For Baseline => True *)
        Some (List.map filtered_classes ~f:Reference.create)
      else if List.length filtered_classes > 1 then (
        (* Log.dump "FIND %a" Expression.pp key;
        List.iter classes ~f:(fun c -> Log.dump "BEFORE : %s" c);
        List.iter filtered_classes ~f:(fun c -> Log.dump "TEST : %s" c); *)
        None
      )
      else if List.length filtered_classes = 1 then (
        let _ = attributes in
        let _ = ClassTableResolution.calculate_classes in 
        let class_key = List.nth_exn filtered_classes 0 |> Reference.create in
        Some [class_key]
        (* let class_key = List.nth_exn filtered_classes 0 |> Reference.create in
        (* List.iter filtered_classes ~f:(fun c -> Log.dump "%a OK : %s" Reference.pp key c); *)
        if (* true || *) (ClassTableResolution.calculate_classes ~key:class_key class_table attributes) (* For Baseline : true *)
        then Some class_key
        else (
          (* let call_attributes = 
            Identifier.Map.keys attributes.call_set 
            |> List.fold ~init:Identifier.Set.empty ~f:(fun acc t -> Identifier.Set.add acc t)
          in
          let all_attributes = Identifier.Set.union attributes.attribute_set call_attributes in
          let x = Identifier.Set.fold ~init:"" all_attributes ~f:(fun acc a -> acc ^ ", " ^ a) in
          Log.dump "%a ==> %a (%s) :: %a" Expression.pp key Reference.pp class_key x Reference.pp func_name; *)
          None
        ) *)
      )
      else (
       None
      )
    in
    
    let usage_attributes =
      parent_usage_attributes
      |> AttributeStorage.join usage_attributes
      |> AttributeAnalysis.AttributeStorage.filter_single_class_param ~class_param:"$parameter$self"
    in 
    
    (* if debug then
      Log.dump "GOGO"; *)
    
    let x =
    AttributeStorage.mapi usage_attributes ~f:(fun ~key ~data:attributes -> 
        let _ = key in
        (* if debug then 
          Log.dump "FIND %a" Expression.pp key; *)

        (* Log.dump "FIND %a" Expression.pp key;  *)

        (* let timer = Timer.start () in *)

        let x =
        attributes
        |> ClassTableResolution.find_classes_from_attributes ~key ~successors class_table
        in

        (* let t1 = Timer.stop_in_sec timer in *)

        let x =
            x
            |> extract_class ~key ~attributes
        in
        
        (* let t2 = Timer.stop_in_sec timer in *)
        
        (* if Float.(>.) t2 0.1 then
          Log.dump "%a %.3f %.3f" Expression.pp key t1 t2; *)

        

        x
        |> (function
        | None -> let _ = find_default_type_of_attributes in None (* find_default_type_of_attributes attributes *)
        | Some v -> 
          (* let call_attributes = 
            Identifier.Map.keys attributes.call_set 
            |> List.fold ~init:Identifier.Set.empty ~f:(fun acc t -> Identifier.Set.add acc t)
          in *)
  
          (* let all_attributes = Identifier.Set.union attributes.attribute_set call_attributes in *)
  
          (* if Identifier.Set.length all_attributes <= 2 then (
            let x = Identifier.Set.fold ~init:"" all_attributes ~f:(fun acc a -> acc ^ ", " ^ a) in
            Log.dump "%a ==> %a (%s) :: %a" Expression.pp key Reference.pp v x Reference.pp func_name;
          ); *)
          
          (* Log.dump "%a ==> %a (%a)" Expression.pp key Reference.pp v AttributeStorage.pp_data_set attributes; *) Some v
        
        )
    )
    in

    x |> LocInsensitiveExpMap.filter_map ~f:(fun v -> 
      match v with
      | Some v -> Some v
      | _ -> v  
    )

end

module FunctionTableResolution = struct
  include FunctionTable

  let store_to_return_var_type ?usedef_table ?class_param ?local t func_name arg_types (store: Refinement.Store.t) =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set t ~key:func_name ~data:(FunctionSummaryResolution.store_to_return_var_type ?usedef_table ?class_param ?local func_summary arg_types store)

  let find_class_of_attributes ~successors ~class_table (t: t) func_name parent_usage_attributes =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    let debug = 
      String.is_substring (Reference.show func_name) ~substring:"salt.daemons.flo.core.SaltRaetRouter._process_road_rxmsg"
    in

    (* Log.dump "Check %a..." Reference.pp func_name; *)

    FunctionSummaryResolution.find_class_of_attributes ~successors ~class_table ~debug ~func_name func_summary parent_usage_attributes

  let can_call_in_test ~filtered_used_variable ~end_define t =

    (* Log.dump "HERE? %b" (Reference.Map.is_empty filtered_used_variable); *)

    let rec bfs_call_chain ?(max=3) ~skip_set n call_chain =
      if max = n then
        []
      else (
        let callee_chain = CallChain.get_callee_chain call_chain in
        let after_skip_set = List.fold callee_chain ~init:skip_set ~f:(fun acc callee -> Reference.Set.add acc callee) in
        List.fold callee_chain ~init:[] ~f:(fun acc callee ->
          if Reference.Set.mem skip_set callee then
            acc
          else (
            let callee_inner_call_chain = 
              FunctionHash.find t callee
              >>| FunctionSummary.get_call_chain
              |> Option.value ~default:CallChain.empty
            in

            if CallChain.length callee_inner_call_chain > 100000 then
              acc
            else
              acc@(callee::(bfs_call_chain ~skip_set:after_skip_set (n+1) callee_inner_call_chain))
          )
        )
      )
    in

    let find_call_chain ~start_defines ~defined_defines ~end_define call_list =
      let _, find_end =
        List.fold call_list ~init:(false, false) ~f:(fun (s, e) call ->
          if e then (s, e)
          else (
            if s
            then (
              if Reference.Set.mem defined_defines call
              then (false, e)
              else if Reference.equal end_define call
              then (s, true)
              else (s, e)
            )
            else (
              (Reference.Set.mem start_defines call, e)
            )
          )  
        ) 
      in

      find_end
    in

    let can_call ~start_defines ~defined_defines ~end_define () =
      FunctionHash.existsi t ~f:(fun ~key ~data:{ FunctionSummary.call_chain; _ } ->
        if Reference.is_test key then (

          (* let setup_func = Reference.drop_last key in
          let setup_func = Reference.combine setup_func (Reference.create "setUp") in
          let call_chain =
            Location.Map.set call_chain ~key:(Location.any) ~data:setup_func
          in *)

          let call_list = bfs_call_chain ~skip_set:Reference.Set.empty 0 call_chain in

          (* List.iter call_list ~f:(fun c -> Log.dump "%a" Reference.pp c); *)

          find_call_chain ~start_defines ~defined_defines ~end_define call_list
        ) else (
          false
        )
      )
    in

    Reference.Map.mapi filtered_used_variable ~f:(fun ~key ~data ->
      Type.Map.filteri data ~f:(fun ~key:typ ~data -> 
        let _ = key, typ in 

        let defined_defines, start_defines = data in

        

        (* Reference.Set.iter defined_defines ~f:(fun defined_define -> Log.dump "defined_defines : %a" Reference.pp defined_define);

        Reference.Set.iter start_defines ~f:(fun start_define -> Log.dump "start_defines : %a" Reference.pp start_define);

        Log.dump "end_defined : %a" Reference.pp end_define; *)

        let result = can_call ~start_defines ~defined_defines ~end_define () in

        (* Log.dump "%a, %a ==> %b" Reference.pp key Type.pp typ result; *)

        result
      )
    )

    

end

module OurSummaryResolution = struct
  include OurSummary

  let store_to_return_var_type ?usedef_table ?class_param ?local { function_table; _ } func_name arg_types store = 
    FunctionTableResolution.store_to_return_var_type ?usedef_table ?class_param ?local function_table func_name arg_types store

  let get_type_of_class_attribute ~type_join ~less_or_equal { class_table; function_table; _ } class_name attribute = ClassTableResolution.get_type_of_class_attribute ~type_join ~less_or_equal ~function_table class_table class_name attribute
  
  let get_self_attributes_tree ~type_join { class_table; _ } class_name = ClassTableResolution.get_self_attributes_tree ~type_join class_table class_name

  let get_temp_self_attributes_tree ~type_join { class_table; _ } class_name = ClassTableResolution.get_temp_self_attributes_tree ~type_join class_table class_name

  let add_parent_attributes { class_table; _ } storage class_name class_var =
    (* 이거 짜야 댕 *)
    let filtered_storage = AttributeStorage.filter_by_prefix storage ~prefix:(Reference.create class_var) in
    ClassTableResolution.add_parent_attributes class_table class_name filtered_storage


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

  let find_class_of_attributes ~successors { class_table; function_table; _ } func_name parent_usage_attributes  =
    FunctionTableResolution.find_class_of_attributes ~successors ~class_table function_table func_name parent_usage_attributes

  (* let update_seen_path { class_table; function_table; _ } =
    ClassTableResolution.update_seen_path ~function_table class_table
 *)

  let can_call_in_test ~filtered_used_variable ~end_define { function_table; _ } =
    FunctionTableResolution.can_call_in_test ~filtered_used_variable ~end_define function_table

  let update_test_passed_used_variable ~class_name ~test_passed_used_variable ~end_define { class_table; _ } =
    ClassTableResolution.update_test_passed_used_variable ~class_name ~test_passed_used_variable ~end_define class_table

end

