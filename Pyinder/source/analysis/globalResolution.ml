(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Core
open Pyre
open Ast
open Statement

type t = {
  dependency: SharedMemoryKeys.DependencyKey.registered option;
  annotated_global_environment: AnnotatedGlobalEnvironment.ReadOnly.t;
}

let create ?dependency annotated_global_environment = { annotated_global_environment; dependency }

let annotated_global_environment { annotated_global_environment; _ } = annotated_global_environment

let attribute_resolution resolution =
  annotated_global_environment resolution
  |> AnnotatedGlobalEnvironment.ReadOnly.attribute_resolution


let class_metadata_environment resolution =
  annotated_global_environment resolution
  |> AnnotatedGlobalEnvironment.ReadOnly.class_metadata_environment


let class_hierarchy_environment resolution =
  class_metadata_environment resolution
  |> ClassMetadataEnvironment.ReadOnly.class_hierarchy_environment


let alias_environment resolution =
  ClassHierarchyEnvironment.ReadOnly.alias_environment (class_hierarchy_environment resolution)


let empty_stub_environment resolution =
  alias_environment resolution |> AliasEnvironment.ReadOnly.empty_stub_environment


let unannotated_global_environment resolution =
  alias_environment resolution |> AliasEnvironment.ReadOnly.unannotated_global_environment


let ast_environment resolution =
  unannotated_global_environment resolution |> UnannotatedGlobalEnvironment.ReadOnly.ast_environment


let class_hierarchy ({ dependency; _ } as resolution) =
  ClassHierarchyEnvironment.ReadOnly.class_hierarchy
    ?dependency
    (class_hierarchy_environment resolution)


let is_tracked resolution = ClassHierarchy.contains (class_hierarchy resolution)

let contains_untracked resolution annotation =
  List.exists
    ~f:(fun annotation -> not (is_tracked resolution annotation))
    (Type.elements annotation)


let is_protocol ({ dependency; _ } as resolution) annotation =
  UnannotatedGlobalEnvironment.ReadOnly.is_protocol
    (unannotated_global_environment resolution)
    ?dependency
    annotation


let primitive_name annotation =
  let primitive, _ = Type.split annotation in
  Type.primitive_name primitive


let class_summary ({ dependency; _ } as resolution) annotation =
  primitive_name annotation
  >>= UnannotatedGlobalEnvironment.ReadOnly.get_class_summary
        (unannotated_global_environment resolution)
        ?dependency


let define_body ({ dependency; _ } as resolution) =
  UnannotatedGlobalEnvironment.ReadOnly.get_define_body
    ?dependency
    (unannotated_global_environment resolution)


let function_definition ({ dependency; _ } as resolution) =
  UnannotatedGlobalEnvironment.ReadOnly.get_function_definition
    ?dependency
    (unannotated_global_environment resolution)


let class_metadata ({ dependency; _ } as resolution) annotation =
  primitive_name annotation
  >>= ClassMetadataEnvironment.ReadOnly.get_class_metadata
        ?dependency
        (class_metadata_environment resolution)


let is_suppressed_module ({ dependency; _ } as resolution) reference =
  EmptyStubEnvironment.ReadOnly.from_empty_stub
    ?dependency
    (empty_stub_environment resolution)
    reference


let aliases ({ dependency; _ } as resolution) =
  AliasEnvironment.ReadOnly.get_alias ?dependency (alias_environment resolution)


let base_is_from_placeholder_stub resolution =
  AnnotatedBases.base_is_from_placeholder_stub
    ~aliases:(aliases resolution)
    ~from_empty_stub:(is_suppressed_module resolution)


let module_exists ({ dependency; _ } as resolution) =
  UnannotatedGlobalEnvironment.ReadOnly.module_exists
    ?dependency
    (unannotated_global_environment resolution)


let get_module_metadata ({ dependency; _ } as resolution) =
  UnannotatedGlobalEnvironment.ReadOnly.get_module_metadata
    ?dependency
    (unannotated_global_environment resolution)


let function_definitions ({ dependency; _ } as resolution) reference =
  let unannotated_global_environment = unannotated_global_environment resolution in
  UnannotatedGlobalEnvironment.ReadOnly.get_function_definition
    unannotated_global_environment
    reference
    ?dependency
  >>| FunctionDefinition.all_bodies


let full_order ({ dependency; _ } as resolution) =
  AttributeResolution.ReadOnly.full_order ?dependency (attribute_resolution resolution)


let less_or_equal resolution = full_order resolution |> TypeOrder.always_less_or_equal

let join resolution left right = 
  let order = full_order resolution in
  let x = TypeOrder.join order left right in

  if !Type.element_join then
    Type.element_to_any x
  else
    x
  (* |> Type.narrow_iterable ~max_depth:3 *)

let meet resolution left right = 
  let order = full_order resolution in 
  TypeOrder.meet order left right |> Type.narrow_iterable ~max_depth:3

let widen resolution = 
  full_order resolution |> TypeOrder.widen

let types_are_orderable resolution type0 type1 =
  less_or_equal resolution ~left:type0 ~right:type1
  || less_or_equal resolution ~left:type1 ~right:type0


let is_compatible_with resolution = full_order resolution |> TypeOrder.is_compatible_with

let is_instantiated resolution = ClassHierarchy.is_instantiated (class_hierarchy resolution)

let parse_reference ?(allow_untracked = false) ({ dependency; _ } as resolution) reference =
  let validation =
    if allow_untracked then SharedMemoryKeys.ParseAnnotationKey.NoValidation else ValidatePrimitives
  in
  Expression.from_reference ~location:Location.any reference
  |> AttributeResolution.ReadOnly.parse_annotation
       ?dependency
       ~validation
       (attribute_resolution resolution)


let is_invariance_mismatch resolution ~left ~right =
  match left, right with
  | ( Type.Parametric { name = left_name; parameters = left_parameters },
      Type.Parametric { name = right_name; parameters = right_parameters } )
    when Identifier.equal left_name right_name ->
      let zipped =
        let variances =
          ClassHierarchy.variables (class_hierarchy resolution) left_name
          (* TODO(T47346673): Do this check when list variadics have variance *)
          >>= Type.Variable.all_unary
          >>| List.map ~f:(fun { Type.Variable.Unary.variance; _ } -> variance)
        in
        match variances with
        | Some variances -> (
            match List.zip left_parameters right_parameters with
            | Ok zipped -> (
                match List.zip zipped variances with
                | Ok zipped ->
                    List.map zipped ~f:(fun ((left, right), variance) -> variance, left, right)
                    |> Option.some
                | _ -> None)
            | _ -> None)
        | _ -> None
      in
      let due_to_invariant_variable (variance, left, right) =
        match variance, left, right with
        | Type.Variable.Invariant, Type.Parameter.Single left, Type.Parameter.Single right ->
            less_or_equal resolution ~left ~right
        | _ -> false
      in
      zipped >>| List.exists ~f:due_to_invariant_variable |> Option.value ~default:false
  | _ -> false


let global ({ dependency; _ } as resolution) reference =
  (* TODO (T41143153): We might want to properly support this by unifying attribute lookup logic for
     module and for class *)
  match Reference.last reference with
  | "__doc__"
  | "__file__"
  | "__name__"
  | "__package__" ->
      let annotation = Annotation.create_immutable Type.string in
      Some { AttributeResolution.Global.annotation; undecorated_signature = None; problem = None }
  | "__path__" ->
      let annotation = Type.list Type.string |> Annotation.create_immutable in
      Some { AttributeResolution.Global.annotation; undecorated_signature = None; problem = None }
  | "__dict__" ->
      let annotation =
        Type.dictionary ~key:Type.string ~value:Type.Any |> Annotation.create_immutable
      in
      Some { annotation; undecorated_signature = None; problem = None }
  | _ ->
      AttributeResolution.ReadOnly.get_global
        (attribute_resolution resolution)
        ?dependency
        reference


let attribute_from_class_name
    ~resolution:({ dependency; _ } as resolution)
    ?(transitive = false)
    ?(accessed_through_class = false)
    ?(special_method = false)
    class_name
    ~name
    ~instantiated
  =
  let access = function
    | Some attribute -> Some attribute
    | None -> (
        match
          UnannotatedGlobalEnvironment.ReadOnly.get_class_summary
            (unannotated_global_environment resolution)
            ?dependency
            class_name
        with
        | Some _ ->
            AnnotatedAttribute.create
              ~annotation:Type.Unknown
              ~original_annotation:Type.Unknown
              ~uninstantiated_annotation:(Some Type.Unknown)
              ~abstract:false
              ~async_property:false
              ~class_variable:false
              ~defined:false
              ~initialized:NotInitialized
              ~name
              ~parent:class_name
              ~visibility:ReadWrite
              ~property:false
              ~undecorated_signature:None
              ~problem:None
            |> Option.some
        | None -> None)
  in
  try
    (* Log.dump "START"; *)
    let x =
    AttributeResolution.ReadOnly.attribute
      ~instantiated
      ~transitive
      ~accessed_through_class
      ~special_method
      ~include_generated_attributes:true
      ?dependency
      (attribute_resolution resolution)
      ~attribute_name:name
      class_name
    in
    (* Log.dump "END?"; *)
    x
    |> access
  with
  | ClassHierarchy.Untracked untracked_type ->
      Log.warning
        "Found untracked type `%s` when checking for attribute `%s` of `%s`."
        untracked_type
        name
        class_name;
      None


let attribute_from_annotation ?special_method resolution ~parent:annotation ~name =
  match Type.resolve_class annotation with
  | None -> None
  | Some [] -> None
  | Some [{ instantiated; accessed_through_class; class_name }] ->
      attribute_from_class_name
        ~resolution
        ~transitive:true
        ~instantiated
        ~accessed_through_class
        ~name
        ?special_method
        class_name
      >>= fun attribute -> Option.some_if (AnnotatedAttribute.defined attribute) attribute
  | Some (_ :: _) -> None


let get_typed_dictionary ~resolution:({ dependency; _ } as resolution) =
  AttributeResolution.ReadOnly.get_typed_dictionary (attribute_resolution resolution) ?dependency


let is_typed_dictionary ~resolution:({ dependency; _ } as resolution) annotation =
  Type.primitive_name annotation
  >>| ClassMetadataEnvironment.ReadOnly.is_typed_dictionary
        (class_metadata_environment resolution)
        ?dependency
  |> Option.value ~default:false


let resolved_type = WeakenMutableLiterals.resolved_type

let is_consistent_with ({ dependency; _ } as resolution) ~resolve left right ~expression =
  let comparator =
    AttributeResolution.ReadOnly.constraints_solution_exists
      ?dependency
      (attribute_resolution resolution)
  in

  let left =
    WeakenMutableLiterals.weaken_mutable_literals
      resolve
      ~get_typed_dictionary:(get_typed_dictionary ~resolution)
      ~expression
      ~resolved:left
      ~expected:right
      ~comparator
    |> resolved_type
  in
  comparator ~get_typed_dictionary_override:(fun _ -> None) ~left ~right


let is_transitive_successor ?placeholder_subclass_extends_all resolution ~predecessor ~successor =
  let class_hierarchy = class_hierarchy resolution in
  ClassHierarchy.is_transitive_successor
    ?placeholder_subclass_extends_all
    class_hierarchy
    ~source:predecessor
    ~target:successor


(* There isn't a great way of testing whether a file only contains tests in Python. Due to the
   difficulty of handling nested classes within test cases, etc., we use the heuristic that a class
   which inherits from unittest.TestCase indicates that the entire file is a test file. *)
let source_is_unit_test resolution ~source =
  let is_unittest { Node.value = { Class.name; _ }; _ } =
    try
      is_transitive_successor
        ~placeholder_subclass_extends_all:false
        resolution
        ~predecessor:(Reference.show name)
        ~successor:"unittest.case.TestCase"
    with
    | ClassHierarchy.Untracked _ -> false
  in
  List.exists (Preprocessing.classes source) ~f:is_unittest


let constraints ~resolution:({ dependency; _ } as resolution) =
  AttributeResolution.ReadOnly.constraints ?dependency (attribute_resolution resolution)


let successors ~resolution:({ dependency; _ } as resolution) =
  ClassMetadataEnvironment.ReadOnly.successors ?dependency (class_metadata_environment resolution)


let immediate_parents ~resolution = ClassHierarchy.immediate_parents (class_hierarchy resolution)

let attributes
    ~resolution:({ dependency; _ } as resolution)
    ?(transitive = false)
    ?(accessed_through_class = false)
    ?(include_generated_attributes = true)
    name
  =
  AttributeResolution.ReadOnly.all_attributes
    (attribute_resolution resolution)
    ~transitive
    ~accessed_through_class
    ~include_generated_attributes
    name
    ?dependency


let instantiate_attribute ~resolution:({ dependency; _ } as resolution) ?instantiated =
  AttributeResolution.ReadOnly.instantiate_attribute
    (attribute_resolution resolution)
    ?dependency
    ?instantiated


let metaclass ~resolution:({ dependency; _ } as resolution) =
  AttributeResolution.ReadOnly.metaclass ?dependency (attribute_resolution resolution)


let resolve_mutable_literals ({ dependency; _ } as resolution) =
  AttributeResolution.ReadOnly.resolve_mutable_literals
    ?dependency
    (attribute_resolution resolution)


let resolve_define ~resolution:({ dependency; _ } as resolution) =
  AttributeResolution.ReadOnly.resolve_define ?dependency (attribute_resolution resolution)


let signature_select ~global_resolution:({ dependency; _ } as resolution) ~resolve_with_locals ~arguments ~callable ~self_argument =
  AttributeResolution.ReadOnly.signature_select ?dependency ~resolve_with_locals ~arguments ~callable ~self_argument (attribute_resolution resolution)
  (* |> (function
    | SignatureSelectionTypes.Found { selected_return_annotation } ->
      (match selected_return_annotation with
      | Type.Callable t -> (* TODO : Modify Resolution of callable *)
      (* Log.dump "Before %s... %a" name Type.pp (Callable t); *)
      let type_join = join resolution in
      let final_model = !OurDomain.our_model in
      let callable = OurDomain.OurSummary.get_callable ~type_join final_model t in
      (* Log.dump "After %s... %a" name Type.pp (Callable callable); *)
      SignatureSelectionTypes.Found { selected_return_annotation = (Callable callable) }
      | Parametric { name = "BoundMethod"; parameters = [Single (Callable t); other]} ->
      (* Log.dump "Before %s... %a" name Type.pp (Callable t); *)
      let type_join = join resolution in
      let final_model = !OurDomain.our_model in
      let callable = OurDomain.OurSummary.get_callable ~type_join final_model t in
      (* Log.dump "After %s... %a" name Type.pp (Callable callable); *)
      SignatureSelectionTypes.Found { selected_return_annotation = (Parametric { name = "BoundMethod"; parameters = [Single (Callable callable); other]}) }
      | _ -> SignatureSelectionTypes.Found { selected_return_annotation }
      )
    | t -> t
  ) *)

let callable_to_arg_types ~global_resolution ~self_argument ~(arguments: AttributeResolution.Argument.t list) (callable: Type.Callable.t) =
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
      let arg_resolved = Type.narrow_union ~join:(join global_resolution) ~less_or_equal:(less_or_equal global_resolution) arg.resolved in  
      (s.value, arg_resolved)::acc
    | Positional -> 
      let arg_resolved = Type.narrow_union ~join:(join global_resolution) ~less_or_equal:(less_or_equal global_resolution) arg.resolved in
      (List.nth_exn param_list (idx+revise_index), arg_resolved)::acc
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

  OurDomain.ArgTypes.make_arg_types save_param_type_list

let our_signature_select ~global_resolution:({ dependency; _ } as resolution) ~resolve_with_locals ~arguments ~callable ~self_argument =
  (* let timer = Timer.start () in *)
  let x =
    AttributeResolution.ReadOnly.signature_select ?dependency ~resolve_with_locals ~arguments ~callable ~self_argument (attribute_resolution resolution) 
  in
  (* let sig_time = Timer.stop_in_sec timer in *)
    (* if Float.(>.) sig_time 0.5 then (
      Log.dump "Origin Signature Time %.3f" sig_time;
    ); *)

  (* Log.dump "OK HERE"; *)

  x
  |> (function
    | SignatureSelectionTypes.Found { selected_return_annotation } ->
      (* let timer = Timer.start () in *)
      (match selected_return_annotation with
      | Type.Callable t -> (* TODO : Modify Resolution of callable *)
      (* Log.dump "Before ... %a" Type.pp (Callable t); *)
      
      let join = join resolution in
      let less_or_equal = less_or_equal resolution in
      let final_model = !OurDomain.our_model in
      let arg_types = callable_to_arg_types ~global_resolution:resolution ~self_argument ~arguments callable in
      let callable = OurDomain.OurSummary.get_callable ~join ~less_or_equal ~successors:(successors ~resolution) final_model arg_types t in
      (* Log.dump "After ... %a" Type.pp (Callable callable); *)
      (* let total_time = Timer.stop_in_sec timer in
      if Float.(>.) total_time 0.05 then (
        (* Log.dump "%a +++ %a ===> %a" Type.pp return_type Type.pp prev_type Type.pp selected_return_annotation; *)
        Log.dump "Signature Time %.3f => %.3f" sig_time total_time;
      ); *)

      SignatureSelectionTypes.Found { selected_return_annotation = (Callable callable) }
      | Parametric { name = "BoundMethod"; parameters = [Single (Callable t); other]} ->
      (* Log.dump "Before... %a" Type.pp (Callable t); *)
      let join = join resolution in
      let less_or_equal = less_or_equal resolution in
      let final_model = !OurDomain.our_model in
      let arg_types = callable_to_arg_types ~global_resolution:resolution ~self_argument ~arguments callable in
      let callable = OurDomain.OurSummary.get_callable ~join ~less_or_equal ~successors:(successors ~resolution) final_model arg_types t in
      (* Log.dump "After... %a" Type.pp (Callable callable); *)
      (* let total_time = Timer.stop_in_sec timer in *)
      (* if Float.(>.) total_time 0.05 then (
        (* Log.dump "%a +++ %a ===> %a" Type.pp return_type Type.pp prev_type Type.pp selected_return_annotation; *)
        Log.dump "BoundMethod Time %.3f => %.3f" sig_time total_time;
      ); *)
      SignatureSelectionTypes.Found { selected_return_annotation = (Parametric { name = "BoundMethod"; parameters = [Single (Callable callable); other]}) }
      | _ -> 
        let type_join = join resolution in
        let final_model = !OurDomain.our_model in
        let arg_types = callable_to_arg_types ~global_resolution:resolution ~self_argument ~arguments callable in
        let return_type = OurDomain.OurSummary.get_callable_return_type ~type_join ~successors:(successors ~resolution) final_model arg_types callable in

        (* Log.dump "Before %a" Type.pp selected_return_annotation; *)

        (* let prev_type = selected_return_annotation in *)

        let selected_return_annotation =
          (match return_type, selected_return_annotation with
          | _, Type.Any -> return_type
          | Type.Unknown, _ -> selected_return_annotation
          | _ -> type_join return_type selected_return_annotation
          )
        in

        (* Log.dump "After %a" Type.pp selected_return_annotation; *)

        (* let total_time = Timer.stop_in_sec timer in
        if Float.(>.) total_time 0.1 then (
          (* Log.dump "%a +++ %a ===> %a" Type.pp return_type Type.pp prev_type Type.pp selected_return_annotation; *)
          match callable.kind with
          | Named s -> Log.dump "Select Time (%a) %.3f => %.3f (%a => %a)" Reference.pp s sig_time total_time Type.pp prev_type Type.pp selected_return_annotation;
          | _ -> Log.dump "Select Time (Anonymous) %.3f => %.3f (%a => %a)" sig_time total_time Type.pp prev_type Type.pp selected_return_annotation;
        ); *)
        SignatureSelectionTypes.Found { selected_return_annotation }
      )
    | t -> 
      (* let total_time = Timer.stop_in_sec timer in
        if Float.(>.) total_time 0.1 then (
          (* Log.dump "%a +++ %a ===> %a" Type.pp return_type Type.pp prev_type Type.pp selected_return_annotation; *)
           Log.dump "NotFound Time %.3f => %.3f" sig_time total_time
        ); *)
      (* Log.dump "???"; *)
      t
  )


let legacy_resolve_exports ({ dependency; _ } as resolution) ~reference =
  UnannotatedGlobalEnvironment.ReadOnly.legacy_resolve_exports
    ?dependency
    (unannotated_global_environment resolution)
    reference


let resolve_exports ({ dependency; _ } as resolution) ?from reference =
  UnannotatedGlobalEnvironment.ReadOnly.resolve_exports
    ?dependency
    (unannotated_global_environment resolution)
    ?from
    reference


let check_invalid_type_parameters ({ dependency; _ } as resolution) =
  AttributeResolution.ReadOnly.check_invalid_type_parameters
    (attribute_resolution resolution)
    ?dependency


let variables ?default ({ dependency; _ } as resolution) =
  ClassHierarchyEnvironment.ReadOnly.variables
    ?default
    ?dependency
    (class_hierarchy_environment resolution)


module ConstraintsSet = struct
  include ConstraintsSet

  let add constraints ~new_constraint ~global_resolution =
    TypeOrder.OrderedConstraintsSet.add
      constraints
      ~new_constraint
      ~order:(full_order global_resolution)


  let solve constraints ~global_resolution =
    TypeOrder.OrderedConstraintsSet.solve constraints ~order:(full_order global_resolution)


  module Solution = struct
    include ConstraintsSet.Solution
  end
end

let constraints_solution_exists ({ dependency; _ } as resolution) =
  AttributeResolution.ReadOnly.constraints_solution_exists
    ~get_typed_dictionary_override:(fun _ -> None)
    ?dependency
    (attribute_resolution resolution)


let extract_type_parameters resolution ~source ~target =
  match source with
  | Type.Top
  | Bottom
  | Any ->
      (* TODO (T63159626): These special cases may not make sense. *)
      None
  | _ ->
      ClassHierarchy.variables (class_hierarchy resolution) target
      >>= fun variables ->
      let namespace = Type.Variable.Namespace.create_fresh () in
      List.map variables ~f:(Type.Variable.namespace ~namespace)
      |> Type.Variable.all_unary
      >>= fun unaries ->
      let solve_against =
        List.map unaries ~f:(fun unary -> Type.Parameter.Single (Type.Variable unary))
        |> Type.parametric target
      in
      ConstraintsSet.add
        ConstraintsSet.empty
        ~new_constraint:(LessOrEqual { left = source; right = solve_against })
        ~global_resolution:resolution
      |> ConstraintsSet.solve ~global_resolution:resolution
      >>= fun solution ->
      List.map unaries ~f:(ConstraintsSet.Solution.instantiate_single_variable solution)
      |> Option.all


let type_of_iteration_value ~global_resolution iterator_type =
  match
    extract_type_parameters global_resolution ~target:"typing.Iterable" ~source:iterator_type
  with
  | Some [iteration_type] -> Some iteration_type
  | _ -> None


(* Determine the appropriate type for `yield` expressions in a generator function, based on the
   return annotation. *)
let type_of_generator_send_and_return ~global_resolution generator_type =
  (* First match against Generator *)
  match
    extract_type_parameters global_resolution ~target:"typing.Generator" ~source:generator_type
  with
  | Some [_yield_type; send_type; return_type] -> send_type, return_type
  | _ -> (
      (* Fall back to match against AsyncGenerator. We fall back instead of using an explicit flag
         because, if the user mixes these types up we still ought to resolve their yield expressions
         to reasonable types *)
      match
        extract_type_parameters
          global_resolution
          ~target:"typing.AsyncGenerator"
          ~source:generator_type
      with
      | Some [_yield_type; send_type] -> send_type, Type.none
      | _ when Type.is_unknown generator_type ->
        Type.Unknown, Type.Unknown
      | _ ->
          (* Fall back to Type.none because it's legal to use other annotations like `object` or
             `Iterator` on a generator function, but in those cases the send type is always NoneType *)
          Type.Unknown, Type.Unknown)


let parse_annotation ({ dependency; _ } as resolution) =
  AttributeResolution.ReadOnly.parse_annotation ?dependency (attribute_resolution resolution)


let resolve_literal ({ dependency; _ } as resolution) =
  AttributeResolution.ReadOnly.resolve_literal ?dependency (attribute_resolution resolution)


let parse_as_parameter_specification_instance_annotation ({ dependency; _ } as resolution) =
  AliasEnvironment.ReadOnly.parse_as_parameter_specification_instance_annotation
    (alias_environment resolution)
    ?dependency


let annotation_parser ?(allow_invalid_type_parameters = false) resolution =
  let validation =
    if allow_invalid_type_parameters then
      SharedMemoryKeys.ParseAnnotationKey.ValidatePrimitives
    else
      ValidatePrimitivesAndTypeParameters
  in
  {
    AnnotatedCallable.parse_annotation = parse_annotation ~validation resolution;
    parse_as_parameter_specification_instance_annotation =
      parse_as_parameter_specification_instance_annotation resolution;
  }


let attribute_names
    ~resolution:({ dependency; _ } as resolution)
    ?(transitive = false)
    ?(accessed_through_class = false)
    ?(include_generated_attributes = true)
    ?instantiated:_
    name
  =
  AttributeResolution.ReadOnly.attribute_names
    (attribute_resolution resolution)
    ~transitive
    ~accessed_through_class
    ~include_generated_attributes
    name
    ?dependency


let global_location ({ dependency; _ } as resolution) =
  AnnotatedGlobalEnvironment.ReadOnly.get_global_location
    (annotated_global_environment resolution)
    ?dependency


let class_exists ({ dependency; _ } as resolution) =
  UnannotatedGlobalEnvironment.ReadOnly.class_exists
    (unannotated_global_environment resolution)
    ?dependency


let overrides class_name ~resolution ~name =
  let find_override parent =
    attribute_from_class_name
      ~transitive:false
      ~accessed_through_class:true
      ~name
      parent
      ~resolution
      ~instantiated:(Primitive class_name)
    >>= fun attribute -> Option.some_if (AnnotatedAttribute.defined attribute) attribute
  in
  successors class_name ~resolution |> List.find_map ~f:find_override


let define resolution decorator_name =
  (* Nested function bodies are empty by default. We have to fill them in. *)
  let rec get_function_definition define_name =
    function_definition resolution define_name
    >>| FunctionDefinition.all_bodies
    >>= function
    | [{ Node.value = { Define.body; _ } as define; location }] ->
        let transform_statement = function
          | {
              Node.value = Statement.Define { body = []; signature = { name = define_name; _ }; _ };
              _;
            } as statement ->
              get_function_definition define_name
              >>| (fun define -> { Node.value = Statement.Define define; location })
              |> Option.value ~default:statement
          | statement -> statement
        in
        { define with body = List.map body ~f:transform_statement } |> Option.some
    (* Ignore functions that have overloads. *)
    | _ -> None
  in
  get_function_definition decorator_name


let refine ~global_resolution annotation refined_type =
  let solve_less_or_equal ~left ~right =
    ConstraintsSet.add
      ConstraintsSet.empty
      ~new_constraint:(LessOrEqual { left; right })
      ~global_resolution
    |> ConstraintsSet.solve ~global_resolution
    >>| fun solution -> ConstraintsSet.Solution.instantiate solution left
  in
  let type_less_or_equal = less_or_equal global_resolution in
  Annotation.refine ~type_less_or_equal ~solve_less_or_equal ~refined_type annotation


let rec join_dict_key_value ?key ?value ~global_resolution t =
  match t with
  | Type.Unknown -> t
  | Union t_list -> 
    let before_list = (List.map t_list ~f:(fun t -> join_dict_key_value t ?key ?value ~global_resolution)) in
    let result = Type.Union before_list in
    (*let x = Type.narrow_union result ~join:(join global_resolution) ~less_or_equal:(less_or_equal global_resolution) in
    (match x with
    | Type.Union t_list -> 
      if (List.length before_list) > (List.length t_list)
        then Log.dump "[[ Before : %i ]] => [[ After : %i ]]" (List.length before_list) (List.length t_list);
      ()
    | _ ->
      Log.dump "[[ Before : %i ]] => [[ After : %i ]]" (List.length before_list) 1
    );
    *)
    result
  | OurTypedDictionary { general; typed_dict } ->
    Type.OurTypedDictionary { 
      general=join_dict_key_value general ?key ?value ~global_resolution;
      typed_dict;
    }
  | Parametric { name = "dict"; parameters } -> (
    match parameters with
    | [Single key_parameter; Single value_parameter] ->
      Parametric {
        name = "dict";
        parameters = [
          Single (join global_resolution key_parameter (Option.value key ~default:Type.Bottom));
          Single (join global_resolution value_parameter (Option.value value ~default:Type.Bottom))
        ];
      }
    | _ -> invalid_arg "It is not valid dict"
  )
  | _ -> (*Log.dump "UPDATE???: %a" Type.pp t;*) t