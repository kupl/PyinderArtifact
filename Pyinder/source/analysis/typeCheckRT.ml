(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Core
open Pyre
open Ast
open Expression
open Statement
open TypeCheckUtil

module OurSummaryResolution = OurTypeSet.OurSummaryResolution
module StatementDefine = Define
module Error = AnalysisError

let error_and_location_from_typed_dictionary_mismatch
    { Node.value = mismatch; location = define_location }
  =
  let mismatch =
    match mismatch with
    | WeakenMutableLiterals.FieldTypeMismatch { field_name; expected_type; actual_type; class_name }
      ->
        Error.FieldTypeMismatch { field_name; expected_type; actual_type; class_name }
    | MissingRequiredField { field_name; class_name } ->
        Error.MissingRequiredField { field_name; class_name }
    | UndefinedField { field_name; class_name } -> Error.UndefinedField { field_name; class_name }
  in
  define_location, Error.TypedDictionaryInitializationError mismatch

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


let errors_from_not_found
    ~callable:({ Type.Callable.kind; _ } as callable)
    ~self_argument
    ~reason
    ~global_resolution
    ?original_target
    ?callee_expression
    ~arguments
  =

  let callee =
    match kind with
    | Type.Callable.Named callable -> Some callable
    | _ -> None
  in

  match reason with
  | SignatureSelectionTypes.AbstractClassInstantiation { class_name; abstract_methods } ->
      [
        ( None,
          Error.InvalidClassInstantiation
            (Error.AbstractClassInstantiation { class_name; abstract_methods }) );
      ]
  | CallingParameterVariadicTypeVariable -> [None, Error.NotCallable (Type.Callable callable)]
  | InvalidKeywordArgument { Node.location; value = { expression; annotation } } ->
      [
        ( Some location,
          Error.InvalidArgument
            (Error.Keyword { expression; annotation; require_string_keys = true }) );
      ]
  | InvalidVariableArgument { Node.location; value = { expression; annotation } } ->
      [Some location, Error.InvalidArgument (Error.ConcreteVariable { expression; annotation })]
  | Mismatches mismatches ->
      let convert_to_error mismatch_reason =
        match mismatch_reason with
        | SignatureSelectionTypes.Mismatch mismatch ->
            let { SignatureSelectionTypes.actual; expected; name; position } =
              Node.value mismatch
            in
            let mismatch, name, position, location =
              ( Error.create_mismatch ~resolution:global_resolution ~actual ~expected ~covariant:true,
                name,
                position,
                Node.location mismatch )
            in

            (* Skip when type is TOP *)
            if Type.is_top mismatch.actual then []
            
            else

            let kind =
              let default_expression = Node.create_with_default_location (Expression.Name (Identifier "")) in
              let target_expression =
                (match arguments with
                | Some args -> 
                  (* TODO : should check list length? *)
                  if (position < 1) || (List.length args <= (position-1)) then default_expression
                  else
                    let { AttributeResolution.Argument.expression; _ } = List.nth_exn args (position-1) in 
                    (match expression with
                    | Some exp -> exp
                    | None -> default_expression
                    )
                | None -> default_expression
                )
              in
              let name =
                (
                  match name with
                  | Some name -> Some name
                  | None -> (
                    match callee_expression with
                    | Some { Node.value = Expression.Name name; _ } -> name_to_reference name >>| Reference.show
                    | _ -> None
                  )
                )
              in
              let normal = 
                  Error.IncompatibleParameterTypeWithReference { name; position; callee; reference=target_expression; mismatch }
              in

              (* Log.dump "HERE?? %a ==> %a %a" Expression.pp target_expression Type.pp mismatch.actual Type.pp mismatch.expected; *)
              
              let typed_dictionary_error
                  ~method_name
                  ~position
                  { Type.Record.TypedDictionary.fields; name = typed_dictionary_name }
                =
                if
                  Type.TypedDictionary.is_special_mismatch
                    ~class_name:typed_dictionary_name
                    ~method_name
                    ~position
                    ~total:(Type.TypedDictionary.are_fields_total fields)
                then
                  match actual with
                  | Type.Literal (Type.String (Type.LiteralValue field_name)) ->
                      let required_field_exists =
                        List.exists
                          ~f:(fun { Type.Record.TypedDictionary.name; required; _ } ->
                            String.equal name field_name && required)
                          fields
                      in
                      if required_field_exists then
                        Error.TypedDictionaryInvalidOperation
                          { typed_dictionary_name; field_name; method_name; mismatch }
                      else
                        Error.TypedDictionaryKeyNotFound
                          { typed_dictionary_name; missing_key = field_name }
                  | Type.Primitive "str" ->
                      Error.TypedDictionaryAccessWithNonLiteral
                        (List.map fields ~f:(fun { name; _ } -> name))
                  | _ -> normal
                else
                  (match method_name, arguments with
                  | ( "__setitem__",
                      Some
                        ({
                           AttributeResolution.Argument.expression =
                             Some
                               {
                                 Node.value = Constant (Constant.String { value = field_name; _ });
                                 _;
                               };
                           _;
                         }
                        :: _) ) ->
                      Error.TypedDictionaryInvalidOperation
                        { typed_dictionary_name; field_name; method_name; mismatch }
                  | _ ->  normal
                  )
              in

              let dictionary_error
                  method_name
                =
                  (match method_name, arguments with
                  | ( "__setitem__",
                      Some
                        _ ) ->
                      Error.TypedDictionaryInvalidOperation
                  { typed_dictionary_name="dictionary"; field_name=""; method_name; mismatch }
                | ( "__getitem__",
                    Some
                      _ ) ->
                    Error.TypedDictionaryInvalidOperation
                      { typed_dictionary_name="dictionary"; field_name=""; method_name; mismatch }
                  | _ -> normal
                  )
              in

              let list_error method_name
              =
                (match method_name, arguments with
                | ( "__setitem__",
                    Some
                      _ ) ->
                    Error.TypedDictionaryInvalidOperation
                { typed_dictionary_name="dictionary"; field_name=""; method_name; mismatch }
                | _ -> normal
                )
              in

              match self_argument, callee >>| Reference.as_list with
              | Some self_annotation, Some callee_reference_list
                when is_operator (List.last_exn callee_reference_list) -> (
                  let is_uninverted = Option.equal Type.equal self_argument original_target in
                  let operator_symbol =
                    if is_uninverted then
                      List.last_exn callee_reference_list |> operator_name_to_symbol
                    else
                      List.last_exn callee_reference_list
                      |> inverse_operator
                      >>= operator_name_to_symbol
                  in
                  match operator_symbol, callee_expression >>| Node.value with
                  | Some operator_name, Some Expression.Name (Attribute { special = true; base; _ }) ->
                      let left_operand, right_operand =
                        if is_uninverted then
                          self_annotation, actual
                        else
                          actual, self_annotation
                      in

                      
                      if false || !OurDomain.baseline (* Baseline *)
                      then
                        Error.UnsupportedOperandWithReference
                        (BinaryWithReference { operator_name; left_operand; right_operand; left_reference=target_expression; right_reference=base;})
                      else if (((String.equal operator_name "+") && Type.is_all_list left_operand && Type.is_all_list right_operand)
                        || ((String.equal operator_name "+") && Type.is_all_tuple left_operand && Type.is_all_tuple right_operand)) 
                      then Error.Top
                      else if Type.can_type left_operand || Type.can_type right_operand then
                        Error.Top 
                      else
                        Error.UnsupportedOperandWithReference
                        (BinaryWithReference { operator_name; left_operand; right_operand; left_reference=target_expression; right_reference=base;})
                        (* (match Node.value base with
                        | Expression.Name name 
                        | Call { callee={ Node.value=Expression.Name name; _ }; _} -> 
                          (match name_to_reference name with
                          | Some right_reference (* when not (Reference.equal Reference.empty target_reference) *) -> 
                            Error.UnsupportedOperandWithReference
                            (BinaryWithReference { operator_name; left_operand; right_operand; left_reference=target_reference; right_reference;})
                          | _ -> 
                            Error.UnsupportedOperandWithReference
                            (BinaryWithReference { operator_name; left_operand; right_operand; left_reference=target_reference; right_reference=Reference.create (Expression.show base);})
                          )
                        | Constant _ when not (Reference.equal Reference.empty target_reference) ->
                          Error.UnsupportedOperandWithReference
                          (BinaryWithReference { operator_name; left_operand; right_operand; left_reference=target_reference; right_reference=Reference.empty;})
                        | _ -> 
                          Error.UnsupportedOperandWithReference
                          (BinaryWithReference { operator_name; left_operand; right_operand; left_reference=target_reference; right_reference=Reference.create (Expression.show base);})
                        ) *)

                        (* Error.UnsupportedOperand
                          (Binary { operator_name; left_operand; right_operand }) *)
                  | _ -> normal)
              | Some annotation, Some [_; method_name] when Type.is_dict annotation ->
                (* Log.dump "HERE? %a %s" Type.pp annotation method_name; *)
                dictionary_error method_name
              | Some (Type.Primitive _ as annotation), Some [_; method_name] ->
                  GlobalResolution.get_typed_dictionary ~resolution:global_resolution annotation
                  >>| typed_dictionary_error ~method_name ~position
                  |> Option.value ~default:normal
              
              (* | Some t, Some [_; method_name] when String.equal method_name "sorted" ->
              | Some t, Some [_; method_name] when String.equal method_name "max" ->
              | Some t, Some [_; method_name] when String.equal method_name "min" -> *)
              | Some t, Some [_; method_name] when Type.is_list t ->
                list_error method_name
              | _ -> normal
            in

            
            let callee = Option.value callee ~default:Reference.empty |> Reference.show in
            let t = mismatch.actual in
            let arguments = Option.value arguments ~default:[] in

            let iterable_test t kind = 
              (  
                match t with
                | Type.Union t_list ->
                  if List.for_all t_list ~f:(fun t -> 
                    Type.is_possible_iter t || Type.is_union t || Type.is_any t || Type.is_top t || Type.is_unknown t
                  ) then Error.Top else kind
                | t -> if Type.is_possible_iter t then Error.Top else kind
              )
            in

            let can_iter_test t kind = 
              (  
                match t with
                | Type.Union t_list ->
                  if List.for_all t_list ~f:(fun t -> 
                    Type.is_really_possible_iter t || Type.is_union t || Type.is_any t || Type.is_top t || Type.is_unknown t
                  ) then Error.Top else kind
                | t -> if Type.is_really_possible_iter t then Error.Top else kind
              )
            in

            
            (* let name = Option.value name ~default:"" in   
            Log.dump "%s / %s / %i ==> %a" name callee (List.length arguments) Type.pp t; *)

            let kind = 
              if String.equal callee "len" then 
                iterable_test t kind
              else if String.equal callee "sorted" then
              (
                  if position = 1 then
                    can_iter_test t kind
                  else if position = 2 then
                    (match t with
                    | Callable { implementation; _ } ->
                      if Type.can_none implementation.annotation then
                        kind
                      else
                        Error.Top
                    | _ -> kind
                    )
                    (* (
                      if Type.can_none t then
                        kind
                      else
                        Error.Top
                    ) *)
                  else
                    kind
              )
              else if String.equal callee "max" || String.equal callee "min" then
                (
                  if List.length arguments = 1 then
                    iterable_test t kind
                  else if List.length arguments > 1 && not (Type.can_none t) then (
                    
                    Error.Top
                  )
                  else
                    kind
                )
              else
                kind
            in

            [Some location, kind]
        | MismatchWithUnpackableType { variable; mismatch } ->
            [
              ( None,
                Error.InvalidArgument (VariableArgumentsWithUnpackableType { variable; mismatch }) );
            ]
      in
      List.concat_map mismatches ~f:convert_to_error
  | MissingArgument parameter -> [None, Error.MissingArgument { callee; parameter }]
  | MutuallyRecursiveTypeVariables -> [None, Error.MutuallyRecursiveTypeVariables callee]
  | ProtocolInstantiation class_name ->
      [None, Error.InvalidClassInstantiation (ProtocolInstantiation class_name)]
  | TooManyArguments { expected; provided } ->
      [None, Error.TooManyArguments { callee; expected; provided }]
  | TypedDictionaryInitializationError mismatches ->
      List.map mismatches ~f:(fun mismatch ->
          error_and_location_from_typed_dictionary_mismatch mismatch)
      |> List.map ~f:(fun (location, error) -> Some location, error)
  | UnexpectedKeyword name -> [None, Error.UnexpectedKeyword { callee; name }]
  | MultipleKeyword name -> [None, Error.UnexpectedKeyword { callee; name }]


let rec unpack_callable_and_self_argument ~signature_select ~global_resolution input =
  let get_call_attribute parent =
    GlobalResolution.attribute_from_annotation global_resolution ~parent ~name:"__call__"
    >>| Annotated.Attribute.annotation
    >>| Annotation.annotation
  in
  match input with
  | Type.Callable callable -> Some { TypeOperation.callable; self_argument = None }
  | Type.TypeOperation (Compose (Concrete annotations)) ->
      List.map annotations ~f:(fun input ->
          get_call_attribute input
          (* TODO (T96555096): Fix potential infinite loop *)
          >>= unpack_callable_and_self_argument ~signature_select ~global_resolution)
      |> Option.all
      >>= TypeOperation.TypeOperation.Compose.compose_list ~signature_select
  | Any ->
      Some
        {
          callable =
            {
              kind = Anonymous;
              implementation = { annotation = Type.Unknown; parameters = Undefined };
              overloads = [];
            };
          self_argument = None;
        }
  | Parametric { name = "BoundMethod"; parameters = [Single callable; Single self_argument] } -> (
      let self_argument = Some self_argument in
      match callable with
      | Callable callable -> Some { TypeOperation.callable; self_argument }
      | complex -> (
          (* We do two layers since almost all callable classes have a BoundMethod __call__ which we
             need to unwrap. We can't go arbitrarily deep since it would be possible to loop, and
             its not worth building in a new assumption system just for this. We can't use a
             constraint/protocol solve if we want to extract overloads, leaving us with this *)
          get_call_attribute complex
          >>= get_call_attribute
          >>= function
          | Callable callable -> Some { TypeOperation.callable; self_argument }
          | _ -> None))
  | _ -> None

module TypeCheckRT (Context : OurContext) = struct
  type partitioned = {
    consistent_with_boundary: Type.t;
    not_consistent_with_boundary: Type.t option;
  }

  (* None means the state in unreachable *)
  and t =
    | Unreachable
    | Value of Resolution.t

  let is_reachable t =
    match t with
    | Unreachable -> false
    | Value _ -> true

  let get_resolution t =
    match t with
    | Unreachable -> None
    | Value r -> Some r
    (*
  let top_to_bottom t =
    match t with
    | Value resolution -> Value (Resolution.top_to_bottom resolution)
    | _ -> t
    
  let set_possibleconditions pre post =
    match pre, post with
    | Value preresolution, Value postresolution ->
      Value (Resolution.set_annotation_store postresolution (
        Refinement.Store.remain_new ~old_store:(Resolution.get_annotation_store preresolution) ~new_store:(Resolution.get_annotation_store postresolution)
      ))
    | _ -> Unreachable
    *)

  let pp format = function
    | Unreachable -> Format.fprintf format "  <UNREACHABLE STATE>\n"
    | Value resolution ->
        let global_resolution = Resolution.global_resolution resolution in
        let expected =
          let parser = GlobalResolution.annotation_parser global_resolution in
          let { Node.value = { Define.signature; _ }; _ } = Context.define in
          Annotated.Callable.return_annotation_without_applying_decorators ~signature ~parser
        in
        let errors =
          let error_to_string error =
            let error =
              let lookup reference =
                GlobalResolution.ast_environment global_resolution
                |> fun ast_environment ->
                AstEnvironment.ReadOnly.get_relative ast_environment reference
              in
              Error.instantiate ~show_error_traces:true ~lookup error
            in
            Format.asprintf
              "    %a -> %s"
              Location.WithPath.pp
              (Error.Instantiated.location error)
              (Error.Instantiated.description error)
          in
          Context.error_map
          >>| LocalErrorMap.all_errors
          >>| List.map ~f:error_to_string
          |> Option.value ~default:[]
          |> String.concat ~sep:"\n"
        in
        Format.fprintf
          format
          "  Expected return: %a\n  Resolution:\n%a\n  Errors:\n%s\n"
          Type.pp
          expected
          Resolution.pp
          resolution
          errors


  let show state = Format.asprintf "%a" pp state

  and equal left right =
    match left, right with
    | Unreachable, Unreachable -> true
    | Value left_resolution, Value right_resolution ->
        Resolution.refinements_equal left_resolution right_resolution
    | _, _ -> false


  let create ~resolution = Value resolution

  let unreachable = Unreachable

  let bottom = Unreachable

  let emit_error ~errors ~location ~kind =
    Error.create
      ~location:(Location.with_module ~module_reference:Context.qualifier location)
      ~kind
      ~define:Context.define
    :: errors


  let emit_typed_dictionary_errors ~errors mismatches =
    let emit_error errors mismatch =
      let location, kind = error_and_location_from_typed_dictionary_mismatch mismatch in
      emit_error ~errors ~location ~kind
    in
    List.fold mismatches ~f:emit_error ~init:errors


  let add_invalid_type_parameters_errors ~resolution ~location ~errors annotation =
    let mismatches, annotation =
      GlobalResolution.check_invalid_type_parameters resolution annotation
    in
    (* TODO : is valid? *)
    let annotation =
      Type.any_to_unknown annotation
    in

    let add_error errors mismatch =
      emit_error ~errors ~location ~kind:(Error.InvalidTypeParameters mismatch)
    in
    List.fold mismatches ~f:add_error ~init:errors, annotation


  let get_untracked_annotation_errors ~resolution ~location annotation =
    let add_untracked_errors errors =
      let is_untracked_name class_name =
        match class_name with
        | "..." -> false
        | _ -> not (GlobalResolution.is_tracked resolution class_name)
      in
      let untracked =
        List.filter (Type.elements annotation) ~f:is_untracked_name
        |> List.dedup_and_sort ~compare:String.compare
      in
      List.fold untracked ~init:errors ~f:(fun errors name ->
          emit_error ~errors ~location ~kind:(Error.UndefinedType (Primitive name)))
    in
    let add_literal_value_errors errors =
      (* Literal enum class names will later be parsed as types, so we must validate them when
          checking for untracked annotations. In error messaging, assume these are arbitrary
          non-literal expressions. *)
      let literals =
        let is_literal_enumeration = function
          | Type.Literal (Type.EnumerationMember _) -> true
          | _ -> false
        in
        Type.collect annotation ~predicate:is_literal_enumeration
      in
      let add_literal_error errors literal =
        match literal with
        | Type.Literal
            (Type.EnumerationMember
              { enumeration_type = Type.Primitive enumeration_name; member_name })
          when not (GlobalResolution.is_tracked resolution enumeration_name) ->
            emit_error
              ~errors
              ~location
              ~kind:
                (Error.InvalidType
                    (InvalidLiteral (Reference.create (enumeration_name ^ "." ^ member_name))))
        | _ -> errors
      in
      List.fold literals ~init:errors ~f:add_literal_error
    in
    add_untracked_errors [] |> add_literal_value_errors


  let parse_and_check_annotation
      ?(bind_variables = true)
      ~resolution
      ({ Node.location; _ } as expression)
    =
    let global_resolution = Resolution.global_resolution resolution in
    let check_and_correct_annotation ~resolution ~location ~annotation errors =
      let check_invalid_variables resolution variable =
        if not (Resolution.type_variable_exists resolution ~variable) then
          let origin =
            if Define.is_toplevel (Node.value Context.define) then
              Error.Toplevel
            else if Define.is_class_toplevel (Node.value Context.define) then
              Error.ClassToplevel
            else
              Error.Define
          in
          Error.InvalidTypeVariable { annotation = variable; origin } |> Option.some
        else
          None
      in
      let all_primitives_and_variables_are_valid, errors =
        let errors, no_untracked =
          let untracked_annotation_errors =
            get_untracked_annotation_errors ~resolution:global_resolution ~location annotation
          in
          List.append errors untracked_annotation_errors, List.is_empty untracked_annotation_errors
        in
        let invalid_variable_error_kinds =
          Type.Variable.all_free_variables annotation
          |> List.filter_map ~f:(check_invalid_variables resolution)
        in
        ( no_untracked && List.is_empty invalid_variable_error_kinds,
          List.fold invalid_variable_error_kinds ~init:errors ~f:(fun errors kind ->
              emit_error ~errors ~location ~kind) )
      in
      if all_primitives_and_variables_are_valid then
        add_invalid_type_parameters_errors
          annotation
          ~resolution:global_resolution
          ~location
          ~errors
      else
        errors, Type.Unknown
    in
    let annotation =
      GlobalResolution.parse_annotation ~validation:NoValidation global_resolution expression
    in

    (* Log.dump "HMM? %a" Type.pp annotation; *)

    let errors =
      match annotation with
      | Type.Callable { implementation = { annotation = Type.Top; _ }; _ } ->
          emit_error
            ~errors:[]
            ~location
            ~kind:
              (Error.InvalidType
                  (InvalidType
                    {
                      annotation = Type.Primitive (Expression.show expression);
                      expected = "`Callable[[<parameters>], <return type>]`";
                    }))
      | _ when Type.contains_top annotation ->
          emit_error
            ~errors:[]
            ~location
            ~kind:
              (Error.InvalidType
                  (InvalidType
                    { annotation = Type.Primitive (Expression.show expression); expected = "" }))
      | _ -> []
    in
    let errors, annotation =
      check_and_correct_annotation errors ~resolution ~location ~annotation
    in

    (* Log.dump "HMM22? %a" Type.pp annotation; *)

    let annotation =
      if bind_variables then Type.Variable.mark_all_variables_as_bound annotation else annotation
    in

    errors, annotation


  let resolution = function
    | Unreachable -> None
    | Value resolution -> Some resolution


  let resolution_or_default ~default = function
    | Unreachable -> default
    | Value resolution -> resolution


  let less_or_equal ~left ~right =
    match left, right with
    | Unreachable, _ -> true
    | _, Unreachable -> false
    | Value left_resolution, Value right_resolution ->
        Refinement.Store.less_or_equal_monotone
          ~left:(Resolution.annotation_store left_resolution)
          ~right:(Resolution.annotation_store right_resolution)

  let widening_threshold = 3

  let add_fixpoint_threshold_reached_error () =
    let define = Context.define in
    let { Node.value = define_value; location = define_location } = define in
    match StatementDefine.is_toplevel define_value with
    | true ->
        (* Avoid emitting errors on top-level defines, which are generally unsuppressable. *)
        ()
    | false ->
        let kind =
          let define = StatementDefine.name define_value in
          AnalysisError.AnalysisFailure (FixpointThresholdReached { define })
        in
        let location = Location.with_module ~module_reference:Context.qualifier define_location in
        let error = AnalysisError.create ~location ~kind ~define in
        let statement_key = [%hash: int * int] (Cfg.entry_index, 0) in
        let (_ : unit option) = Context.error_map >>| LocalErrorMap.append ~statement_key ~error in
        ()


  let widen ~previous ~next ~iteration =
    match previous, next with
    | Unreachable, _ -> next
    | _, Unreachable -> previous
    | Value previous_resolution, Value next_resolution ->
        if iteration + 1 >= widening_threshold then
          add_fixpoint_threshold_reached_error ();
        Value
        (Resolution.outer_widen_refinements
              ~iteration
              ~widening_threshold
              previous_resolution
              next_resolution)
        (*
          (Resolution.outer_widen_refinements
              ~iteration
              ~widening_threshold
              previous_resolution
              next_resolution)
        *)


  let join left right = 
    widen ~previous:left ~next:right ~iteration:0

  (*
  let widen_possible ~previous ~next ~iteration =
    match previous, next with
    | Unreachable, _ -> next
    | _, Unreachable -> previous
    | Value previous_resolution, Value next_resolution ->
        if iteration + 1 >= widening_threshold then
          add_fixpoint_threshold_reached_error ();
        Value
          (Resolution.widen_with_merge_refinements
              ~iteration
              ~widening_threshold
              previous_resolution
              next_resolution)

  let join_possible left right = widen_possible ~previous:left ~next:right ~iteration:0

  let update_possible prev current func_name =
    match prev, current with
    | _, Unreachable -> Unreachable
    | Unreachable, Value current_resolution ->
      let current_annotation = Resolution.get_annotation_store current_resolution in
      let update_annotation = Refinement.Store.update_from_top_to_bottom current_annotation in
      let global_resolution = Resolution.global_resolution current_resolution in
      
      let our_model = OurTypeSet.select_our_model func_name in
      let current_possibleannotation = OurTypeSet.OurSummary.get_possible_condition our_model func_name in
      let update_annotation = Refinement.Store.join_with_merge ~global_resolution update_annotation current_possibleannotation in
      let update_resolution = Resolution.set_annotation_store current_resolution update_annotation in
      
      Value update_resolution
    | Value prev_resolution, Value current_resolution ->
      let prev_annotation = Resolution.get_annotation_store prev_resolution in
      let current_annotation = Resolution.get_annotation_store current_resolution in
      let update_prev_annotation = Refinement.Store.update_from_top_to_bottom prev_annotation in

      (*Log.dump ">>> Anno >>> \n%a \n%a" Refinement.Store.pp prev_annotation Refinement.Store.pp update_prev_annotation;*)

      let update_current_annotation = Refinement.Store.update_from_top_to_bottom current_annotation in
      let update_annotation = Refinement.Store.update_possible ~global_resolution:(Resolution.global_resolution current_resolution) update_prev_annotation update_current_annotation in
      let global_resolution = Resolution.global_resolution current_resolution in
      let our_model = OurTypeSet.select_our_model func_name in
      let current_possibleannotation = OurTypeSet.OurSummary.get_possible_condition our_model func_name in
      let update_annotation = Refinement.Store.join_with_merge ~global_resolution update_annotation current_possibleannotation in
      let update_resolution = Resolution.set_annotation_store current_resolution update_annotation in
      Value update_resolution
  *)


  module Resolved = struct
    type base =
      | Class of Type.t
      | Instance of Type.t
      | Super of Type.t

    type t = {
      resolution: Resolution.t;
      errors: Error.t list;
      resolved: Type.t;
      resolved_annotation: Annotation.t option;
      base: base option;
    }

    let resolved_base_type = function
      | Some (Class base_type)
      | Some (Instance base_type)
      | Some (Super base_type) ->
          Some base_type
      | None -> None
  end

  module Callee = struct
    type base = {
      expression: Expression.t;
      resolved_base: Type.t;
    }

    type attribute = {
      name: Identifier.t;
      resolved: Type.t;
    }

    type callee_attribute = {
      base: base;
      attribute: attribute;
      expression: Expression.t;
    }

    type t =
      | Attribute of callee_attribute
      | NonAttribute of {
          expression: Expression.t;
          resolved: Type.t;
        }

    let resolved = function
      | Attribute { attribute = { resolved; _ }; _ }
      | NonAttribute { resolved; _ } ->
          resolved
    
(*     let update_resolved callee to_type =
      match callee with
      | Attribute ({ attribute = inner; _ } as t)-> 
        Attribute { t with attribute= { inner with resolved=to_type; }; }
        
      | NonAttribute t -> 
        NonAttribute { t with resolved = to_type; } *)

    let to_any_resolved = function
      | Attribute ({ attribute = { resolved; _ } as inner; _ } as t)-> 
        Attribute { t with attribute= { inner with resolved=if Type.can_unknown resolved then Type.Any else resolved; }; }
        
      | NonAttribute ({ resolved; _ } as t)-> 
        NonAttribute { t with resolved = if Type.can_unknown resolved then Type.Any else resolved;}

    let expression = function
      | Attribute { expression; _ }
      | NonAttribute { expression; _ } ->
          expression

    let get_base = function
      | Attribute { base={ expression; _ }; _ }
      | NonAttribute { expression; _ } -> expression
  end

  module CallableApplicationData = struct
    type ('return_annotation, 'arguments) callable_data = {
      callable: TypeOperation.callable_and_self_argument;
      arguments: 'arguments;
      is_inverted_operator: bool;
      selected_return_annotation: 'return_annotation;
    }

    type ('return_annotation, 'arguments) t =
      | KnownCallable of ('return_annotation, 'arguments) callable_data
      | UnknownCallableAttribute of {
          callable_attribute: Callee.callee_attribute;
          arguments: 'arguments;
        }

    let unknown_callable_attribute_before_application callable_attribute =
      UnknownCallableAttribute { callable_attribute; arguments = () }


    let known_callable_before_application callable =
      KnownCallable
        { callable; is_inverted_operator = false; arguments = (); selected_return_annotation = () }
  end

  let type_of_signature ~resolution signature =
    let global_resolution = Resolution.global_resolution resolution in
    match
      GlobalResolution.resolve_define
        ~resolution:global_resolution
        ~implementation:(Some signature)
        ~overloads:[]
    with
    | { decorated = Ok (Type.Callable callable); _ } ->
        Type.Callable { callable with kind = Anonymous }
    | { decorated = Ok other; _ } -> other
    | { decorated = Error _; _ } -> Any


  let type_of_parent ~global_resolution parent =
    let parent_name = Reference.show parent in
    let parent_type = Type.Primitive parent_name in
    let variables = GlobalResolution.variables global_resolution parent_name in
    match variables with
    | None
    | Some [] ->
        parent_type
    | Some variables ->
        List.map variables ~f:Type.Variable.to_parameter |> Type.parametric parent_name
    | exception _ -> parent_type


  let instantiate_path ~global_resolution location =
    let ast_environment = GlobalResolution.ast_environment global_resolution in
    let location = Location.with_module ~module_reference:Context.qualifier location in
    Location.WithModule.instantiate
      ~lookup:(AstEnvironment.ReadOnly.get_relative ast_environment)
      location


  let define_signature =
    let { Node.value = { Define.signature; _ }; _ } = Context.define in
    signature


  let return_annotation ~global_resolution =
    let signature = define_signature in
    let annotation : Type.t =
      let parser = GlobalResolution.annotation_parser global_resolution in
      Annotated.Callable.return_annotation_without_applying_decorators ~signature ~parser
    in
    let annotation =
      match annotation with
      | Type.Parametric { name = "typing.TypeGuard" | "typing_extensions.TypeGuard"; _ } ->
          Type.bool
      | _ when signature.async && not signature.generator ->
          Type.coroutine_value annotation |> Option.value ~default:Type.Unknown
      | _ -> annotation
    in
    Type.Variable.mark_all_variables_as_bound annotation


  let check_attribute ~(class_origin: Error.class_origin) attr =
    match class_origin with
    | ClassType (Type.Primitive t) ->
      OurDomain.OurSummary.check_attr ~attr !OurDomain.our_model (Reference.create t)
    | ClassInUnion { unions; index; } ->
      (match List.nth unions index with
      | Some (Type.Primitive t) ->
        OurDomain.OurSummary.check_attr ~attr !OurDomain.our_model (Reference.create t)
      | _ -> false
      )
    | _ -> false


  let rec validate_return expression ~resolution ~at_resolution ~errors ~location ~actual ~is_implicit =
    let global_resolution = Resolution.global_resolution resolution in
    let { Node.location = define_location; value = define } = Context.define in
    let { Define.Signature.async; generator; return_annotation = return_annotation_expression; _ } =
      define.signature
    in
    let return_annotation = return_annotation ~global_resolution in
    (* We weaken type inference of mutable literals for assignments and returns to get around the
        invariance of containers when we can prove that casting to a supertype is safe. *)
    let actual =
      GlobalResolution.resolve_mutable_literals
        global_resolution
        ~resolve:(resolve_expression_type ~resolution ~at_resolution)
        ~expression
        ~resolved:actual
        ~expected:return_annotation
    in
    let check_incompatible_return actual errors =
      if
        Define.has_return_annotation define
        && (not
              (GlobalResolution.constraints_solution_exists
                  global_resolution
                  ~left:actual
                  ~right:return_annotation))
        && (not (Define.is_abstract_method define))
        && (not (Define.is_overloaded_function define))
        && (not (Type.is_none actual && async && generator))
        && not (Type.is_none actual && Type.is_noreturn return_annotation)
      then
        let rec check_unimplemented = function
          | [
              { Node.value = Statement.Pass; _ };
              { Node.value = Statement.Return { Return.expression = None; _ }; _ };
            ] ->
              true
          | {
              Node.value =
                Statement.Expression { Node.value = Expression.Constant (Constant.String _); _ };
              _;
            }
            :: tail ->
              check_unimplemented tail
          | _ -> false
        in

        let default_expression = Node.create_with_default_location (Expression.Name (Identifier "")) in
        let reference_exp =
          match expression with
          | Some expression -> expression
          | _ -> default_expression
        in

        emit_error
          ~errors
          ~location
          ~kind:
            (Error.IncompatibleReturnTypeWithExpression
                {
                  mismatch =
                    Error.create_mismatch
                      ~resolution:global_resolution
                      ~actual
                      ~expected:return_annotation
                      ~covariant:true;
                  is_implicit;
                  is_unimplemented = check_unimplemented define.body;
                  reference=reference_exp;
                  define_location;
                })
      else
        errors
    in
    let check_missing_return actual errors =
      let contains_literal_any =
        return_annotation_expression >>| Type.expression_contains_any |> Option.value ~default:false
      in
      if
        (not (Define.has_return_annotation define))
        || (contains_literal_any && Type.contains_prohibited_any return_annotation)
      then
        let given_annotation =
          Option.some_if (Define.has_return_annotation define) return_annotation
        in
        emit_error
          ~errors
          ~location:define_location
          ~kind:
            (Error.MissingReturnAnnotation
                {
                  name = Reference.create "$return_annotation";
                  annotation = Some actual;
                  given_annotation;
                  evidence_locations = [instantiate_path ~global_resolution location];
                  thrown_at_source = true;
                })
      else
        errors
    in
    match actual with
    | { resolved = actual; typed_dictionary_errors = [] } ->
        check_incompatible_return actual errors |> check_missing_return actual
    | { typed_dictionary_errors; _ } -> emit_typed_dictionary_errors ~errors typed_dictionary_errors

  and check_empty_constant expression =
    match expression with
    | Expression.Constant Constant.(False | NoneLiteral)
    | Expression.Constant (Constant.Integer 0)
    | Expression.Constant (Constant.Float 0.0)
    | Expression.Constant (Constant.Complex 0.0)
    | Expression.Constant (Constant.String { StringLiteral.value = ""; _ })
    | Expression.List []
    | Expression.Tuple []
    | Expression.Dictionary { Dictionary.entries = []; keywords = [] }
      -> true
    | _ -> false

  and forward_expression ~resolution ~at_resolution ({ Node.location; value } as expression) =
    (* let { StatementDefine.Signature.name=define_name; _ } = define_signature in *)
    (*let timer = Timer.start () in *)
    
  
    let _ = expression in
    (* if String.is_substring (Reference.show define_name) ~substring:"wrapper"
      then (
        Log.dump "Expression %a" Expression.pp expression;
      ); *)

      (* Log.dump "Expression %a" Expression.pp expression; *)

    let global_resolution = Resolution.global_resolution resolution in
    let forward_entry ~resolution ~errors ~entry:{ Dictionary.Entry.key; value } =
      let { Resolved.resolution; resolved = key_resolved; errors = key_errors; _ } =
        forward_expression ~resolution ~at_resolution key
      in
      let { Resolved.resolution; resolved = value_resolved; errors = value_errors; _ } =
        forward_expression ~resolution ~at_resolution value
      in
      ( Type.weaken_literals key_resolved,
        Type.weaken_literals value_resolved,
        resolution,
        List.concat [key_errors; value_errors; errors] )
    in
    let forward_generator
        ~resolution
        ~errors
        ~generator:({ Comprehension.Generator.conditions; _ } as generator)
      =
      (* Propagate the target type information. *)
      let resolution, errors =
        let iterator_resolution, iterator_errors =
          let post_resolution, errors =
            let { Assign.target; annotation; value } = Statement.generator_assignment generator in
            forward_assignment ~resolution ~at_resolution ~location ~target ~annotation ~value
          in
          resolution_or_default post_resolution ~default:resolution, errors
        in
        let iterator_errors =
          (* Don't throw Incompatible Variable errors on the generated iterator assign; we are
              temporarily minting a variable in a new scope and old annotations should be ignored. *)
          let is_not_assignment_error = function
            | { Error.kind = Error.IncompatibleVariableType _; _ } -> false
            | _ -> true
          in
          List.filter ~f:is_not_assignment_error iterator_errors
        in
        (* We want the resolution in the iterator assignment -- they will become useful in
            `forward_comprehension`. Don't worry about annotation store pollutions as we will throw
            away generator-local variables there. *)
        iterator_resolution, List.append iterator_errors errors
      in
      List.fold conditions ~init:(resolution, errors) ~f:(fun (resolution, errors) condition ->
          let resolution, new_errors =
            let post_resolution, errors = forward_assert ~resolution ~at_resolution condition in
            resolution_or_default post_resolution ~default:resolution, errors
          in
          resolution, List.append new_errors errors)
    in
    let forward_comprehension ~resolution ~errors ~element ~generators =
      let resolved, errors =
        List.fold
          generators
          ~f:(fun (resolution, errors) generator ->
            forward_generator ~resolution ~errors ~generator)
          ~init:(resolution, errors)
        |> fun (resolution, errors) ->
        let { Resolved.resolved; errors = element_errors; _ } =
          forward_expression ~resolution ~at_resolution element
        in
        resolved, List.append element_errors errors
      in
      (* Discard generator-local variables. *)
      {
        Resolved.resolution;
        resolved = Type.weaken_literals resolved;
        resolved_annotation = None;
        base = None;
        errors;
      }
    in
    let forward_elements ~resolution ~errors ~elements =
      let forward_element { Resolved.resolution; resolved; errors; _ } expression =
        match Node.value expression with
        | Expression.Starred (Starred.Once expression) ->
            let { Resolved.resolution; resolved = new_resolved; errors = new_errors; _ } =
              forward_expression ~resolution ~at_resolution expression
            in
            let parameter =
              new_resolved
              |> GlobalResolution.type_of_iteration_value ~global_resolution
              |> Option.value ~default:Type.Unknown
            in
            {
              Resolved.resolution;
              resolved = GlobalResolution.join global_resolution resolved parameter;
              errors = List.append new_errors errors;
              resolved_annotation = None;
              base = None;
            }
        | _ ->
            let { Resolved.resolution; resolved = new_resolved; errors = new_errors; _ } =
              forward_expression ~resolution ~at_resolution expression
            in
            
            {
              resolution;
              resolved = GlobalResolution.join global_resolution resolved new_resolved;
              errors = List.append new_errors errors;
              resolved_annotation = None;
              base = None;
            }
      in
      let correct_bottom { Resolved.resolution; resolved; errors; _ } =
        let resolved =
          if Type.is_unbound resolved then
            Type.variable "_T" |> Type.Variable.mark_all_free_variables_as_escaped
          else if Type.is_top resolved then
            Type.Unknown
          else
            resolved
        in
        (* Log.dump "%a => %a" Expression.pp expression Type.pp resolved; *)
        { Resolved.resolution; errors; resolved; resolved_annotation = None; base = None }
      in
      List.fold
        elements
        ~init:
          {
            Resolved.resolution;
            errors;
            resolved = Type.Bottom;
            resolved_annotation = None;
            base = None;
          }
        ~f:forward_element
      |> (fun { Resolved.resolution; errors; resolved; _ } ->
            {
              Resolved.resolution;
              errors;
              resolved = Type.weaken_literals resolved;
              resolved_annotation = None;
              base = None;
            })
      |> correct_bottom
    in
    let forward_reference ~resolution ~errors referencea =
      
      
      let reference = GlobalResolution.legacy_resolve_exports global_resolution ~reference:referencea in
      (* Log.dump "FIND %a" Reference.pp reference; *)
      (* Log.dump "%a" Resolution.pp resolution; *)
      let annotation =
        let local_annotation = Resolution.get_local resolution ~reference in
        match local_annotation, Reference.prefix reference with
        | Some annotation, _ -> 

          
          (* Log.dump "HMM... %a" Annotation.pp annotation; *)
          let new_annotation = annotation in
          
          (* let new_annotation =
            (match Annotation.annotation annotation with
              | Callable t -> (* TODO : Modify Resolution of callable *)
              (* Log.dump "Before %s... %a" name Type.pp (Callable t); *)
              let type_join = GlobalResolution.join global_resolution in
              let final_model = !OurDomain.our_model in
              let callable = OurDomain.OurSummary.get_callable ~type_join final_model t in
              let annotation = Annotation.create_mutable (Callable callable) in
              annotation
              | Parametric { name = "BoundMethod"; parameters = [Single (Callable t); other]} ->
                (* Log.dump "Before %s... %a" name Type.pp (Callable t); *)
                let type_join = GlobalResolution.join global_resolution in
                let final_model = !OurDomain.our_model in
                let callable = OurDomain.OurSummary.get_callable ~type_join final_model t in
                (* Log.dump "After %s... %a" name Type.pp (Callable callable); *)
                let annotation = Annotation.create_mutable (Parametric { name = "BoundMethod"; parameters = [Single (Callable callable); other]}) in
                annotation
              | _ -> annotation
            )
          in *)

          (* Log.dump "??? %a ==> %a" Reference.pp reference Annotation.pp annotation; *)

          Some new_annotation
        | None, Some qualifier -> (
          
            (* Fallback to use a __getattr__ callable as defined by PEP 484. *)
            let getattr =
              Resolution.get_local
                resolution
                ~reference:(Reference.create ~prefix:qualifier "__getattr__")
              >>| Annotation.annotation
            in
            let correct_getattr_arity signature =
              Type.Callable.Overload.parameters signature
              >>| (fun parameters -> List.length parameters == 1)
              |> Option.value ~default:false
            in
            let create_annotation signature =
              Annotation.create_immutable
                ~original:(Some Type.Unknown)
                (Type.Callable.Overload.return_annotation signature)
            in
            
            

            match getattr with
            | Some (Callable { overloads = [signature]; _ }) when correct_getattr_arity signature ->
              
                Some (create_annotation signature)
            | Some (Callable { implementation = signature; _ }) when correct_getattr_arity signature
              ->
                

                Some (create_annotation signature)
            | _ -> None)
        | _ -> None
      in

      match annotation with
      | Some annotation ->
        
          {
            Resolved.resolution;
            errors;
            resolved = Annotation.annotation annotation;
            resolved_annotation = Some annotation;
            base = None;
          }
      | None -> 

        (
          match GlobalResolution.module_exists global_resolution reference with
          | false when not (GlobalResolution.is_suppressed_module global_resolution reference) ->
              let errors =
                match Reference.prefix reference with
                | Some qualifier when not (Reference.is_empty qualifier) ->
                    if GlobalResolution.module_exists global_resolution qualifier then
                      let origin =
                        let ast_environment = GlobalResolution.ast_environment global_resolution in
                        match AstEnvironment.ReadOnly.get_module_path ast_environment qualifier with
                        | Some module_path -> Error.ExplicitModule module_path
                        | None -> Error.ImplicitModule qualifier
                      in

                      let expression =
                        Node.create_with_default_location (Expression.Name (create_name_from_reference_without_location (Reference.drop_last reference)))
                      in

                      emit_error
                        ~errors
                        ~location
                        ~kind:
                          (Error.UndefinedAttributeWithReference
                              { reference=expression; attribute = Reference.last reference; origin = Error.Module origin })
                    else
                      errors
                | _ -> errors
              in

              let { StatementDefine.Signature.parent; _ } = define_signature in
              let type_ = 
              (match parent with
              | Some parent ->
                let file_name = Reference.delocalize parent |> Reference.drop_last in
                
                let var = Reference.delocalize reference |> Reference.last in
                let t = OurDomain.OurSummary.get_module_var_type !OurDomain.our_model file_name var in 
                (* Log.dump "??? %a . %s = > %a" Reference.pp file_name var Type.pp t; *)
                t
              | _ -> Type.Unknown
              )
              
              in
              { resolution; errors; resolved = type_; resolved_annotation = None; base = None }
          | _ ->
              
              { resolution; errors; resolved = Type.Unknown; resolved_annotation = None; base = None })
    in
    let resolve_attribute_access
        ~base_resolved:
          { Resolved.resolution; errors; resolved = resolved_base; base = super_base; _ }
        ~base
        ~special
        ~attribute
        ~has_default
      =
      
      
      (* let { StatementDefine.Signature.name=define_name; _ } = define_signature in *)

      let name = Name.Attribute { base; special; attribute } in
      let reference = name_to_reference name in
      let name_expression = name in

      
      
      let access_as_attribute () =
        
        let find_attribute ({ Type.instantiated; accessed_through_class; class_name } as class_data)
          =
          let name = attribute in
          (* Log.dump "OH.. %a => %a" Name.pp name_expression Type.pp instantiated;  *)
          match
            GlobalResolution.attribute_from_class_name
              class_name
              ~transitive:true
              ~accessed_through_class
              ~special_method:special
              ~resolution:global_resolution
              ~name
              ~instantiated
          with
          | Some attribute ->
            
              let attribute =
                if not (Annotated.Attribute.defined attribute) then
                  Resolution.fallback_attribute
                    class_name
                    ~instantiated:(Some resolved_base)
                    ~accessed_through_class
                    ~resolution
                    ~name
                  |> Option.value ~default:attribute
                else
                  attribute
              in

              let undefined_target =
                
                if Annotated.Attribute.defined attribute then (
                  None
                )
                else (
                  (* match Resolution.get_local_with_attributes ~name:name_expression resolution with
                  | Some _ -> None
                  | _ ->  *)Some instantiated
                )
              in

              (* Collect @property's in the call graph. *)
              Some (class_data, attribute, undefined_target)
          | None -> None
        in
        let module_path_of_parent_module class_type =
          let ast_environment = GlobalResolution.ast_environment global_resolution in
          GlobalResolution.class_summary global_resolution class_type
          >>| Node.value
          >>= fun { ClassSummary.qualifier; _ } ->
          AstEnvironment.ReadOnly.get_module_path ast_environment qualifier
        in

      

        match Type.resolve_class resolved_base >>| List.map ~f:find_attribute >>= Option.all with
        | None ->
            let errors, resolution =
              if has_default then
                errors, resolution
              else
                let errors =
                  let skip_error = check_attribute ~class_origin:(ClassType resolved_base) attribute in

                  if skip_error then
                    errors
                  else (
                    emit_error
                      ~errors
                      ~location
                      ~kind:
                        (Error.UndefinedAttributeWithReference
                            {
                              reference=base;
                              attribute;
                              origin =
                                Error.Class
                                  {
                                    class_origin = ClassType resolved_base;
                                    parent_module_path = module_path_of_parent_module resolved_base;
                                  };
                            })
                  )
                in
                let resolution =
                  (* TODO: have to add attribute in resolution? *)
                  (*
                  Log.dump "Base : %a / Attr : %s" Expression.pp base attribute;
                  *)
                  resolution
                in
                errors, resolution
            in
            {
              Resolved.resolution;
              errors;
              resolved = Type.Unknown;
              resolved_annotation = None;
              base = None;
            }
        | Some [] ->
            {
              Resolved.resolution;
              errors;
              resolved = Type.Unknown;
              resolved_annotation = None;
              base = None;
            }
        | Some (_ :: _ as attribute_info) ->
            let name = attribute in
            let class_datas, attributes, _ = List.unzip3 attribute_info in
            let head_annotation, tail_annotations, resolution =

            (* Log.dump "FIND %s.%s" (Expression.show base) name;  *)

              let (rev_annotations, resolution) = attributes |> List.foldi ~init:([], resolution) ~f:(fun i (acc, resolution) attribute -> 
                let annotation = Annotated.Attribute.annotation attribute in
                (* Log.dump "??? %s => %b" (Annotated.Attribute.name attribute) (Annotated.Attribute.property attribute); *)

                
                let new_annotation, resolution =
                    let class_data = List.nth_exn class_datas i in
                    match Annotation.annotation annotation with
                    | Type.Top | Unknown | Any when NamedTuple.is_named_tuple ~global_resolution ~annotation:(class_data.instantiated) ->
                      let get_local_type = 
                        Resolution.get_local_with_attributes ~name:name_expression resolution 
                        |> Option.value ~default:(Annotation.create_mutable Type.Unknown)
                      in
                      (match Annotation.annotation get_local_type with
                      | Type.Top | Unknown | Any -> 
                        let final_model = !OurDomain.our_model in
                        let class_name = Type.class_name class_data.instantiated in
                        let add_init = Reference.combine class_name (Reference.create "__init__") in
                        let arg_types_of_namedtuple = OurDomain.OurSummary.get_all_arg_types ~type_join:(GlobalResolution.join global_resolution) final_model add_init in
                        let attribute_name = "$parameter$" ^ (Annotated.Attribute.name attribute) in
                        let arg_type = OurDomain.ArgTypes.get_type arg_types_of_namedtuple attribute_name in
                        let annotation = arg_type |> Annotation.create_mutable in
                        let resolution = Resolution.refine_local_with_attributes resolution ~temporary:false ~name:name_expression ~annotation in

                        annotation, resolution
                      | _ -> get_local_type, resolution
                      )
                    (* | Type.Top | Unknown | Any ->
                      (* TODO : final summary 만으로 충분한가? *)
                      let final_model = !OurDomain.our_model in
                      let attribute_name = (Annotated.Attribute.name attribute) in
                      
                      OurTypeSet.OurSummaryResolution.get_type_of_class_attribute final_model (Type.class_name class_data.instantiated) attribute_name
                      |> (fun t ->
                       (*  Log.dump "%s, %a => %a" attribute_name Reference.pp (Type.class_name class_data.instantiated) Type.pp t; *)
                        match t with
                        | Type.Unknown -> annotation
                        | _ -> Annotation.create_mutable t
                      ), resolution *)
                    (* | Callable t -> (* TODO : Modify Resolution of callable *)
                      (* Log.dump "Before %s... %a" name Type.pp (Callable t); *)
                      let type_join = GlobalResolution.join global_resolution in
                      let final_model = !OurDomain.our_model in
                      let callable = OurDomain.OurSummary.get_callable ~type_join final_model t in
                      let annotation = Annotation.create_mutable (Callable callable) in

                      (* Log.dump "After %s... %a" name Type.pp (Callable callable); *)
                      annotation, resolution
                    | Parametric { name = "BoundMethod"; parameters = [Single (Callable t); other]} ->
                      (* Log.dump "Before %s... %a" name Type.pp (Callable t); *)
                      let type_join = GlobalResolution.join global_resolution in
                      let final_model = !OurDomain.our_model in
                      let callable = OurDomain.OurSummary.get_callable ~type_join final_model t in
                      (* Log.dump "After %s... %a" name Type.pp (Callable callable); *)
                      let annotation = Annotation.create_mutable (Parametric { name = "BoundMethod"; parameters = [Single (Callable callable); other]}) in

                      annotation, resolution *)
                    | _ -> 
                      (* TODO : final summary 만으로 충분한가? *) 
                      let final_model = !OurDomain.our_model in

                      (* Log.dump "WHAT?? %a" OurDomain.OurSummary.pp final_model; *)
                      let attribute_name = (Annotated.Attribute.name attribute) in
                      let type_join = GlobalResolution.join global_resolution in
                      let less_or_equal = GlobalResolution.less_or_equal global_resolution in
                      
                      OurTypeSet.OurSummaryResolution.get_type_of_class_attribute ~type_join ~less_or_equal final_model (Type.class_name class_data.instantiated) attribute_name
                      |> (fun t ->
                       
                        match t with
                        | None -> 
                          (* Log.dump "%s, %a => %a" attribute_name Reference.pp (Type.class_name class_data.instantiated) Annotation.pp annotation; *)
                          annotation
                        | Some t -> 
                          (* Log.dump "%s, %a => %a" attribute_name Reference.pp (Type.class_name class_data.instantiated) Type.pp t; *)
                         (*  if String.is_substring (Reference.show define_name) ~substring:"luigi.contrib.redshift.S3CopyToTable.run"
                            then (
                              Log.dump "FIND %s.%s ==> %a" (Expression.show base) name Type.pp t;
                            ); *)
                          Annotation.create_mutable t
                      ), resolution
                in
                new_annotation::acc, resolution
                ) 
              in

              
      
              let annotations = List.rev rev_annotations in
              List.hd_exn annotations, List.tl_exn annotations, resolution
            in

            begin
              let attributes_with_instantiated =
                List.zip_exn
                  attributes
                  (class_datas |> List.map ~f:(fun { Type.instantiated; _ } -> instantiated))
              in
              Context.Builder.add_property_callees
                ~global_resolution
                ~resolved_base
                ~attributes:attributes_with_instantiated
                ~location
                ~qualifier:Context.qualifier
                ~name
            end;

            let errors, resolution =
              let attribute_name, target =
                match
                  List.find attribute_info ~f:(fun (_, _, undefined_target) ->
                      Option.is_some undefined_target)
                with
                | Some (_, attribute, Some target) ->
                    AnnotatedAttribute.public_name attribute, Some target
                | Some (_, attribute, _) -> AnnotatedAttribute.public_name attribute, None
                | _ -> name, None
              in
              

              match target with
              | Some target ->
                  if has_default then
                    errors, resolution
                  else if Option.is_some (inverse_operator name) && not (Option.is_some (inverse_math_operator name) && Type.can_none resolved_base) then
                    (* Defer any missing attribute error until the inverse operator has been
                        typechecked. *)
                    errors, resolution
                  else
                    let class_origin =
                      match resolved_base with
                      | Type.Union [Type.NoneType; _]
                      | Union [_; Type.NoneType] ->
                          Error.ClassType target
                      | Union unions ->
                          List.findi ~f:(fun _ element -> Type.equal element target) unions
                          >>| (fun (index, _) -> Error.ClassInUnion { unions; index })
                          |> Option.value ~default:(Error.ClassType target)
                      | _ -> Error.ClassType target
                    in

                    let errors =
                      let skip_error = check_attribute ~class_origin attribute_name in

                      if skip_error then
                        errors
                      else (
                        emit_error
                          ~errors
                          ~location
                          ~kind:
                            (Error.UndefinedAttributeWithReference
                                {
                                  reference=base;
                                  attribute = attribute_name;
                                  origin =
                                    Error.Class
                                      {
                                        class_origin;
                                        parent_module_path = module_path_of_parent_module target;
                                      };
                                })
                      )
                    in
                    (* if String.is_substring (Reference.show define_name) ~substring:"airflow.www.app.create_app"
                      then (
                        Log.dump "BEFORE %a" Expression.pp expression;
                    ); *)
                    (* let resolution =
                      (* TODO: have to add attribute in resolution? *)
                      (*Log.dump "Base : %a / Attr : %s" Expression.pp base attribute;*)
                      Resolution.refine_local_with_attributes resolution ~temporary:true ~name:name_expression ~annotation:(Annotation.create_mutable Type.Unknown)
                      
                    in *)
                    (* if String.is_substring (Reference.show define_name) ~substring:"airflow.www.app.create_app"
                      then (
                        Log.dump "AFTER %a" Expression.pp expression;
                    ); *)
                    errors, resolution
              | _ -> errors, resolution
            in

            

            let resolved_annotation =
              let apply_local_override global_annotation =

                (* if String.is_substring (Reference.show define_name) ~substring:"luigi.contrib.redshift.S3CopyToTable.run"
                  then (
                    Log.dump "2222 Name %a (%a)" Name.pp name_expression Annotation.pp global_annotation;
                  ); *)

                let local_override =
                  reference
                  >>= fun reference ->
                  Resolution.get_local_with_attributes
                    resolution
                    ~name:(create_name_from_reference ~location:Location.any reference)
                    ~global_fallback:(Type.is_meta (Annotation.annotation global_annotation))
                in
                match local_override with
                | Some local_annotation ->
                local_annotation
                | None ->
                global_annotation
              in
              (*
              let apply_class_info annotation =
                Log.dump "Resolved_Base : %a" Type.pp resolved_base;
                match (Annotation.annotation annotation) with
                | Type.Top | Unknown -> 
                  if OurDomain.is_inference_mode (OurDomain.load_mode ()) then
                    (* TODO : final summary 만으로 충분한가? *)
                    let final_model = !OurDomain.our_summary in
                    OurTypeSet.OurSummaryResolution.get_type_of_class_attribute final_model (Type.class_name resolved_base) attribute
                    |> (fun t ->
                      match t with
                      | Type.Unknown -> Log.dump "Mayber?"; annotation
                      | _ -> Annotation.create_mutable t
                    )

                  else
                    annotation
                | _ -> annotation
              in
              *)

              let join sofar element =
                (* let refined =
                  Refinement.Unit.join
                    ~global_resolution
                    (Refinement.Unit.create sofar)
                    (Refinement.Unit.create element)
                  |> Refinement.Unit.base
                  |> Option.value ~default:(Annotation.create_mutable Type.Unknown)
                in
                { refined with annotation = Type.union [sofar.annotation; element.annotation] } *)

                (* if String.is_substring (Reference.show define_name) ~substring:"luigi.contrib.redshift.S3CopyToTable.run"
                  then (
                    Log.dump "1111 Name %a (%a) (%a)" Name.pp name_expression Annotation.pp sofar Annotation.pp element;
                  ); *)

                Annotation.join ~type_join:(GlobalResolution.join global_resolution) sofar element
              in

              List.fold ~init:head_annotation ~f:join tail_annotations 
              |> apply_local_override
              (*
              |> apply_class_info
              *)
            in

            (* Log.dump "Name %a (%a)" Name.pp name_expression Annotation.pp resolved_annotation; *)

            (* if String.is_substring (Reference.show define_name) ~substring:"luigi.contrib.redshift.S3CopyToTable.run"
            then (
              Log.dump "Name %a (%a)" Name.pp name_expression Annotation.pp resolved_annotation;
            ); *)

            let resolved_annotation =
              match Annotation.annotation resolved_annotation with
              | Type.Top | Any -> Annotation.create_mutable Type.Unknown
              | _ -> resolved_annotation
            in
            
            {
              resolution;
              errors;
              resolved = Annotation.annotation resolved_annotation;
              resolved_annotation = Some resolved_annotation;
              base = None;
            }
      in
      let resolved =
        match resolved_base with
        (* Global or local. *)
          
        | Type.Top ->
            reference
            >>| forward_reference ~resolution ~errors
            |> Option.value
                  ~default:
                    {
                      Resolved.resolution;
                      errors;
                      resolved = Type.Unknown;
                      resolved_annotation = None;
                      base = None;
                    }
        (* TODO(T63892020): We need to fix up qualification so nested classes and functions are just
            normal locals rather than attributes of the enclosing function, which they really are not *)
        | Type.Parametric { name = "BoundMethod"; _ }
        | Type.Callable _ -> (
            let resolved =
              reference >>= fun reference -> Resolution.get_local resolution ~reference
            in
            match resolved with
            | Some annotation ->
                {
                  resolution;
                  errors;
                  resolved = Annotation.annotation annotation;
                  resolved_annotation = Some annotation;
                  base = None;
                }
            | None -> access_as_attribute ())
        | _ ->
            (* Attribute access. *)
            access_as_attribute ()
      in


      
      let base =
        match super_base with
        | Some (Resolved.Super _) -> super_base
        | _ ->
            let is_global_meta =
              let is_global () =
                match base with
                | { Node.value = Name name; _ } ->
                    name_to_identifiers name
                    >>| Reference.create_from_list
                    >>= GlobalResolution.global global_resolution
                    |> Option.is_some
                | _ -> false
              in
              Type.is_meta resolved_base && is_global ()
            in
            if is_global_meta then
              Some (Resolved.Class resolved_base)
            else
              Some (Resolved.Instance resolved_base)
      in
      { resolved with base }
    in
    let forward_callable ~resolution ~errors ~target ~dynamic ~callee ~arguments =
      (*Log.dump "[Forward Callable] %a / %a" Expression.pp (Callee.expression callee) Type.pp (Callee.resolved callee);
    
      
      let dump_arguments arguments = 
        List.iter arguments ~f:(fun arg ->
          Log.dump "Arg : %a" Call.Argument.pp arg; 
        )
      in
      
      dump_arguments arguments;
      *)
      let { StatementDefine.Signature.name=define_name; _ } = define_signature in

      (* Name (Name.Attribute _ as name) 
      when  && (
        
      ) -> 

      if OurDomain.is_recheck_mode (OurDomain.load_mode ()) then (
        match name_to_reference name with
        | Some reference ->
          let reference = Reference.delocalize_only_name reference in
          Reference.Set.fold !OurDomain.skip_reference_set ~init:false ~f:(fun flag ref ->
            flag || (Reference.equal ref reference) || (String.is_substring (Reference.show reference) ~substring:(Reference.show ref))
          )
        | _ -> false
      ) else ( *)
      (* if String.is_substring (Reference.show define_name) ~substring:"HTMLFormatter._write_col_header"
        then (
          Log.dump "Callee %a ==> %a" Expression.pp (Callee.expression callee) Type.pp (Callee.resolved callee);
        ); *)
      (* Log.dump "Callee %a Type %a" Expression.pp (Callee.expression callee) Type.pp (Callee.resolved callee); *)

      (* Log.dump "[Forward Callable] %a / %a" Expression.pp (Callee.expression callee) Type.pp (Callee.resolved callee); *)

      let resolved_dict_get callee_resolved =

        let rec resolved_dict_get callee_resolved =
          match callee_resolved with
          | Type.Union t_list ->(*  List.fold t_list ~init:Type.Bottom ~f:(fun acc t -> GlobalResolution.join global_resolution acc (resolved_dict_getitem t)) *)
            (* let other_types = List.map t_list ~f:(fun t -> not (Type.is_dict t)) in *)
            let new_t_list = 
              List.map t_list ~f:(fun t -> resolved_dict_get t)
              |> List.filter ~f:Option.is_some 
              |> List.map ~f:(fun t -> Option.value_exn t ~message:"Why is in None?")
            in
            if List.length new_t_list = 0 then None
            else (
              Some (List.fold new_t_list ~init:Type.Bottom ~f:(fun acc t -> GlobalResolution.join global_resolution acc t))
            )
          | Type.Parametric (* dict.get 처리 *)
          { name = "BoundMethod"; parameters = [Single (Callable { kind = Named name; _ }); Single origin] } 
          when String.equal (Reference.show name) "dict.get"
          ->
            if List.length arguments <= 2
              then
                (
                let annotation_type = origin in
                let reversed_arguments =
                  let forward_argument reversed_arguments argument =
                    let expression, kind = Ast.Expression.Call.Argument.unpack argument in
                    forward_expression ~resolution ~at_resolution expression
                    |> fun { resolved; _ } ->
                      { AttributeResolution.Argument.kind; expression = Some expression; resolved }
                      :: reversed_arguments
                  in
                  List.fold arguments ~f:forward_argument ~init:[]
                in
                let arguments = List.rev reversed_arguments in

                (* value 원소는 literal이어야 한다 *)
                let value_arg = List.nth_exn arguments 0 in

                (match annotation_type, value_arg.expression with
                | OurTypedDictionary _, Some expression when (not !Type.restrict_dict) ->
                  let t = Type.get_dict_value_type ~with_key:(Some (Expression.show expression)) ~value_type:value_arg.resolved annotation_type in
                  Some t
                | _ -> None
                )
              )
              
              else (
                failwith "GetItem Callee Length is not 1"
              )
          | _ -> (* Log.dump "No %a" Type.pp callee_resolved; *) None
        in

        let t = resolved_dict_get callee_resolved in
        (match t with
        | Some t ->
          if List.length arguments = 2 then
            let reversed_arguments =
              let forward_argument reversed_arguments argument =
                let expression, kind = Ast.Expression.Call.Argument.unpack argument in
                forward_expression ~resolution ~at_resolution expression
                |> fun { resolved; _ } ->
                  { AttributeResolution.Argument.kind; expression = Some expression; resolved }
                  :: reversed_arguments
              in
              List.fold arguments ~f:forward_argument ~init:[]
            in
            let arguments = List.rev reversed_arguments in
            let default_value_arg = List.nth_exn arguments 1 in
            Some (GlobalResolution.join global_resolution t default_value_arg.resolved) 
          else
            Some t
        | _ -> t
        )
        
      in
     

      (* Ours : zip *)
      let resolved_zip callee_resolved =
        match callee_resolved with
        | Type.Parametric (* zip 처리 *)
          { name = "type" | "typing.Type"; parameters=[Single (Primitive "zip")]; }  ->
            let reversed_arguments =
              let forward_argument reversed_arguments argument =
                let expression, kind = Ast.Expression.Call.Argument.unpack argument in
                forward_expression ~resolution ~at_resolution expression
                |> fun { resolved; _ } ->
                  { AttributeResolution.Argument.kind; expression = Some expression; resolved }
                  :: reversed_arguments
              in
              List.fold arguments ~f:forward_argument ~init:[]
            in
            let arguments = List.rev reversed_arguments in

            let extract_element_type iterable =
              match iterable with
              | Type.Parametric { name = "list" | "typing.List"; parameters = [Single parameter] } ->
                if Type.is_any parameter then
                  Some Type.Unknown
                else
                  Some parameter
              | Tuple (Concrete parameters) ->
                Some (Union parameters)
              | _ -> None
            in

            let resolved_list = List.map arguments ~f:(fun argument -> 
              let new_type =
                Type.union_fold_with_filter ~f:extract_element_type argument.resolved
                |> Option.value ~default:Type.Unknown
              in
              
              (* Type.iterable *) new_type
            ) 
            in

            Type.tuple resolved_list
            |> Type.iterable
        | _ -> callee_resolved
      in

      (* Ours : List *)
      let resolved_list_append resolution callee =
        let rec get_type callee_resolved =
          match callee_resolved with
          | Type.Union t_list ->
            let new_t_list = 
              List.map t_list ~f:(fun t -> get_type t)
              |> List.filter ~f:Option.is_some 
              |> List.map ~f:(fun t -> Option.value_exn t ~message:"Why is in None?")
            in
            if List.length new_t_list = 0 then None
            else Some (Type.Union new_t_list)
          | Type.Parametric (* list.append 처리 *)
            { name = "BoundMethod"; parameters = [Single (Callable { kind = Named name; _ }); Single origin] } 
            when String.equal (Reference.show name) "list.append"
            -> 
              if List.length arguments = 1
              then
                (
                let reversed_arguments =
                  let forward_argument reversed_arguments argument =
                    let expression, kind = Ast.Expression.Call.Argument.unpack argument in
                    forward_expression ~resolution ~at_resolution expression
                    |> fun { resolved; _ } ->
                      { AttributeResolution.Argument.kind; expression = Some expression; resolved }
                      :: reversed_arguments
                  in
                  List.fold arguments ~f:forward_argument ~init:[]
                in
                let arguments = List.rev reversed_arguments in

                let value_arg = List.nth_exn arguments 0 in
                
                (match origin with
                | Parametric _ -> 
                  let origin_parameter = Type.single_parameter origin in
                  Some (GlobalResolution.join global_resolution origin_parameter value_arg.resolved |> Type.list)
                | _ -> None
                )
                
                )
              else
                failwith "Append Get 2 Item"
          | _ -> None
        in

        match callee with
        | Callee.Attribute { base={ expression={ Node.value = Expression.Name name; _ }; _}; _ } ->
          let new_type = get_type (Callee.resolved callee) in
          (match new_type with
          | Some t -> 
            let join = GlobalResolution.join global_resolution in
            let less_or_equal = GlobalResolution.less_or_equal global_resolution in
            Resolution.refine_local_with_attributes resolution ~name ~annotation:(Annotation.create_mutable (t |> Type.narrow_union ~join ~less_or_equal))
          | _ -> resolution
          )
        | _ -> resolution
      in

      let resolved_list_extend resolution callee =
        let rec get_type callee_resolved =
          match callee_resolved with
          | Type.Union t_list ->
            let new_t_list = 
              List.map t_list ~f:(fun t -> get_type t)
              |> List.filter ~f:Option.is_some 
              |> List.map ~f:(fun t -> Option.value_exn t ~message:"Why is in None?")
            in
            if List.length new_t_list = 0 then None
            else Some (Type.Union new_t_list)
          | Type.Parametric (* list.extend 처리 *)
            { name = "BoundMethod"; parameters = [Single (Callable { kind = Named name; _ }); Single origin] } 
            when String.equal (Reference.show name) "list.extend"
            -> 
              if List.length arguments = 1
              then
                (
                let reversed_arguments =
                  let forward_argument reversed_arguments argument =
                    let expression, kind = Ast.Expression.Call.Argument.unpack argument in
                    forward_expression ~resolution ~at_resolution expression
                    |> fun { resolved; _ } ->
                      { AttributeResolution.Argument.kind; expression = Some expression; resolved }
                      :: reversed_arguments
                  in
                  List.fold arguments ~f:forward_argument ~init:[]
                in
                let arguments = List.rev reversed_arguments in

                let value_arg = List.nth_exn arguments 0 in
                let value_type = value_arg.resolved in

                (match origin with
                | Parametric _ -> 
                  let origin_parameter = Type.single_parameter origin in
                  let update_value_type value_type =
                    match value_type with
                    | Type.Parametric { parameters = [Single value_inner]; _ } when 
                      Type.is_iterable value_type ||
                      Type.is_list value_type ||
                      Type.is_set value_type ||
                      Type.is_tuple value_type
                      ->
                      GlobalResolution.join global_resolution origin_parameter value_inner |> Type.list
                    | Type.Parametric { parameters = [Single value_inner; _]; _ } when  Type.is_dict value_type
                      ->
                      GlobalResolution.join global_resolution origin_parameter value_inner |> Type.list
                    | _ -> 
                      (* TODO : Error Plz *)
                      origin
                  in
                  Some (Type.union_update ~f:update_value_type value_type)
                | _ -> None
                )
                )

              else
                None
          | _ -> None
        in

        match callee with
        | Callee.Attribute { base={ expression={ Node.value = Expression.Name name; _ }; _}; _ } ->
          let new_type = get_type (Callee.resolved callee) in
          (match new_type with
          | Some t -> 
            let join = GlobalResolution.join global_resolution in
            let less_or_equal = GlobalResolution.less_or_equal global_resolution in
            Resolution.refine_local_with_attributes resolution ~name ~annotation:(Annotation.create_mutable (t |> Type.narrow_union ~join ~less_or_equal))
          | _ -> resolution
          )
        | _ -> resolution
      in

      (* Ours : Dict *)

      let rec resolved_dict_getitem callee_resolved =
        match callee_resolved with
        | Type.Union t_list ->(*  List.fold t_list ~init:Type.Bottom ~f:(fun acc t -> GlobalResolution.join global_resolution acc (resolved_dict_getitem t)) *)
          let new_t_list = 
            List.map t_list ~f:(fun t -> resolved_dict_getitem t)
            |> List.filter ~f:Option.is_some 
            |> List.map ~f:(fun t -> Option.value_exn t ~message:"Why is in None?")
          in
          if List.length new_t_list = 0 then None
          else (
            Some (List.fold new_t_list ~init:Type.Bottom ~f:(fun acc t -> GlobalResolution.join global_resolution acc t))
          )
        | Type.Parametric (* dict.__getitem__ 처리 *)
          { name = "BoundMethod"; parameters = [Single (Callable { kind = Named name; _ }); Single origin] } 
          when String.equal (Reference.show name) "dict.__getitem__"
          -> 
            if List.length arguments = 1
            then
              (
              let annotation_type = origin in
              let reversed_arguments =
                let forward_argument reversed_arguments argument =
                  let expression, kind = Ast.Expression.Call.Argument.unpack argument in
                  forward_expression ~resolution ~at_resolution expression
                  |> fun { resolved; _ } ->
                    { AttributeResolution.Argument.kind; expression = Some expression; resolved }
                    :: reversed_arguments
                in
                List.fold arguments ~f:forward_argument ~init:[]
              in
              let arguments = List.rev reversed_arguments in

              (* value 원소는 literal이어야 한다 *)
              let value_arg = List.nth_exn arguments 0 in


              if Type.can_union ~f:(fun t -> Type.equal t (Primitive "slice")) value_arg.resolved 
              then None (* callee_resolved *)
              else (
                let result = 
                  (match value_arg.expression with
                  | Some exp -> 
                    Type.get_dict_value_type ~with_key:(Some (Expression.show exp)) ~value_type:value_arg.resolved annotation_type
                  | _ -> Type.get_dict_value_type annotation_type 
                  )
                  (* if Type.contains_literal value_arg.resolved
                  then (
                    Type.get_dict_value_type ~with_key:(Some (Expression.show (Option.value_exn value_arg.expression))) annotation_type
                  )
                  else Type.get_dict_value_type annotation_type  *)
                in
                
                (* Log.dump "Value : %a / Annotation : %a" Type.pp value_arg.resolved Type.pp annotation_type; *)

                Some result
              )
              )
            
            else (
              None
            )
            

        | _ -> None
      in

      let rec update_dict_setitem resolution callee_resolved =
        match callee_resolved with
        | Type.Union t_list -> List.fold t_list ~init:resolution ~f:update_dict_setitem
        | Type.Parametric (* dict.__setitem__ 처리 *)
            { name = "BoundMethod"; parameters = [Single (Callable { kind = Named name; _ }); Single _] } 
            when String.equal (Reference.show name) "dict.__setitem__"
            ->
              if List.length arguments = 2
              then
                let reversed_arguments =
                  let forward_argument reversed_arguments argument =
                    let expression, kind = Ast.Expression.Call.Argument.unpack argument in
                    forward_expression ~resolution ~at_resolution expression
                    |> fun { resolved; _ } ->
                      { AttributeResolution.Argument.kind; expression = Some expression; resolved }
                      :: reversed_arguments
                  in
                  List.fold arguments ~f:forward_argument ~init:[]
                in
                let arguments = List.rev reversed_arguments in
                
                let key_arg = List.nth_exn arguments 0 in
                let value_arg = List.nth_exn arguments 1 in
                let _ = value_arg in

                
                match (Callee.expression callee) with
                | { Node.value = Name (Attribute { base; _ }); _ } ->
                  (match base with
                  | { Node.value = Name name; _} ->
                    
                    
                    (* Log.dump "Expression : %a / %a -> %a" Expression.pp expression Type.pp key_arg.resolved Type.pp value_arg.resolved;
 *)
                    let annotation_type = Resolution.resolve_expression_to_type resolution base in
                    (*
                    let change_dict t =
                      if Type.is_dict t
                      then (
                        Type.dictionary ~key:Type.Unknown ~value:Type.Unknown
                      )
                      else t
                    in

                    let rec resolved_dict t =
                      match t with
                      | Type.Union t_list ->
                        Type.Union (List.map t_list ~f:resolved_dict)
                      | t -> change_dict t
                    in

                    let value_arg_resolved = resolved_dict value_arg.resolved in
                    *)
                    let value_arg_resolved = value_arg.resolved in

                    let name = name_to_reference name |> Option.value ~default:Reference.empty in

                    let update_dict_field =
                      (* key 원소가 literal이면 OurTypedDictionary *)
                      if (not !Type.restrict_dict) && Type.contains_literal key_arg.resolved
                      then (
                        Type.OurTypedDictionary.update_dict_field ~join_f:(GlobalResolution.join global_resolution) annotation_type (Expression.show (Option.value_exn key_arg.expression)) value_arg_resolved
                      )
                      else (* key 원소가 literal이 아니면 Dictionary *)
                        annotation_type
                    in

                    

                    let update_dict_key_value =
                      GlobalResolution.join_dict_key_value update_dict_field ~global_resolution ~key:key_arg.resolved ~value:value_arg_resolved
                    in

                    (* Log.dump "Update Type : %a" Type.pp update_dict_field;
                    Log.dump "Result Type : %a" Type.pp update_dict_key_value; *)
                    let join = GlobalResolution.join global_resolution in
                    let less_or_equal = GlobalResolution.less_or_equal global_resolution in
                    let annotation = update_dict_key_value |> Type.narrow_union ~join ~less_or_equal |> Annotation.create_mutable in
                    let prefix_name = Reference.prefix name |> Option.value ~default:Reference.empty in
                    let attributes = Reference.drop_prefix ~prefix:prefix_name name in

                    let prefix_name, attributes = 
                      if Reference.is_empty prefix_name 
                      then attributes, prefix_name
                      else prefix_name, attributes
                    in

                    let annotation_store = Resolution.get_annotation_store resolution in
                    let update_annotation_store = Refinement.Store.set_annotation ~name:prefix_name ~attribute_path:attributes ~base:None ~annotation annotation_store in
                    let x = Resolution.set_annotation_store resolution update_annotation_store in
                    
                    (* Log.dump "Result Resolution : %a" Resolution.pp x; *)
                    
                    x
                  | _ -> resolution
                  )
                  

                | _ -> resolution
                

                (*
                match key_arg.resolved with
                | Literal (Integer literal) ->
                  let new_field = 
                    Type.OurTypedDictionary.create_field ~annotation:(Annotation.create_mutable value_arg.resolved) literal 
                  in
                | Literal (String (LiteralValue literal)) ->
                  let new_field = 
                    Type.OurTypedDictionary.create_field ~annotation:(Annotation.create_mutable value_arg.resolved) literal 
                  in
                | Literal (Bytes literal)  ->
                  let new_field = 
                    Type.OurTypedDictionary.create_field ~annotation:(Annotation.create_mutable value_arg.resolved) literal 
                  in
                | _ -> ()
                  *)
              else
                resolution

        | _ -> resolution
      in

      let resolved_dict_update resolution callee =
        let rec get_type callee_resolved =
          match callee_resolved with
          | Type.Union t_list ->
            let new_t_list = 
              List.map t_list ~f:(fun t -> get_type t)
              |> List.filter ~f:Option.is_some 
              |> List.map ~f:(fun t -> Option.value_exn t ~message:"Why is in None?")
              |> List.fold ~init:Type.Bottom ~f:(fun acc t -> GlobalResolution.join global_resolution acc t)
            in
            (* TODO : is okay join?? *)
            if Type.equal Type.Bottom new_t_list then None
            else Some new_t_list
            (* if List.length new_t_list = 0 then None
            else Some (Type.Union new_t_list) *)
          | Type.Parametric (* dict.update 처리 *)
              { name = "BoundMethod"; parameters = [Single (Callable { kind = Named name; _ }); Single origin] } 
              when String.equal (Reference.show name) "typing.MutableMapping.update"
              ->
                if List.length arguments = 1
                then
                  let reversed_arguments =
                    let forward_argument reversed_arguments argument =
                      let expression, kind = Ast.Expression.Call.Argument.unpack argument in
                      forward_expression ~resolution ~at_resolution expression
                      |> fun { resolved; _ } ->
                        { AttributeResolution.Argument.kind; expression = Some expression; resolved }
                        :: reversed_arguments
                    in
                    List.fold arguments ~f:forward_argument ~init:[]
                  in
                  let arguments = List.rev reversed_arguments in
                  
                  let value_arg = List.nth_exn arguments 0 in
                  let value_type = value_arg.resolved in

                  (* (match value_arg.expression with
                  | Some e ->  Log.dump "VALUE : %a" Expression.pp e;
                  | _ -> Log.dump "NO..";
                  ); *)
                 

                  let update_value_type value_type =
                    (match value_type with
                    | Type.Parametric _ when Type.is_dict value_type ->
                      GlobalResolution.join global_resolution value_type origin
                    | OurTypedDictionary _ ->
                      GlobalResolution.join global_resolution value_type origin
                    | _ -> 
                      origin
                    )
                  in

                  (* Log.dump "??? %a ===> %a" Type.pp value_type Type.pp (update_value_type value_type); *)

                  Some (Type.union_update ~f:update_value_type value_type)

                else (
                  (* Update can be 2 more arguments *)
                  None
                )

          | _ -> None
        in

        match callee with
        | Callee.Attribute { base={ expression={ Node.value = Expression.Name name; _ }; _}; _ } ->
          let old_type = (Callee.resolved callee) in
          let new_type = get_type old_type in
          
          (match new_type with
          | Some t -> 
            let join = GlobalResolution.join global_resolution in
            let less_or_equal = GlobalResolution.less_or_equal global_resolution in
            
            let resolution = Resolution.refine_local_with_attributes resolution ~name ~annotation:(Annotation.create_mutable (t |> Type.narrow_union ~join ~less_or_equal)) in
            (* let new_type = Resolution.get_local_with_attributes ~name resolution 
              |> Option.value ~default:(Type.dictionary ~key:Type.Unknown ~value:Type.Unknown |> Annotation.create_mutable)
              |> Annotation.annotation
            in
            Log.dump "?? %a" Type.pp new_type;

            let callee = Callee.update_resolved callee new_type in *)

            callee, resolution
          | _ -> callee, resolution
          )
        | _ -> callee, resolution
      in

      let update_method_type arguments callee =
        let rec update_resolved t = 
          match t with
          | Type.Union t_list -> Type.Union (List.map t_list ~f:update_resolved)
          | Type.Callable t -> (* TODO : Modify Resolution of callable *)
          (* Log.dump "Before %s... %a" name Type.pp (Callable t); *)
            let reversed_arguments =
              let forward_argument reversed_arguments argument =
                let expression, kind = Ast.Expression.Call.Argument.unpack argument in
                forward_expression ~resolution ~at_resolution expression
                |> fun { resolved; _ } ->
                  { AttributeResolution.Argument.kind; expression = Some expression; resolved }
                  :: reversed_arguments
              in
              List.fold arguments ~f:forward_argument ~init:[]
            in
            let arguments = List.rev reversed_arguments in
            let join = GlobalResolution.join global_resolution in
            let less_or_equal = GlobalResolution.less_or_equal global_resolution in
            let successors = GlobalResolution.successors ~resolution:global_resolution in
            let final_model = !OurDomain.our_model in
            let arg_types = GlobalResolution.callable_to_arg_types ~global_resolution ~self_argument:None ~arguments t in
            let callable = OurDomain.OurSummary.get_callable ~join ~less_or_equal ~successors final_model arg_types t in
          (* Log.dump "After %s... %a" name Type.pp (Callable callable); *)
            Type.Callable callable
          | Type.Parametric { name = "BoundMethod"; parameters = [Single (Callable t); Single self_argument]} ->
          (* Log.dump "Before... %a" Type.pp (Callable t); *)
            let reversed_arguments =
              let forward_argument reversed_arguments argument =
                let expression, kind = Ast.Expression.Call.Argument.unpack argument in
                forward_expression ~resolution ~at_resolution expression
                |> fun { resolved; _ } ->
                  { AttributeResolution.Argument.kind; expression = Some expression; resolved }
                  :: reversed_arguments
              in
              List.fold arguments ~f:forward_argument ~init:[]
            in
            let arguments = List.rev reversed_arguments in
            let join = GlobalResolution.join global_resolution in
            let less_or_equal = GlobalResolution.less_or_equal global_resolution in
            let successors = GlobalResolution.successors ~resolution:global_resolution in
            let final_model = !OurDomain.our_model in
            let arg_types = GlobalResolution.callable_to_arg_types ~global_resolution ~self_argument:(Some self_argument) ~arguments t in
            let callable = OurDomain.OurSummary.get_callable ~join ~less_or_equal ~successors final_model arg_types t in
            
            
            (* Log.dump "After... %a" Type.pp (Callable callable); *)
            Type.Parametric { name = "BoundMethod"; parameters = [Single (Callable callable); Single self_argument]}
          | t -> t 
        in

        let new_resolved = update_resolved (Callee.resolved callee) in

        match callee with
        | Attribute ({ attribute; _ } as t)->
          let attribute = { attribute with resolved=new_resolved } in
          Callee.Attribute { t with attribute }
        | NonAttribute t ->
          NonAttribute { t with resolved=new_resolved }

      in

      let callee =
        if !OurDomain.on_any
        then callee
        else (
          Callee.to_any_resolved callee
        ) 
      in


      let resolution = resolved_list_append resolution callee in
      let resolution = resolved_list_extend resolution callee in
      let resolution = update_dict_setitem resolution (Callee.resolved callee) in
      let callee, resolution = resolved_dict_update resolution callee in

      let callee = update_method_type arguments callee in

      (* Log.dump "Resolution >>> %a" Resolution.pp resolution; *)

      let rec update_resolved_type ?(no_rec=false) t =
        let t = t |> Type.Variable.convert_all_escaped_free_variables_to_bottom  in
        match t with
        (* possible infinite loop *)
        | Type.Variable _
          when not no_rec
          -> update_resolved_type ~no_rec:true (t |> Type.Variable.convert_all_escaped_free_variables_to_bottom)
        | Type.Top 
        | Type.Any
          -> update_resolved_type Type.Unknown
        | Type.Bottom 
        | Type.Unknown
          ->
          let resolved_arguments =
            let forward_argument reversed_arguments argument =
              let expression, _ = Ast.Expression.Call.Argument.unpack argument in
              forward_expression ~resolution ~at_resolution expression
              |> fun { resolved; _ } ->
                resolved :: reversed_arguments
            in
            List.fold arguments ~f:forward_argument ~init:[]
          in

          (* default typecasting 처리 *)
          let resolved = 
            match Node.value (Callee.expression callee) with
            | Name (Name.Attribute { attribute = "__str__"; _}) -> Type.string
            | Name (Name.Attribute { attribute = "__bytes__"; _}) -> Type.bytes
            | Name (Name.Attribute { attribute = "__int__"; _}) -> Type.integer
            | Name (Name.Attribute { attribute = "__bool__"; _}) 
            | Name (Name.Attribute { attribute = "__eq__"; _}) 
            | Name (Name.Attribute { attribute = "__neq__"; _}) 
            | Name (Name.Attribute { attribute = "__ge__"; _}) 
            | Name (Name.Attribute { attribute = "__le__"; _}) 
            | Name (Name.Attribute { attribute = "__gt__"; _}) 
            | Name (Name.Attribute { attribute = "__lt__"; _}) 
            -> Type.bool
            | Name (Name.Attribute { attribute = "__float__"; _}) -> Type.float
            | Name (Name.Attribute { attribute = "__list__"; _}) -> 
              Type.list (Type.union resolved_arguments)
            | Name (Name.Attribute { attribute = "__set__"; _}) -> Type.set (Type.union resolved_arguments)
            | Name (Name.Attribute { attribute = "__tuple__"; _}) -> Type.tuple resolved_arguments
            | Name (Name.Attribute { attribute = "__dict__"; _}) -> Type.dictionary ~key:Type.Unknown ~value:Type.Unknown
            | Name (Name.Attribute { attribute = "decode"; _}) -> Type.string
            | Name (Name.Attribute { attribute = "encode"; _}) -> Type.bytes
            | _ -> 
              Type.Unknown
              (* resolved_dict_getitem t (Callee.resolved callee) *)
          in

          resolved
        | _ -> t
      in

      let open CallableApplicationData in
      let unpack_callable_and_self_argument =
        unpack_callable_and_self_argument
          ~signature_select:
            (GlobalResolution.our_signature_select
                ~global_resolution
                ~resolve_with_locals:(resolve_expression_type_with_locals ~resolution ~at_resolution))
          ~global_resolution
      in

      (*
      if String.equal (Expression.show (Callee.expression callee)) "sorted"
      then
        match unpack_callable_and_self_argument with
        | Some c -> Log.dump "WOW : %a" TypeOperation.pp c;
        | None -> Log.dump "UU";
      *)
      
      let find_method ~parent ~name ~special_method =
        GlobalResolution.attribute_from_annotation global_resolution ~parent ~name ~special_method
        >>| Annotated.Attribute.annotation
        >>| Annotation.annotation
        >>= unpack_callable_and_self_argument
      in
      let callable_from_type resolved =
        match unpack_callable_and_self_argument resolved with
        | Some unpacked -> Some unpacked
        | _ -> find_method ~parent:resolved ~name:"__call__" ~special_method:true
      in
      let inverse_operator_callable
          ~callee_attribute:
            ({ Callee.base = { expression; resolved_base }; attribute = { name; _ }; _ } as
            callee_attribute)
        = function
        | [{ AttributeResolution.Argument.resolved; _ }] as arguments ->
            let found_inverse_operator =
              inverse_operator name
              >>= (fun name -> find_method ~parent:resolved ~name ~special_method:false)
              >>= fun found_callable ->
              if Type.is_any resolved_base || Type.is_unbound resolved_base then
                None
              else
                let inverted_arguments =
                  [
                    {
                      AttributeResolution.Argument.expression = Some expression;
                      resolved = resolved_base;
                      kind = Positional;
                    };
                  ]
                in
                Some
                  (KnownCallable
                      {
                        callable = found_callable;
                        arguments = inverted_arguments;
                        is_inverted_operator = true;
                        selected_return_annotation = ();
                      })
            in
            Option.first_some
              found_inverse_operator
              (Some (UnknownCallableAttribute { callable_attribute = callee_attribute; arguments }))
        | _ -> None
      in
      let rec get_callables callee =
        match callee with
        | Callee.Attribute ({ attribute = { resolved; _ }; _ } as callee_attribute)
          when Type.is_top resolved ->
            Some [unknown_callable_attribute_before_application callee_attribute]
        | Callee.Attribute { attribute = { resolved; _ }; _ }
        | Callee.NonAttribute { resolved; _ } -> (
            let resolved = Type.filter_unknown resolved in
            match resolved with
            | Type.Union annotations ->
                List.map annotations ~f:(fun annotation ->
                    callable_from_type annotation
                    >>| fun callable -> known_callable_before_application callable)
                |> Option.all
            | Type.Variable { constraints = Type.Variable.Bound parent; _ } ->
                let callee =
                  match callee with
                  | Callee.Attribute { attribute; base; expression } ->
                      Callee.Attribute
                        { base; attribute = { attribute with resolved = parent }; expression }
                  | Callee.NonAttribute callee ->
                      Callee.NonAttribute { callee with resolved = parent }
                in
                get_callables callee
            | annotation ->
                callable_from_type annotation
                >>| fun callable -> [known_callable_before_application callable])
      in
      let return_annotation_with_callable_and_self
          ~resolution
          ({
              callable = { TypeOperation.callable; _ };
              arguments;
              is_inverted_operator;
              selected_return_annotation;
            } as callable_data)
        =
        match selected_return_annotation, callable with
        | SignatureSelectionTypes.NotFound _, _ -> (
            match callee, callable, arguments with
            | ( Callee.Attribute { base = { expression; resolved_base }; _ },
                { Type.Callable.kind = Type.Callable.Named name; _ },
                [{ AttributeResolution.Argument.resolved; _ }] )
              when not is_inverted_operator ->
                inverse_operator (Reference.last name)
                >>= (fun name -> find_method ~parent:resolved ~name ~special_method:false)
                >>| (fun ({ TypeOperation.callable; self_argument } as
                          unpacked_callable_and_self_argument) ->
                      let arguments =
                        [
                          {
                            AttributeResolution.Argument.expression = Some expression;
                            kind = Positional;
                            resolved = resolved_base;
                          };
                        ]
                      in
                      {
                        callable_data with
                        selected_return_annotation =
                          GlobalResolution.our_signature_select
                            ~arguments
                            ~global_resolution:(Resolution.global_resolution resolution)
                            ~resolve_with_locals:(resolve_expression_type_with_locals ~resolution ~at_resolution)
                            ~callable
                            ~self_argument;
                        (* Make sure we emit errors against the inverse function, not the original *)
                        callable = unpacked_callable_and_self_argument;
                      })
                |> Option.value ~default:{ callable_data with selected_return_annotation }
            | _ -> { callable_data with selected_return_annotation })
        | ( (Found { selected_return_annotation; _ } as found_return_annotation),
            { kind = Named access; _ } )
          when not (Reference.is_initialize access) ->
            Type.split selected_return_annotation
            |> fst
            |> Type.primitive_name
            >>| (function
                  | class_name ->
                      let abstract_methods =
                        GlobalResolution.attributes
                          ~transitive:true
                          class_name
                          ~resolution:global_resolution
                        >>| List.filter ~f:AnnotatedAttribute.abstract
                        |> Option.value ~default:[]
                        |> List.map ~f:Annotated.Attribute.name
                      in
                      if not (List.is_empty abstract_methods) then
                        SignatureSelectionTypes.NotFound
                          {
                            closest_return_annotation = selected_return_annotation;
                            reason =
                              Some
                                (AbstractClassInstantiation
                                    { class_name = Reference.create class_name; abstract_methods });
                          }
                      else if GlobalResolution.is_protocol global_resolution (Primitive class_name)
                      then
                        NotFound
                          {
                            closest_return_annotation = selected_return_annotation;
                            reason = Some (ProtocolInstantiation (Reference.create class_name));
                          }
                      else
                        found_return_annotation)
            |> Option.value ~default:found_return_annotation
            |> fun selected_return_annotation -> 
              { callable_data with selected_return_annotation }

        | _ -> 

          { callable_data with selected_return_annotation }
      in
      let extract_found_not_found_unknown_attribute = function
        | KnownCallable
            {
              callable = { TypeOperation.callable; self_argument; _ };
              selected_return_annotation =
                SignatureSelectionTypes.Found { selected_return_annotation };
              arguments;
              _
            } ->
              
            (match callable.kind with
            | Named reference when not (Reference.is_initialize reference) ->
              let our_model = !OurDomain.our_model in
              let arg_types = GlobalResolution.callable_to_arg_types ~global_resolution ~self_argument ~arguments callable in
              let less_or_equal = GlobalResolution.less_or_equal global_resolution in 
              let type_join = GlobalResolution.join global_resolution in
              let observed_return_type = OurDomain.OurSummary.get_return_type ~type_join ~less_or_equal our_model reference arg_types in

              (* if String.is_substring (Reference.show define_name) ~substring:"_write_col_header"
                && (String.is_substring (Expression.show expression) ~substring:"columns.format") then
              (
                Log.dump "REF %a" Reference.pp reference;
                Log.dump "OBSERVED %a" Type.pp observed_return_type;
                Log.dump "UNION %a" Type.pp (Type.union [selected_return_annotation; observed_return_type]);

                Log.dump "JOIN %a" Type.pp (Type.union_join selected_return_annotation observed_return_type);
              ); *)
              (* Log.dump "NO? %a" Type.pp observed_return_type; *)

              (match selected_return_annotation with
              | Any -> `Fst observed_return_type
              | _ -> `Fst (Type.union [selected_return_annotation; observed_return_type])
              )
            | _ -> `Fst selected_return_annotation
            )
            
        | KnownCallable _ as not_found -> 
          `Snd not_found
        | UnknownCallableAttribute _ as unknown_callable_attribute ->
            `Trd unknown_callable_attribute
      in
      let resolved_for_bad_callable ~resolution ~errors undefined_attributes =
        (* When an operator does not exist on the left operand but its inverse exists on the right
            operand, the missing attribute error would not have been thrown for the original
            operator. Build up the original error in case the inverse operator does not typecheck. *)
        let potential_missing_operator_error undefined_attributes =
          match target, callee with
          | Some target, Callee.Attribute { attribute = { name; resolved }; _ }
            when (Type.is_top resolved
                  || Type.is_unknown resolved)
                  && Option.is_some (inverse_operator name)
                  && (not (Type.is_any target))
                  && (not (Type.is_unknown target))
                  && not (Type.is_unbound target) ->    
              (
              match undefined_attributes, operator_name_to_symbol name with
(*               | ( [
                    UnknownCallableAttribute
                      { arguments = [{ AttributeResolution.Argument.resolved; _ }]; _ };
                  ],
                  _ ) when Type.is_unknown resolved -> None  *)
              | ( [
                    UnknownCallableAttribute
                      { arguments = [{ AttributeResolution.Argument.resolved; _ }]; _ };
                  ],
                  Some operator_name ) 
                  ->
                    (* Log.dump "HERE??? %a" Expression.pp expression; *)
                  Some
                    (Error.UnsupportedOperand
                        (Binary { operator_name; left_operand = target; right_operand = resolved }))
              | _ ->
                  let class_module =
                    let ast_environment = GlobalResolution.ast_environment global_resolution in
                    GlobalResolution.class_summary global_resolution target
                    >>| Node.value
                    >>= fun { ClassSummary.qualifier; _ } ->
                    AstEnvironment.ReadOnly.get_module_path ast_environment qualifier
                  in

                  let skip_error = check_attribute ~class_origin:(ClassType target) name in

                  if skip_error then
                    None
                  else (

                    Some
                      (Error.UndefinedAttributeWithReference
                          {
                            reference = Callee.get_base callee;
                            attribute = name;
                            origin =
                              Error.Class
                                { class_origin = ClassType target; parent_module_path = class_module };
                          }))
                  )
          | _ -> None
        in
        let errors =
          let resolved_callee = Callee.resolved callee |> Type.filter_unknown in

          let rec can_call t =
            match t with
            | Type.Parametric { name = "type"; parameters = [Single Any] }
            | Parametric { name = "BoundMethod"; parameters = [Single Any; _] }
            | Parametric { name = "type"; parameters = [Single Unknown] }
            | Parametric { name = "BoundMethod"; parameters = [Single Unknown; _] }
            | Parametric { name = "typing.Type"; _ }
            | Type.Any
            | Type.Top
            | Type.Unknown -> true
            | Type.Union t_list -> List.for_all t_list ~f:can_call
            | _ -> false
          in

          let get_errors resolved_callee potential =
            match can_call resolved_callee, potential with
            | false, Some kind -> emit_error ~errors ~location ~kind
            | false, None -> emit_error ~errors ~location ~kind:(Error.NotCallable resolved_callee)
            | true, _ -> errors
          in
          get_errors resolved_callee (potential_missing_operator_error undefined_attributes)
        in

        {
          Resolved.resolution;
          errors;
          resolved=update_resolved_type Type.Any;
          resolved_annotation = None;
          base = None;
        }
      in
      
        
      let join_return_annotations
          ~resolution
          ~errors
          (found_return_annotations, not_found_return_annotations)
        =

        match found_return_annotations, (not_found_return_annotations |> List.rev) with
        | head :: tail, [] ->
          (* Log.dump "HO %a" Expression.pp expression; *)
            Some
              {
                Resolved.resolution;
                errors;
                resolved = List.fold ~f:(GlobalResolution.join global_resolution) ~init:head tail;
                resolved_annotation = None;
                base = None;
              }

        | (_,
          KnownCallable
          {
            selected_return_annotation =
              SignatureSelectionTypes.NotFound
                { closest_return_annotation; reason = Some reason };
            callable = unpacked_callable_and_self_argument;
            arguments;
            _;
          }
          :: _
          ) ->
            let errors =
              let error_kinds =
                let { TypeOperation.callable; self_argument } =
                  unpacked_callable_and_self_argument
                in

                errors_from_not_found
                  ~reason
                  ~callable
                  ~self_argument
                  ~global_resolution
                  ?original_target:target
                  ~callee_expression:(Callee.expression callee)
                  ~arguments:(Some arguments)
              in
              let emit errors (more_specific_error_location, kind) =
                let location = Option.value more_specific_error_location ~default:location in
                emit_error ~errors ~location ~kind
              in
              List.fold error_kinds ~init:errors ~f:emit
            in

            let { TypeOperation.callable; _ } =
              unpacked_callable_and_self_argument
            in
            (* List.iter errors ~f:(fun e -> Log.dump "ERROR : %a" Error.pp e); *)

            let _ = closest_return_annotation in
            (* Log.dump "HMM? %a == %a" Expression.pp expression Type.pp closest_return_annotation;
            Log.dump "!!! %a" Type.Callable.pp callable;  *)
            let resolved =
              if String.is_suffix (Expression.show (Callee.expression callee)) ~suffix:"__" 
              then (
                closest_return_annotation
                (* List.fold ~init:closest_return_annotation tail ~f:(fun acc t -> 
                  match t with
                  | KnownCallable
                    {
                      selected_return_annotation =
                        SignatureSelectionTypes.NotFound
                          { closest_return_annotation; _};
                      _;
                    } -> GlobalResolution.join global_resolution closest_return_annotation acc
                  | _ -> acc
                ) *)
              )
              else (
                match callable.kind with
                | Named reference ->
                  if (Reference.is_initialize reference) 
                    || (String.is_suffix (Reference.show reference) ~suffix:"TemporaryFile")
                    || (String.is_prefix (Reference.show reference) ~prefix:"re.")
                  then (
                    closest_return_annotation
                  )
                  else (
                    Type.Unknown
                  )
                | _ -> Type.Unknown
              )
            in

            Some
              {
                resolution;
                errors;
                resolved (* closest_return_annotation*);
                resolved_annotation = None;
                base = None;
              }

        | _ -> 
          
          None
      in
      let check_for_error ({ Resolved.resolved; errors; _ } as input) =

        let is_broadcast_error = function
          | Type.Parametric
              {
                name = "pyre_extensions.BroadcastError";
                parameters = [Type.Parameter.Single _; Type.Parameter.Single _];
              } ->
              true
          | _ -> false
        in
        match Type.collect resolved ~predicate:is_broadcast_error with
        | [] -> input
        | broadcast_errors ->
            let new_errors =
              List.fold broadcast_errors ~init:errors ~f:(fun current_errors error_type ->
                  match error_type with
                  | Type.Parametric
                      {
                        name = "pyre_extensions.BroadcastError";
                        parameters =
                          [Type.Parameter.Single left_type; Type.Parameter.Single right_type];
                      } ->
                      emit_error
                        ~errors:current_errors
                        ~location
                        ~kind:
                          (Error.BroadcastError
                              {
                                expression = { location; value };
                                left = left_type;
                                right = right_type;
                              })
                  | _ -> current_errors)
            in

            { input with resolved = Type.Unknown; errors = new_errors }
      in
      let select_return_annotation_bidirectional_inference
          ({
              callable =
                {
                  TypeOperation.callable =
                    { Type.Callable.implementation = { parameters; _ }; overloads; _ } as callable;
                  self_argument;
                };
              _;
            } as callable_data)
        =
        let callable_data_with_return_annotation, resolution, errors =
          match parameters, overloads with
          | Type.Callable.Defined record_parameters, [] ->
              let resolution, errors, reversed_arguments =
                let forward_argument (resolution, errors, reversed_arguments) argument =
                  let expression, kind = Ast.Expression.Call.Argument.unpack argument in
                  forward_expression ~resolution ~at_resolution expression
                  |> fun { resolution; errors = new_errors; resolved; _ } ->

                  ( resolution,
                    List.append new_errors errors,
                    { AttributeResolution.Argument.kind; expression = Some expression; resolved }
                    :: reversed_arguments )
                in
                List.fold arguments ~f:forward_argument ~init:(resolution, errors, [])
              in
              let arguments = List.rev reversed_arguments in
              let open AttributeResolution.SignatureSelection in
              prepare_arguments_for_signature_selection ~self_argument arguments
              |> get_parameter_argument_mapping
                    ~all_parameters:parameters
                    ~parameters:record_parameters
                    ~self_argument
              |> check_arguments_against_parameters
                    ~order:(GlobalResolution.full_order global_resolution)
                    ~resolve_mutable_literals:
                      (GlobalResolution.resolve_mutable_literals global_resolution)
                    ~resolve_with_locals:(resolve_expression_type_with_locals ~resolution ~at_resolution)
                    ~callable
              |> instantiate_return_annotation
                    ~order:(GlobalResolution.full_order global_resolution)
              |> fun selected_return_annotation ->

              { callable_data with arguments; selected_return_annotation }, resolution, errors
          | _ ->
              let resolution, errors, reversed_arguments =
                let forward_argument (resolution, errors, reversed_arguments) argument =
                  let expression, kind = Ast.Expression.Call.Argument.unpack argument in
                  forward_expression ~resolution ~at_resolution expression
                  |> fun { resolution; errors = new_errors; resolved; _ } ->

                  ( resolution,
                    List.append new_errors errors,
                    { AttributeResolution.Argument.kind; expression = Some expression; resolved }
                    :: reversed_arguments )
                in
                List.fold arguments ~f:forward_argument ~init:(resolution, errors, [])
              in
              let arguments = List.rev reversed_arguments in

              let selected_return_annotation =
                GlobalResolution.our_signature_select
                  ~global_resolution
                  ~resolve_with_locals:(resolve_expression_type_with_locals ~resolution ~at_resolution)
                  ~arguments
                  ~callable
                  ~self_argument
              in
              { callable_data with arguments; selected_return_annotation }, resolution, errors
        in
        let callable_data_with_selected_return_annotation =
          return_annotation_with_callable_and_self ~resolution callable_data_with_return_annotation
        in
        [KnownCallable callable_data_with_selected_return_annotation], resolution, errors
      in



      let callables_with_selected_return_annotations, resolution, errors =
        let callable_data_list = get_callables callee |> Option.value ~default:[] in

        match callable_data_list, Context.constraint_solving_style with
        | [KnownCallable callable_data], Configuration.Analysis.ExpressionLevel ->
          


            select_return_annotation_bidirectional_inference callable_data
        | callable_data_list, _ ->
            let resolution, errors, reversed_arguments =
              let forward_argument (resolution, errors, reversed_arguments) argument =
                let expression, kind = Ast.Expression.Call.Argument.unpack argument in
                forward_expression ~resolution ~at_resolution expression
                |> fun { resolution; errors = new_errors; resolved; _ } ->
                  (* TODO: handle slice *)
                  let resolved =
                    if Type.can_union ~f:(fun t -> Type.equal t (Primitive "slice")) resolved
                    then Type.filter_unknown resolved
                    else resolved
                  in

                  (* Log.dump "%a => %a" Expression.pp expression Type.pp resolved; *)

                ( resolution,
                  List.append new_errors errors,
                  { AttributeResolution.Argument.kind; expression = Some expression; resolved }
                  :: reversed_arguments )
              in
              List.fold arguments ~f:forward_argument ~init:(resolution, errors, [])
            in

            let arguments = List.rev reversed_arguments in

            let callable_data_list =
              List.filter_map callable_data_list ~f:(function
                  | UnknownCallableAttribute { callable_attribute; _ } ->
                      inverse_operator_callable ~callee_attribute:callable_attribute arguments
                  | KnownCallable callable_data ->
                      Some (KnownCallable { callable_data with arguments }))
            in

            let select_annotation_for_known_callable = function
              | KnownCallable
                  ({ callable = { TypeOperation.callable; self_argument }; arguments; _ } as
                  callable_data) ->

                  let selected_return_annotation =
                    GlobalResolution.our_signature_select
                      ~global_resolution
                      ~resolve_with_locals:(resolve_expression_type_with_locals ~resolution ~at_resolution)
                      ~arguments
                      ~callable
                      ~self_argument

                  in

                  

                  (* (match selected_return_annotation with
                  | Found { selected_return_annotation; _ } -> Log.dump "FOUND %a" Type.pp selected_return_annotation;
                  | NotFound { reason=Some reason; _ } -> Log.dump "%a" SignatureSelectionTypes.pp_reason reason;
                  | _ -> ();
                  ); *)

                  KnownCallable
                    (return_annotation_with_callable_and_self
                        ~resolution
                        { callable_data with selected_return_annotation })
              | UnknownCallableAttribute other -> UnknownCallableAttribute other
            in
            List.map callable_data_list ~f:select_annotation_for_known_callable, resolution, errors
      in

      let { StatementDefine.Signature.name; _ } = define_signature in

      (* Log.dump "HMM"; *)
      let ignore_lines = Context.ignore_lines in
      let is_ignore = 
        List.exists ignore_lines ~f:(fun { Ignore.location=ignore_location; _ } -> 
          let ignore_line = Location.line ignore_location in
          let node_line = Location.line location in

          ignore_line = node_line
        )
      in



      let resolution =
        if (Reference.is_test name || Reference.is_just_check name || is_ignore) then
          resolution
        else (
          List.fold callables_with_selected_return_annotations ~init:resolution ~f:(fun resolution callable ->
              match callable with
              | KnownCallable { callable = { TypeOperation.callable; self_argument }; arguments; _ } ->
                (* Log.dump "[[[ List Callable ]]]\n%a\n" Type.Callable.pp callable; *)

                let update_arg_type arg_type ret_type =
                  GlobalResolution.join global_resolution arg_type ret_type
                in 
                
                let allowed_list =
                  [
                    "object";
                    "int";
                    "float";
                    "str";
                    "bytes";
                    "dict";
                    "set";
                    "list";
                    "tuple";
                    "typing";
                    "json";
                    "hasattr";
                    "getattr";
                  ]
                in

                let _ = update_arg_type in
                
                let resolution =
                  let rec update_resolution (callable: Type.Callable.t) resolution =
                    (match callable.kind with
                    | Named reference when List.exists allowed_list ~f:(fun allowed -> String.equal allowed (Reference.first reference )) ->
                      resolution
                    | Named reference ->
                      if (Reference.is_test name && not (String.equal (Reference.last reference) "__init__")) then
                        resolution
                      else (

                        let params = callable.implementation.parameters in
                        let param_list = 
                        (match params with
                        | Defined defined_param_list ->
                          List.fold defined_param_list ~init:[] ~f:(fun acc param ->
                            (match param with
                            | PositionalOnly s -> ((String.concat ["__pyinder_"; string_of_int s.index; "__"]), s.annotation)::acc
                            | Named n -> (n.name, n.annotation)::acc
                            | _ -> (*print_endline "Other Param";*) acc
                            )
                          )
                        | _ -> (*print_endline "No defined";*) []
                        )
                        in
                        let param_list = List.rev param_list in
                        let param_type_init, revise_index = 
                        (match self_argument with
                        | Some t -> 
                          if List.length param_list == 0 then [], 1 else (
                            let s, _ = List.nth_exn param_list 0 in
                            [((s,t),None)], 1
                          ) 
                        | None -> (*Log.dump "No Self";*) [], 0
                        )
                        in

                        (* Log.dump "TEST HERE";
                        List.iter param_list ~f:(fun param ->
                          Log.dump "%s\n" param; 
                        );  *)

                        let param_type_list, resolution = List.foldi arguments ~init:(param_type_init, resolution) ~f:(fun idx (acc, resolution) arg ->
                          if List.length param_list <= (idx+revise_index) then acc, resolution
                          else
                          (match arg.kind with
                          | SingleStar | DoubleStar -> (*print_endline "This is Star Arg";*) acc, resolution
                          | Named s ->  
                            ((s.value, arg.resolved), arg.expression)::acc, resolution
                          | Positional -> 
                            let update_resolution =
                              (match arg.expression with
                              | Some exp -> (
                                match Node.value exp with
                                | Name name ->
(* 
                                  let param_identifier, param_annotation = List.nth_exn param_list (idx+revise_index) in
                                  let param_reference = Reference.create param_identifier in

                                  

                                  (* let target_func_arg_type = 
                                    OurDomain.ArgTypes.get_type func_arg_types param_identifier
                                  in *)

                                  
                                  let arg_type = 
                                    Resolution.resolve_expression_to_type resolution exp 
                                    |> (function
                                      | Type.Top -> Type.Unknown
                                      | t -> t
                                    )
                                  in
                                  (* let arg_annotation_type = 
                                    OurDomain.OurSummary.get_arg_annotation our_model callee_name
                                  in *)
                                  (* let ret_type = 
                                    OurDomain.ReferenceMap.find ret_var_type param_reference |> Option.value ~default:Type.Unknown
                                  in *)

                                  let _ = param_reference in

                                  let param_annotation = Type.top_to_unknown param_annotation |> Type.any_to_unknown in

                                  let new_arg_type = update_arg_type arg_type param_annotation in 

                                  (* Log.dump "%a => %a (%a)" Reference.pp param_reference Type.pp arg_type Type.pp param_annotation;
                                  Log.dump "New %a" Type.pp new_arg_type; *)


                                  (* Not Used
                                  let usedef_tables = 
                                    OurDomain.OurSummary.get_usedef_tables our_model callee_name 
                                    |> Option.value ~default:Usedef.UsedefStruct.empty
                                  in
                                  
                                            
                                  let new_arg_type =
                                    match Usedef.UsedefStruct.normal_exit usedef_tables with
                                    | Some usedef_state -> 
                                      if Usedef.UsedefState.is_undefined usedef_state param_reference
                                      then update_arg_type ~heuristic:true arg_type ret_type arg_annotation_type target_func_arg_type
                                      else update_arg_type arg_type ret_type arg_annotation_type target_func_arg_type
                                    | _ -> update_arg_type arg_type ret_type arg_annotation_type target_func_arg_type
                                  in
                                  *) 


                                  
                                  (* Log.dump "Callee %a Arg %a New type %a" Reference.pp callee_name Expression.pp exp Type.pp new_arg_type; *)
                                  
                                  let update_resolution = Resolution.refine_local_with_attributes resolution ~name ~annotation:(Annotation.create_mutable new_arg_type) in
                                  

                                  (* Log.dump "HMM? %a" Resolution.pp update_resolution; *)

                                  update_resolution *)

                                  let _ = name in
                                  resolution
                                | _ -> resolution
                              )
                                
                              | None -> resolution
                              )
                            in

                            let arg_resolved =
                              if Type.is_optional arg.resolved && (not !OurDomain.baseline) then (* For Baseline => False *)
                                (match arg.expression with
                                | Some exp -> (
                                  match Node.value exp with
                                  | Name name when is_simple_name name ->
                                    (match name_to_reference name with
                                    | Some ref when Reference.is_self ref || Reference.is_cls ref ->
                                      (match Resolution.get_local_with_attributes_of_temp ~name update_resolution with
                                      | Some t when Type.equal (Annotation.annotation t) arg.resolved ->
                                        Resolution.get_local_with_attributes_of_anno ~name update_resolution
                                        >>| Annotation.annotation
                                        |> Option.value ~default:Type.Unknown
                                      | _ -> arg.resolved
                                      )
                                    
                                    | _ -> arg.resolved
                                    )
                                  | _ -> arg.resolved
                                  )
                                | None -> arg.resolved
                                )
                              else
                                arg.resolved
                            in
                            let s, _ = List.nth_exn param_list (idx+revise_index) in
                            ((s, arg_resolved), arg.expression)::acc, update_resolution
                          )
                        )
                        in

                        
                        
                        let param_type_list = List.rev param_type_list in

                        
                        (* Log.dump "TEST HERE";
                        List.iter param_type_list ~f:(fun (param, typ) ->
                          Log.dump "%s -> %a\n" param Type.pp typ; 
                        );  *)
                        
                        
                        

                          (* Exclusive Self *)
                        let save_param_type_list, argument_list =
                          (match self_argument with
                          | Some _ -> 
                            if List.length param_list == 0 
                            then param_type_list 
                            else 
                              let _, no_self_param = List.split_n param_type_list 1 in
                              no_self_param
                          | None -> param_type_list
                          )
                          |> List.unzip 
                        in

                        


                        let join = GlobalResolution.join global_resolution in
                        let less_or_equal = GlobalResolution.less_or_equal global_resolution in

                        let arg_types = 
                          OurDomain.ArgTypes.make_arg_types save_param_type_list 
                          |> OurDomain.ArgTypes.map ~f:(Type.narrow_union ~join ~less_or_equal)
                        in

                        (* if OurDomain.is_inference_mode (OurDomain.load_mode ()) then *)
                          let { StatementDefine.Signature.name; _ } = define_signature in
                          let our_summary = !Context.our_summary in

                          (* Log.dump "??? %a" Reference.pp reference; *)

                          if !OurDomain.is_first && (OurDomain.is_inference_mode (OurDomain.load_mode ())) then (
                            let unique_analysis = OurDomain.OurSummary.get_unique_analysis !OurDomain.our_model name in

                            (* Log.dump "NAME : %a" Reference.pp name;
                            Log.dump "UNIQUE : %a" UniqueAnalysis.UniqueStruct.pp unique_analysis; *)

                            let param_varset = 
                              (
                                match UniqueAnalysis.UniqueStruct.find_pre_statements_of_location unique_analysis location with
                                | Some (state, loc) ->
                                  let _ = state, loc in
                                  let rec param_arg_map param_list argument_list acc =
                                    (match param_list, argument_list with
                                    | (param, _)::tl_param, arg::tl_arg ->
                                      
                                      let acc =
                                        (match arg with
                                        | Some exp -> (
                                          match Node.value exp with
                                          | Expression.Name name ->
                                            let ref = name_to_reference name in
                                            (match ref with
                                            | Some ref ->
                                              let var_set = UniqueAnalysis.UniqueState.get_all_relative_variables ~reference:ref state in
                                              let var_set =
                                                Reference.Set.filter var_set ~f:(fun v -> 
                                                  let v = 
                                                    if Reference.is_local v then Reference.delocalize_only_name v else v
                                                  in
                                                  Reference.is_cls v || Reference.is_self v || Reference.is_attribute v
                                                )
                                              in
                                              Identifier.Map.set acc ~key:param ~data:var_set
                                            | _ -> 
                                              
                                              acc
                                            )
                                          | _ -> acc
                                        )
                                        | _ -> acc
                                        )
                                      in
                                      param_arg_map tl_param tl_arg acc
                                    | _ -> acc
                                    )
                                  in

                                  (* Log.dump "ARG LIST : %i" (List.length argument_list); *)

                                  param_arg_map save_param_type_list argument_list Identifier.Map.empty
                                | _ ->
                                  Identifier.Map.empty
                              )
                            in
                            (* Log.dump "WHAT???"; *)
                            
                            (* List.iter save_param_type_list ~f:(fun (param, typ) ->
                              Log.dump "%s -> %a" param Type.pp typ; 
                            ); *)
                            (* Identifier.Map.iteri param_varset ~f:(fun ~key:param_varset ~data:varset ->
                              Log.dump "KEY %a" Identifier.pp param_varset;
                              Reference.Set.iter varset ~f:(fun v -> Log.dump "VAR %a" Reference.pp v);
                            ); *)
                            OurDomain.OurSummary.add_param_varset our_summary reference param_varset;
                          );

                          if !OurDomain.on_dataflow (* && (not (Reference.is_test name || Reference.is_just_check name)) *) then
                            OurDomain.OurSummary.add_new_signature ~join:(GlobalResolution.join global_resolution) ~caller_name:name our_summary reference arg_types;

                          ();
                          (* Context.our_summary := our_summary; *)
                        (* else (); *)

                        resolution
                      )
                    | _ -> 
                      (* TODO: Must Fix 
                      ex) x = goo
                          x(z)   ...
                      *)
                      let local_kind = 
                        let { Node.value; _ } = (Callee.expression callee) in
                        value |> (function
                        | Expression.Name t -> name_to_reference t
                        | _ -> None 
                        )
                      in
                      
                      (match local_kind with
                      | Some kind -> update_resolution { callable with kind=Named kind } resolution
                      | _ -> resolution 
                      )
                      
                    
                  )
                  in
                  update_resolution callable resolution
                  
                in
                resolution
              | _ -> resolution
        ))
      in


      (*
      Format.printf "[[[ Callee ]]]\n\n%a\n\n" Expression.pp (Callee.expression callee);
      Format.printf "[[[ Callee Type ]]]\n\n%a\n\n" Type.pp (Callee.resolved callee);

      let _ =
      (match Callee.resolved callee with
      | Callable { kind; _ } ->
        let kind =
          match kind with
          | Anonymous -> None
          | Named name -> Some name
        in
        let _ = kind in ()
      | Parametric { parameters; _ } ->
        List.iter parameters ~f:(fun param ->
          match param with
          | Single single ->
            (match single with
            | Callable { kind; _ } -> 
              let kind =
                match kind with
                | Anonymous -> None
                | Named name -> Format.printf "\n%a\n" Reference.pp name; Some name
              in
              let _ = kind in ()
            | _ -> print_endline "This is not Callable";
            )
          | CallableParameters _ -> print_endline "This is CallableParam";
          | Unpacked _ -> print_endline "This is Unpacked";
        );
      | _ -> print_endline "No Callable";
      )
      in

      List.iter arguments ~f:(fun arg -> 
        Format.printf "[[[ Argument Value ]]]\n\n%a\n\n" Expression.pp arg.value;
        (match arg.name with
        | Some n -> Format.printf "WOW \n\n%a\n\n" Identifier.pp n.value;
        | None -> ()
        )
      );
      *)

      
      (* Log.dump "[[[ Callee ]]]\n\n%a ==> %a\n\n" Expression.pp (Callee.expression callee) Type.pp (Callee.resolved callee);
      (List.iter callables_with_selected_return_annotations ~f:(function
              | KnownCallable { callable = { TypeOperation.callable; _ }; _ } -> Log.dump "??? %a" Type.Callable.pp callable; ()
              | _ -> ())); *)


      Context.Builder.add_callee
        ~global_resolution
        ~target
        ~callables:
          (List.filter_map callables_with_selected_return_annotations ~f:(function
              | KnownCallable { callable = { TypeOperation.callable; _ }; _ } -> Some callable
              | _ -> None))
        ~arguments
        ~dynamic
        ~qualifier:Context.qualifier
        ~callee_type:(Callee.resolved callee)
        ~callee:(Callee.expression callee);

      let found_return_annotations, not_found_return_annotations, undefined_attributes =
        List.partition3_map
          callables_with_selected_return_annotations
          ~f:extract_found_not_found_unknown_attribute
      in
      
      

      let resolved =
        join_return_annotations
          ~resolution
          ~errors
          (found_return_annotations, not_found_return_annotations)

        |> (function
                    | Some resolved -> 
                      (* Log.dump "??? %a" Type.pp resolved.resolved; *)
                      { resolved with resolved=update_resolved_type resolved.resolved}
                    | None -> 
                      resolved_for_bad_callable ~resolution ~errors undefined_attributes)

        |> check_for_error
      in


      let forward_argument ~resolution argument =
        let expression, _ = Ast.Expression.Call.Argument.unpack argument in
        forward_expression ~resolution ~at_resolution expression
        |> fun { resolved; _ } ->
          match resolved with
          | Type.Parametric (* Column Default Type 처리 *)
          { name = "type" | "typing.Type"; parameters=[Single (Primitive s)]; } 
          | Primitive s  
            when String.is_prefix s ~prefix:"sqlalchemy.sql.sqltypes" ->
              if String.is_suffix ~suffix:"String" s then Type.string
              else if String.is_suffix ~suffix:"Float" s then Type.float
              else if String.is_suffix ~suffix:"Integer" s then Type.integer
              else if String.is_suffix ~suffix:"Boolean" s then Type.bool
              else Type.Unknown
          | _ -> resolved
      in

      let callee_reference =
        let { Node.value; _ } = Callee.expression callee in
        match value with
        | Name n -> name_to_reference n
        | _ -> None
      in

      let callee_resolved = Callee.resolved callee in

      (* Log.dump "CALLEE %a => %a" Expression.pp expression Type.pp callee_resolved; *)

      let get_typed_dict_type_of_get callee_resolved t =
        let get_typed_dict_type = 
          resolved_dict_get callee_resolved
        in

        (match get_typed_dict_type with
        | Some get_typed_dict_type -> 
          (* Log.dump "%a" Expression.pp expression; *)
          (* Log.dump "HERE?? %a ==> %a" Type.pp t Type.pp get_typed_dict_type; *)
          { resolved with resolved = get_typed_dict_type }
        | _ ->
          (match t with
          | Type.Union [NoneType; Unknown] | Union [Unknown; NoneType] -> resolved
          | Type.Union t -> { resolved with resolved=Type.Union (List.filter t ~f:(fun sub -> not (Type.is_none sub))) }
          | _ -> resolved
          )
        )
      in

      let resolved_builtin_functions (resolved: Resolved.t) callee callee_resolved =
        let _ = callee in
        match callee_resolved with
        | Type.Parametric (* zip 처리 *)
          { name = "type" | "typing.Type"; parameters=[Single (Primitive "zip")]; } ->
            let x = resolved_zip callee_resolved |> update_resolved_type in
            
            { resolved with resolved = x }
        | Type.Parametric (* Column 처리 *)
          { name = "type" | "typing.Type"; parameters=[Single (Primitive "sqlalchemy.sql.schema.Column")]; } 
        | Type.Parametric (* Column 처리 *)
          { name = "type" | "typing.Type"; parameters=[Single (Primitive "sqlalchemy.Column")]; } 
        | Primitive "sqlalchemy.sql.schema.Column"
        | Primitive "sqlalchemy.Column"
          ->
            let real_type =
              (match arguments with
              | [] -> Type.Unknown
              | hd::_ -> forward_argument ~resolution hd
              )
            in
            (* Log.dump "HMM : %a" Type.pp real_type; *)
            { resolved with resolved=real_type; resolved_annotation=None }
        | Primitive "luigi.parameter.Parameter" | Primitive "parameter.Paramter" | Primitive "Parameter" ->
          { resolved with resolved=Type.Unknown; resolved_annotation=None }
        | Primitive "luigi.parameter.IntParameter" | Primitive "parameter.IntParamter" | Primitive "IntParameter" ->
          { resolved with resolved=Type.integer; resolved_annotation=None }
        | Primitive "luigi.parameter.FloatParameter" | Primitive "parameter.FloatParamter" | Primitive "FloatParameter" ->
          { resolved with resolved=Type.float; resolved_annotation=None }
        | Primitive "luigi.parameter.BoolParameter" | Primitive "parameter.BoolParamter" | Primitive "BoolParameter" ->
          { resolved with resolved=Type.bool; resolved_annotation=None }
        | Type.Parametric (* dict.get 처리 *)
            { name = "BoundMethod"; parameters = [Single (Callable { kind = Named name; _ }); Single _] } when String.equal (Reference.show name) "dict.get" ->
              get_typed_dict_type_of_get callee_resolved resolved.resolved
        | Type.Parametric (* Column Default Type 처리 *)
          { name = "type" | "typing.Type"; parameters=[Single (Primitive s)]; } 
        | Primitive s  
          when String.is_prefix s ~prefix:"sqlalchemy.sql.sqltypes" ->
            if String.is_suffix ~suffix:"String" s then { resolved with resolved=Type.string; resolved_annotation=None }
            else if String.is_suffix ~suffix:"Float" s then { resolved with resolved=Type.float; resolved_annotation=None }
            else if String.is_suffix ~suffix:"Integer" s then { resolved with resolved=Type.integer; resolved_annotation=None }
            else if String.is_suffix ~suffix:"Boolean" s then { resolved with resolved=Type.bool; resolved_annotation=None }
            else { resolved with resolved=Type.Unknown; resolved_annotation=None }
        | _ -> 
          let new_t = resolved_dict_getitem callee_resolved in

          
          
          match new_t with
          | Some new_t ->
            
            { resolved with resolved = new_t |> update_resolved_type }
          | None -> 
            
            (match resolved.resolved, callee_reference, callee_resolved with
            | Type.Unknown, Some callee_reference, _
            when String.is_suffix ~suffix:"$zip" (Reference.show callee_reference) 
            || String.is_suffix ~suffix:".zip" (Reference.show callee_reference)
            ->
              let heuristic_callee = 
                Type.Parametric { name = "type"; parameters=[Single (Primitive "zip")]; }
              in
              let x = resolved_zip heuristic_callee |> update_resolved_type in
              (* if String.is_substring (Reference.show define_name) ~substring:"_write_col_header"
                then (
                  (* Log.dump "%a" Resolution.pp resolved.resolution; *)
                  Log.dump "ZIP %a" Type.pp x;
                ); *)
              { resolved with resolved = x }
            | t, Some callee_reference, _ when 
              String.is_suffix ~suffix:"get" (Reference.show callee_reference) &&
              (Type.can_union ~f:Type.is_dict (target |> Option.value ~default:Type.Unknown))
              ->

              (* let update_flag = 
                (match callee_resolved with
                  | Type.Parametric (* dict.get 처리 *)
                    { name = "BoundMethod"; parameters = [Single (Callable { kind = Named name; _ }); Single _] } when String.equal (Reference.show name) "dict.get" 
                    -> true
                  | _ -> false
                )
                || 
              in *)

              get_typed_dict_type_of_get callee_resolved t
            | _, _
              ,Type.Parametric (* dict.update 처리 *)
              { name = "BoundMethod"; parameters = [Single (Callable { kind = Named name; _ }); _] } 
              when String.equal (Reference.show name) "typing.MutableMapping.update"
              -> { resolved with resolved=Type.dictionary ~key:Type.Unknown ~value:Type.Unknown; }

              (* let update_flag = 
                (match callee_resolved with
                  | Type.Parametric (* dict.get 처리 *)
                    { name = "BoundMethod"; parameters = [Single (Callable { kind = Named name; _ }); Single _] } when String.equal (Reference.show name) "dict.get" 
                    -> true
                  | _ -> false
                )
                || 
              in *)


            | _ -> 
              resolved
            )
            
          (* if Type.equal callee_resolved new_t 
          then (
            match resolved.resolved, callee_reference with
            | Type.Unknown, Some callee_reference when String.is_suffix ~suffix:"$zip" (Reference.show callee_reference) ->
              let heuristic_callee = 
                Type.Parametric { name = "type"; parameters=[Single (Primitive "zip")]; }
              in
              { resolved with resolved = resolved_zip heuristic_callee |> update_resolved_type }
            | _ -> resolved
          )
          else (
            { resolved with resolved = new_t |> update_resolved_type } 
          )*)
      in

      let resolved_def_variables (resolved: Resolved.t) callee callee_resolved =
        match Node.value (Callee.expression callee) with
        | Expression.Name name when is_simple_name name ->
          (match callee_resolved with
          | Type.Parametric { name = "BoundMethod"; parameters = [Single (Callable { kind = Named name; _ }); _]; _ } ->
            let final_model = !OurDomain.our_model in
            let vartypeset = OurDomain.OurSummary.get_usedef_defined final_model name in
            let new_resolution =
              OurDomain.VarTypeSet.fold vartypeset ~init:resolved.resolution ~f:(fun ~key ~data resolution ->
                  let name = create_name_from_reference_without_location key in
                  let typ = OurDomain.TypeSet.fold data ~init:Type.Bottom ~f:(fun acc t -> GlobalResolution.join global_resolution acc t) in

                  (match typ with
                  | Type.Bottom -> resolution
                  | _ -> 
                    let annotation = Annotation.create_mutable typ in
                    Resolution.refine_local_with_attributes resolution ~name ~annotation
                  )
                  
              )
            in

            { resolved with resolution=new_resolution; }
          | _ -> resolved
          )
        | _ -> resolved
      in

  
      (* List.iter resolved.errors ~f:(fun e -> Log.dump "%a" Error.pp e); *)


      let x = resolved_builtin_functions resolved callee callee_resolved in

      

      let resolved = resolved_def_variables x callee callee_resolved in

      let _ = define_name in

      
      (* if String.is_substring (Reference.show define_name) ~substring:"series.order"
        && (String.is_substring (Expression.show (Callee.expression callee)) ~substring:"solveset")
        then (
          (* Log.dump "%a" Resolution.pp resolved.resolution; *)
          Log.dump "END Callee %a ==> %a" Expression.pp (Callee.expression callee) Type.pp (resolved.resolved);
          List.iter resolved.errors ~f:(fun e -> Log.dump "%a" Error.pp e);
        ); *)

        (* if String.is_substring (Reference.show define_name) ~substring:"_write_col_header"
          && (String.is_substring (Expression.show expression) ~substring:"columns.format")
          then (
            (* Log.dump "%a" Resolution.pp resolved.resolution; *)
            Log.dump "END Callee %a ==> %a" Expression.pp expression Type.pp (resolved.resolved)
          ); *)


        (* if String.equal (Reference.show define_name) "salt.state.State.call"
          && (String.is_substring (Expression.show expression) ~substring:"ret.update")
          then (
            Log.dump "%a" Resolution.pp resolved.resolution;
            Log.dump "END Callee %a ==> %a" Expression.pp expression Type.pp (resolved.resolved)
          );

        if String.equal (Reference.show define_name) "salt.state.State.call"
          && (String.is_substring (Expression.show expression) ~substring:"22222")
          then (
            Log.dump "%a" Resolution.pp resolved.resolution;
            Log.dump "END Callee %a ==> %a" Expression.pp expression Type.pp (resolved.resolved)
          );

          if String.equal (Reference.show define_name) "salt.state.State.call"
            && (String.is_substring (Expression.show expression) ~substring:"33333")
            then (
              Log.dump "%a" Resolution.pp resolved.resolution;
              Log.dump "END Callee %a ==> %a" Expression.pp expression Type.pp (resolved.resolved)
            );
 
            if String.equal (Reference.show define_name) "salt.state.State.call"
              && (String.is_substring (Expression.show expression) ~substring:"44444")
              then (
                Log.dump "%a" Resolution.pp resolved.resolution;
                Log.dump "END Callee %a ==> %a" Expression.pp expression Type.pp (resolved.resolved)
              ); *)
   

      (* Log.dump "Callee %a Type %a" Expression.pp (Callee.expression callee) Type.pp (Callee.resolved callee); *)
      (* Log.dump ">>> %a" Expression.pp expression;
      Log.dump "END Callee %a ==> %a (%a)" Expression.pp (Callee.expression callee) Type.pp (resolved.resolved) Type.pp x.resolved; *)

      (* Log.dump "END Callee %a ==> %a (%a)" Expression.pp (Callee.expression callee) Type.pp (resolved.resolved) Type.pp x.resolved; *)

      (* if String.is_substring (Reference.show define_name) ~substring:"settings" 
        && String.is_substring (Expression.show (Callee.expression callee)) ~substring:"getboolean" 
        then (
          Log.dump "END Callee %a ==> %a (%a)" Expression.pp (Callee.expression callee) Type.pp (resolved.resolved) Type.pp x.resolved;
        ); *)
      resolved
      (* ) *)
      
    in

    let xxx = (

    match value with
    | Await expression -> (
        let { Resolved.resolution; resolved; errors; _ } =
          forward_expression ~resolution ~at_resolution expression
        in

        match resolved with
        | Type.Any ->
            { Resolved.resolution; resolved = Type.Any; errors; resolved_annotation = None; base = None }
        | Type.Unknown ->
          { resolution; resolved = Type.Unknown; errors; resolved_annotation = None; base = None }
        | _ -> (
            match
              GlobalResolution.extract_type_parameters
                global_resolution
                ~target:"typing.Awaitable"
                ~source:resolved
            with
            | Some [awaited_type] ->
                {
                  resolution;
                  resolved = awaited_type;
                  errors;
                  resolved_annotation = None;
                  base = None;
                }
            | _ ->
                let errors =
                  emit_error ~errors ~location ~kind:(Error.IncompatibleAwaitableType resolved)
                in
                { resolution; resolved = Type.Unknown; errors; resolved_annotation = None; base = None }
            ))
    | BooleanOperator { BooleanOperator.left; operator; right } -> (
        let {
          Resolved.resolution = resolution_left;
          resolved = resolved_left;
          errors = errors_left;
          _;
        }
          =
          forward_expression ~resolution ~at_resolution left
        in
        let left_assume =
          match operator with
          | BooleanOperator.And -> left
          | BooleanOperator.Or -> normalize (negate left)
        in
        (* Log.dump "LEFT %a : %a" Expression.pp left_assume Type.pp resolved_left; *)
        match refine_resolution_for_assert ~resolution:resolution_left ~at_resolution left_assume with
        | Unreachable ->
            {
              Resolved.resolution = resolution_left;
              resolved = resolved_left;
              errors = errors_left;
              resolved_annotation = None;
              base = None;
            }
        | Value refined_resolution -> (
          (* Log.dump "HMM %a (%a) : %a" Expression.pp expression Type.pp resolved_left Resolution.pp refined_resolution; *)
          
            let forward_right resolved_left =
              let {
                Resolved.resolution = resolution_right;
                resolved = resolved_right;
                errors = errors_right;
                _;
              }
                =
                forward_expression ~resolution:refined_resolution ~at_resolution right
              in
              let resolved =
                match resolved_left with
                | None -> resolved_right
                | Some resolved_left ->
                    GlobalResolution.join global_resolution resolved_left resolved_right
              in
              {
                Resolved.resolution =
                  Resolution.outer_join_refinements resolution_left resolution_right;
                errors = List.append errors_left errors_right;
                resolved;
                resolved_annotation = None;
                base = None;
              }
            in
            
            let resolved_left = 
              if Type.is_primitive_bool resolved_left
              then Type.Unknown
              else resolved_left
            in
            match resolved_left, operator with
            | resolved_left, BooleanOperator.And when Type.is_falsy resolved_left ->
                (* false_expression and b has the same type as false_expression *)
                {
                  resolution = resolution_left;
                  errors = errors_left;
                  resolved = resolved_left;
                  resolved_annotation = None;
                  base = None;
                }
            | resolved_left, BooleanOperator.Or when Type.is_truthy resolved_left ->
                (* true_expression or b has the same type as true_expression *)
                {
                  resolution = resolution_left;
                  errors = errors_left;
                  resolved = resolved_left;
                  resolved_annotation = None;
                  base = None;
                }
            | resolved_left, BooleanOperator.Or when Type.is_falsy resolved_left ->
                (* false_expression or b has the same type as b *)
                forward_right None
            | resolved_left, BooleanOperator.And when Type.is_truthy resolved_left ->
                (* true_expression and b has the same type as b *)
                forward_right None
            | Type.Union parameters, BooleanOperator.Or ->
                (* If type_of(a) = Union[A, None], then type_of(a or b) = Union[A, type_of(b) under
                    assumption type_of(a) = None] *)
                let not_none_left =
                  Type.union
                    (List.filter parameters ~f:(fun parameter -> not (Type.is_none parameter)))
                in
                forward_right (Some not_none_left)
            | _, _ -> forward_right (Some resolved_left)))
    | Call { callee = { Node.value = Name (Name.Identifier "super"); _ } as callee; arguments } -> (
        let metadata =
          Resolution.parent resolution
          >>| (fun parent -> Type.Primitive (Reference.show parent))
          >>= GlobalResolution.class_metadata global_resolution
        in
        (* Resolve `super()` calls. *)
        let superclass { ClassMetadataEnvironment.successors; extends_placeholder_stub_class; _ } =
          if extends_placeholder_stub_class then
            None
          else
            List.find successors ~f:(GlobalResolution.class_exists global_resolution)
        in
        match metadata >>= superclass with
        | Some superclass ->
            let resolved = Type.Primitive superclass in
            {
              resolution;
              errors = [];
              resolved;
              resolved_annotation = None;
              base = Some (Super resolved);
            }
        | None ->
            let { Resolved.resolved; _ } = forward_expression ~resolution ~at_resolution callee in
            forward_callable
              ~resolution
              ~errors:[]
              ~target:None
              ~callee:(Callee.NonAttribute { expression = callee; resolved })
              ~dynamic:false
              ~arguments)
    | Call
        {
          callee = { Node.value = Name (Name.Identifier "type"); _ };
          arguments = [{ Call.Argument.value; _ }];
        } ->
        (* Resolve `type()` calls. *)
        let resolved = resolve_expression_type ~resolution ~at_resolution value |> Type.meta in
        { resolution; errors = []; resolved; resolved_annotation = None; base = None }
    | Call { callee = { Node.location; value = Name (Name.Identifier "reveal_locals") }; _ } ->
        (* Special case reveal_locals(). *)
        let from_annotation (reference, unit) =
          let name = reference in
          let annotation =
            Option.value ~default:(Annotation.create_mutable Type.Unknown) (Refinement.Unit.base unit)
          in
          { Error.name; annotation }
        in
        let annotations = Map.to_alist (Resolution.annotation_store resolution).annotations in
        let temporary_annotations =
          Map.to_alist (Resolution.annotation_store resolution).temporary_annotations
        in
        let revealed_locals = List.map ~f:from_annotation (temporary_annotations @ annotations) in
        let errors = emit_error ~errors:[] ~location ~kind:(Error.RevealedLocals revealed_locals) in
        { resolution; errors; resolved = Type.none; resolved_annotation = None; base = None }
    | Call
        {
          callee = { Node.location; value = Name (Name.Identifier "reveal_type") };
          arguments = { Call.Argument.value; _ } :: remainder;
        } ->
        (* Special case reveal_type(). *)
        let qualify =
          match remainder with
          | [
            {
              Call.Argument.name = Some { Node.value = name; _ };
              value = { Node.value = Constant Constant.True; _ };
            };
          ]
            when Identifier.equal name "$parameter$qualify" ->
              true
          | _ -> false
        in
        let errors =
          emit_error
            ~errors:[]
            ~location
            ~kind:
              (Error.RevealedType
                  { expression = value; annotation = resolve_expression ~resolution ~at_resolution value; qualify })
        in
        { resolution; errors; resolved = Type.none; resolved_annotation = None; base = None }
    | Call
        {
          callee = { Node.location; value = Name name };
          arguments = [{ Call.Argument.value = cast_annotation; _ }; { Call.Argument.value; _ }];
        }
      when Option.equal
              Reference.equal
              (name_to_reference name)
              (Some (Reference.create "typing.cast"))
            || Option.equal
                Reference.equal
                (name_to_reference name)
                (Some (Reference.create "pyre_extensions.safe_cast")) ->
        let contains_literal_any = Type.expression_contains_any cast_annotation in
        let errors, cast_annotation = parse_and_check_annotation ~resolution cast_annotation in
        let resolution, resolved, errors =
          let { Resolved.resolution; resolved; errors = value_errors; _ } =
            forward_expression ~resolution ~at_resolution value
          in
          resolution, resolved, List.append value_errors errors
        in
        let errors =
          if contains_literal_any then
            emit_error
              ~errors
              ~location
              ~kind:
                (Error.ProhibitedAny
                    {
                      missing_annotation =
                        {
                          Error.name = name_to_reference_exn name;
                          annotation = None;
                          given_annotation = Some cast_annotation;
                          evidence_locations = [];
                          thrown_at_source = true;
                        };
                      is_type_alias = false;
                    })
          else if Type.equal cast_annotation resolved then
            emit_error ~errors ~location ~kind:(Error.RedundantCast resolved)
          else if
            Reference.equal
              (name_to_reference_exn name)
              (Reference.create "pyre_extensions.safe_cast")
            && GlobalResolution.less_or_equal
                  global_resolution
                  ~left:cast_annotation
                  ~right:resolved
          then
            emit_error
              ~errors
              ~location
              ~kind:(Error.UnsafeCast { expression = value; annotation = cast_annotation })
          else
            errors
        in
        { resolution; errors; resolved = cast_annotation; resolved_annotation = None; base = None }
    | Call
        {
          callee = { Node.value = Name (Name.Identifier "isinstance"); _ } as callee;
          arguments =
            [{ Call.Argument.value = expression; _ }; { Call.Argument.value = annotations; _ }] as
            arguments;
        } ->
        let { Resolved.resolved; _ } = forward_expression ~resolution ~at_resolution callee in
        let callables =
          match resolved with
          | Type.Callable callable -> [callable]
          | _ -> []
        in
        Context.Builder.add_callee
          ~global_resolution
          ~target:None
          ~callables
          ~arguments
          ~dynamic:false
          ~qualifier:Context.qualifier
          ~callee_type:resolved
          ~callee;

        (* Be angelic and compute errors using the typeshed annotation for isinstance. *)

        (* We special case type inference for `isinstance` in asserted, and the typeshed stubs are
            imprecise (doesn't correctly declare the arguments as a recursive tuple. *)
        let resolution, errors =
          let { Resolved.resolution; errors; _ } = forward_expression ~resolution ~at_resolution expression in
          let resolution, errors, annotations =
            let rec collect_types (state, errors, collected) = function
              | { Node.value = Expression.Tuple annotations; _ } ->
                  List.fold annotations ~init:(state, errors, collected) ~f:collect_types
              | expression ->
                  let { Resolved.resolution; resolved; errors = expression_errors; _ } =
                    forward_expression ~resolution ~at_resolution expression
                  in

                  (* Log.dump "?? %a ==> %a" Expression.pp expression Type.pp resolved; *)

                  let new_annotations =
                    match resolved with
                    | Type.Tuple (Concrete annotations) ->
                        List.map annotations ~f:(fun annotation ->
                            annotation, Node.location expression)
                    | Type.Tuple (Concatenation concatenation) ->
                        Type.OrderedTypes.Concatenation.extract_sole_unbounded_annotation
                          concatenation
                        >>| (fun element_annotation ->
                              [element_annotation, Node.location expression])
                        |> Option.value ~default:[resolved, Node.location expression]
                    | annotation -> [annotation, Node.location expression]
                  in
                  resolution, List.append expression_errors errors, new_annotations @ collected
            in
            collect_types (resolution, errors, []) annotations
          in
          let add_incompatible_non_meta_error errors (non_meta, location) =
            emit_error
              ~errors
              ~location
              ~kind:
                (Error.IncompatibleParameterType
                    {
                      name = None;
                      position = 2;
                      callee = Some (Reference.create "isinstance");
                      mismatch =
                        {
                          Error.actual = non_meta;
                          expected =
                            Type.union
                              [
                                Type.meta Type.Any;
                                Type.Tuple
                                  (Type.OrderedTypes.create_unbounded_concatenation
                                    (Type.meta Type.Any));
                              ];
                          due_to_invariance = false;
                        };
                    })
          in

          let rec is_compatible annotation =
            match annotation with
            | _ when Type.is_meta annotation or Type.is_untyped annotation -> true
            | Type.Primitive "typing._Alias" -> true
            | Type.Tuple (Concatenation concatenation) ->
                Type.OrderedTypes.Concatenation.extract_sole_unbounded_annotation concatenation
                >>| (fun annotation -> Type.is_meta annotation)
                |> Option.value ~default:false
            | Type.Tuple (Type.OrderedTypes.Concrete annotations) ->
                List.for_all ~f:Type.is_meta annotations
            | Type.Union annotations -> List.for_all annotations ~f:is_compatible
            | Type.NoneType -> false
            | _ -> false
          in
          let errors =
            List.find annotations ~f:(fun (annotation, _) 
              ->
                (* Log.dump "?? %a" Type.pp annotation;  *)
                not (is_compatible annotation)
            )
            >>| add_incompatible_non_meta_error errors
            |> Option.value ~default:errors
          in

          (* 
          TODO:
              Set possiblecondition 
              How to convert parametric to type.union?
          *)

          (*
          (match Node.value expression with
          | Name name ->

            let make_possible_type annotation =
              (match annotation with
              | Type.Parametric { parameters = [Single (Primitive _ as element)]; _ } when Type.is_meta annotation 
                -> element
              | _ when Type.is_meta annotation or Type.is_untyped annotation -> Type.Bottom
              | Type.Primitive "typing._Alias" -> Type.Bottom
              | Type.Tuple (Concatenation concatenation) ->
                  Type.OrderedTypes.Concatenation.extract_sole_unbounded_annotation concatenation
                  |> Option.value ~default:Type.Bottom
              | Type.Tuple (Type.OrderedTypes.Concrete annotations) ->
                  Type.union annotations
              | Type.Union annotations -> Type.union annotations
              | _ ->Type.Bottom
              )
            in
            let possible_type = List.fold annotations ~init:Type.Bottom ~f:(fun sofar (annotation, _) -> Type.union [sofar; make_possible_type annotation] ) in
            let new_resolution = Resolution.new_local_with_attributes resolution ~name ~annotation:(Annotation.create_mutable possible_type) in
            let new_store = Resolution.get_annotation_store new_resolution in
            (*Format.printf "[[[ NEW RESOLUTION ]]] \n\n%a\n\n%a\n\n" Type.pp possible_type Resolution.pp new_resolution;*)
            (**)
            if OurDomain.is_inference_mode (OurDomain.load_mode ()) then
              let {StatementDefine.Signature.name; _} = define_signature in
              let our_model = OurDomain.load_summary name in
              let store_join = Refinement.Store.join_with_merge ~global_resolution:(Resolution.global_resolution resolution) in
              let our_model = 
                OurDomain.OurSummary.join_with_merge_function_possiblecondition ~store_join our_model name new_store
              in
              OurDomain.save_summary our_model name
            else ()
            
          | _ -> ()
          );
          *)
          
          resolution, errors
        in

        
        (*Format.printf "\n\n%a -> %a\n%a\n\n" Expression.pp expression Expression.pp annotations Resolution.pp resolution;*)
        
        { resolution; errors; resolved = Type.bool; resolved_annotation = None; base = None }
    | Call
        {
          callee =
            {
              Node.value =
                Name
                  (Name.Attribute
                    { attribute = ("assertIsNotNone" | "assertTrue") as attribute; base; _ });
              _;
            } as callee;
          arguments =
            ( [{ Call.Argument.value = expression; _ }]
            | [{ Call.Argument.value = expression; _ }; _] ) as arguments;
        } ->
        let resolution, resolved_callee, errors, resolved_base =
          let resolution, assume_errors =
            let post_resolution, errors = forward_assert ~resolution ~at_resolution expression in
            resolution_or_default post_resolution ~default:resolution, errors
          in
          let { Resolved.resolution; resolved; errors = callee_errors; base = resolved_base; _ } =
            forward_expression ~resolution ~at_resolution callee
          in
          resolution, resolved, List.append assume_errors callee_errors, resolved_base
        in
        forward_callable
          ~resolution
          ~errors
          ~target:None
          ~dynamic:true
          ~callee:
            (Callee.Attribute
                {
                  base =
                    {
                      expression = base;
                      resolved_base =
                        Resolved.resolved_base_type resolved_base |> Option.value ~default:Type.Unknown;
                    };
                  attribute = { name = attribute; resolved = resolved_callee };
                  expression = callee;
                })
          ~arguments
    | Call
        {
          callee =
            {
              Node.value = Name (Name.Attribute { attribute = "assertFalse" as attribute; base; _ });
              _;
            } as callee;
          arguments =
            ( [{ Call.Argument.value = expression; _ }]
            | [{ Call.Argument.value = expression; _ }; _] ) as arguments;
        } ->
        let resolution, resolved_callee, errors, resolved_base =
          let resolution, assume_errors =
            let post_resolution, errors = forward_assert ~resolution ~at_resolution (negate expression) in
            resolution_or_default post_resolution ~default:resolution, errors
          in
          let { Resolved.resolution; resolved; errors = callee_errors; base = resolved_base; _ } =
            forward_expression ~resolution ~at_resolution callee
          in
          resolution, resolved, List.append assume_errors callee_errors, resolved_base
        in
        forward_callable
          ~resolution
          ~errors
          ~target:None
          ~dynamic:true
          ~callee:
            (Callee.Attribute
                {
                  base =
                    {
                      expression = base;
                      resolved_base =
                        Resolved.resolved_base_type resolved_base |> Option.value ~default:Type.Unknown;
                    };
                  attribute = { name = attribute; resolved = resolved_callee };
                  expression = callee;
                })
          ~arguments
    | Call
        {
          callee = { Node.value = Name (Name.Identifier "getattr"); _ };
          arguments =
            { Call.Argument.value = base; _ }
            :: { Call.Argument.value = attribute_expression; _ } :: (([] | [_]) as default_argument);
        } -> (
        let ({ Resolved.errors; resolution; _ } as base_resolved) =
          forward_expression ~resolution ~at_resolution base
        in
        let resolution, errors, attribute_resolved =
          forward_expression ~resolution ~at_resolution attribute_expression
          |> fun { resolution; errors = attribute_errors; resolved = attribute_resolved; _ } ->
          resolution, List.append attribute_errors errors, attribute_resolved
        in
        let resolution, errors, has_default =
          match default_argument with
          | [{ Call.Argument.value = default_expression; _ }] ->
              forward_expression ~resolution ~at_resolution default_expression
              |> fun { resolution; errors = default_errors; _ } ->
              resolution, List.append default_errors errors, true
          | _ -> resolution, errors, false
        in
        match attribute_resolved with
        | Type.Literal (String (LiteralValue attribute)) ->
            resolve_attribute_access
              ~base_resolved:{ base_resolved with Resolved.resolution; errors }
              ~base
              ~special:false
              ~attribute
              ~has_default
        | _ ->
            {
              Resolved.resolution;
              errors;
              resolved = Type.Unknown;
              base = None;
              resolved_annotation = None;
            })
    | Call call ->
      (* 이게 일반적인 Call *)

        let { Call.callee; arguments } = AnnotatedCall.redirect_special_calls ~resolution call in
        let {
          Resolved.errors = callee_errors;
          resolved = resolved_callee;
          base = resolved_base;
          resolution = callee_resolution;
          _;
        }
          =
          forward_expression ~resolution ~at_resolution callee
        in  
       
        let { Resolved.resolution = updated_resolution; resolved; errors = updated_errors; _ } =
          let target_and_dynamic resolved_callee =
            if Type.is_meta resolved_callee then
              Some (Type.single_parameter resolved_callee), false
            else
              match resolved_base with
              | Some (Resolved.Instance resolved) when not (Type.is_top resolved) ->
                  Some resolved, true
              | Some (Resolved.Class resolved) when not (Type.is_top resolved) ->
                  Some resolved, false
              | Some (Resolved.Super resolved) when not (Type.is_top resolved) ->
                  Some resolved, false
              | _ -> None, false
          in
          let create_callee resolved =
            match Node.value callee with
            | Expression.Name (Name.Attribute { base; attribute; _ }) ->
                Callee.Attribute
                  {
                    base =
                      {
                        expression = base;
                        resolved_base =
                          Resolved.resolved_base_type resolved_base
                          |> Option.value ~default:Type.Unknown;
                      };
                    attribute = { name = attribute; resolved = resolved_callee };
                    expression = callee;
                  }
            | _ -> Callee.NonAttribute { expression = callee; resolved }
          in
          match resolved_callee with
          | Type.Parametric { name = "type"; parameters = [Single (Type.Union resolved_callees)] }
            ->
              let forward_inner_callable (resolution, errors, annotations) inner_resolved_callee =
                let target, dynamic = target_and_dynamic inner_resolved_callee in
                forward_callable
                  ~resolution
                  ~errors:[]
                  ~target
                  ~dynamic
                  ~callee:(create_callee inner_resolved_callee)
                  ~arguments
                |> fun { resolution; resolved; errors = new_errors; _ } ->
                resolution, List.append new_errors errors, resolved :: annotations
              in
              let resolution, errors, return_annotations =
                List.fold_left
                  ~f:forward_inner_callable
                  ~init:(callee_resolution, callee_errors, [])
                  (List.map ~f:Type.meta resolved_callees)
              in

              {
                resolution;
                errors;
                resolved = Type.union return_annotations;
                resolved_annotation = None;
                base = None;
              }

          | _ ->
              let target, dynamic = target_and_dynamic resolved_callee in
              forward_callable
                ~resolution:callee_resolution
                ~errors:callee_errors
                ~target
                ~dynamic
                ~callee:(create_callee resolved_callee)
                ~arguments
        in

        


        (*
        let our_model = OurTypeSet.load_summary name in
        List.iteri arguments ~f:(fun i arg ->
          let unpacked_argument = Call.Argument.unpack arg in
          match unpacked_argument with
          | _, Named arg ->
            let callee_arguments = OurTypeSet.OurSummary.get_func_arg_types our_model name in

        );
        (* return condition으로 현재 resolution update 해야함 *)
        *)


        (*
          왜 Temporary Annotation을 지우는거지?   
        *)

        (*
        Log.dump "Resolution >>> \n%a" Resolution.pp resolution;
        
        Log.dump "Update resolution >>> \n%a" Resolution.pp updated_resolution;
        *)

        

        let _ = updated_resolution in
        {
          resolution = updated_resolution;
          errors = updated_errors;
          resolved;
          resolved_annotation = None;
          base = None;
        }
        (*
        {
          resolution = Resolution.clear_temporary_annotations updated_resolution;
          errors = updated_errors;
          resolved;
          resolved_annotation = None;
          base = None;
        }
        *)
    | ComparisonOperator
        { ComparisonOperator.left; right; operator = ComparisonOperator.In as operator }
    | ComparisonOperator
        { ComparisonOperator.left; right; operator = ComparisonOperator.NotIn as operator } ->

        
        let resolve_in_call
            (resolution, errors, joined_annotation)
            { Type.instantiated; class_name; accessed_through_class }
          =
          let resolve_method
              ?(accessed_through_class = false)
              ?(special_method = false)
              class_name
              instantiated
              name
            =
            GlobalResolution.attribute_from_class_name
              ~transitive:true
              ~accessed_through_class
              class_name
              ~resolution:global_resolution
              ~special_method
              ~name
              ~instantiated
            >>| Annotated.Attribute.annotation
            >>| Annotation.annotation
            >>= function
            | Type.Top | Type.Unknown -> None
            | annotation -> Some annotation
          in
          let { Resolved.resolution; resolved; errors; _ } =
            match
              resolve_method
                ~accessed_through_class
                ~special_method:true
                class_name
                instantiated
                "__contains__"
            with
            | Some resolved ->
                let callee =
                  let { Resolved.resolved = resolved_base; _ } =
                    forward_expression ~resolution ~at_resolution right
                  in
                  Callee.Attribute
                    {
                      base = { expression = right; resolved_base };
                      attribute = { name = "__contains__"; resolved };
                      expression =
                        {
                          Node.location;
                          value =
                            Expression.Name
                              (Name.Attribute
                                  { base = right; attribute = "__contains__"; special = true });
                        };
                    }
                in
                
                let x =
                forward_callable
                  ~resolution
                  ~errors
                  ~target:(Some instantiated)
                  ~dynamic:true
                  ~callee
                  ~arguments:[{ Call.Argument.name = None; value = left }]
                in

                (* Log.dump "RESULT : %a" Type.pp x.resolved; *)

                x
            | None -> 
              
              (* let { StatementDefine.Signature.name=define_name; _ } = define_signature in *)
              (
                match
                  resolve_method
                    ~accessed_through_class
                    ~special_method:true
                    class_name
                    instantiated
                    "__iter__"
                with
                | Some iter_callable ->
                    let create_callee resolved =
                      Callee.NonAttribute
                        {
                          expression =
                            {
                              Node.location;
                              value =
                                Expression.Name
                                  (Name.Attribute
                                      { base = right; attribute = "__iter__"; special = true });
                            };
                          resolved;
                        }
                    in

                    (* if String.is_substring (Reference.show define_name) ~substring:"HTMLFormatter._write_col_header"
                      then (
                        Log.dump "Expression %a" Expression.pp expression;
                      ); *)
                    (* Since we can't call forward_expression with the general type (we don't have a
                        good way of saying "synthetic expression with type T", simulate what happens
                        ourselves. *)
                    let forward_method
                        ~method_name
                        ~arguments
                        { Resolved.resolution; resolved = parent; errors; _ }
                      =

                      
                      
                      let x = 
                        Type.split parent
                        |> fst
                        |> Type.primitive_name
                        >>= (fun class_name -> resolve_method class_name parent method_name)
                        >>| fun callable ->
                        forward_callable
                          ~dynamic:true
                          ~resolution
                          ~errors
                          ~target:(Some parent)
                          ~callee:(create_callee callable)
                          ~arguments:
                            (List.map arguments ~f:(fun value -> { Call.Argument.name = None; value }))
                      in

                      

                      (* if String.is_substring (Reference.show define_name) ~substring:"HTMLFormatter._write_col_header"
                        && (String.equal method_name "__next__")
                        then (
                          Log.dump "Expression %a" Expression.pp expression;
                          Log.dump "Parent %a" Type.pp parent;
                          match x with
                          | Some x ->
                            Log.dump "Child %a" Type.pp x.resolved;
                          | None ->
                            Log.dump "Child is None";
                        );
 *)
                        x
                    in

                    forward_callable
                      ~dynamic:true
                      ~resolution
                      ~errors
                      ~target:(Some instantiated)
                      ~callee:(create_callee iter_callable)
                      ~arguments:[]
                    |> forward_method ~method_name:"__next__" ~arguments:[]
                    >>= forward_method ~method_name:"__eq__" ~arguments:[left]
                    |> Option.value
                          ~default:
                            {
                              Resolved.resolution;
                              errors;
                              resolved = Type.Unknown;
                              resolved_annotation = None;
                              base = None;
                            }
                | None -> (
                    let getitem_attribute =
                      {
                        Node.location;
                        value =
                          Expression.Name
                            (Name.Attribute
                                { base = right; attribute = "__getitem__"; special = true });
                      }
                    in
                    let call =
                      let getitem =
                        {
                          Node.location;
                          value =
                            Expression.Call
                              {
                                callee = getitem_attribute;
                                arguments =
                                  [
                                    {
                                      Call.Argument.name = None;
                                      value =
                                        {
                                          Node.location;
                                          value = Expression.Constant (Constant.Integer 0);
                                        };
                                    };
                                  ];
                              };
                        }
                      in
                      {
                        Node.location;
                        value =
                          Expression.Call
                            {
                              callee =
                                {
                                  Node.location;
                                  value =
                                    Name
                                      (Name.Attribute
                                          { base = getitem; attribute = "__eq__"; special = true });
                                };
                              arguments = [{ Call.Argument.name = None; value = left }];
                            };
                      }
                    in
                    let ({ Resolved.resolved; _ } as getitem_resolution) =
                      forward_expression ~resolution ~at_resolution getitem_attribute
                    in
                    let is_valid_getitem = function
                      | Type.Parametric
                          {
                            name = "BoundMethod";
                            parameters =
                              [
                                Single
                                  (Type.Callable
                                    {
                                      implementation =
                                        { parameters = Defined (_ :: index_parameter :: _); _ };
                                      _;
                                    });
                                _;
                              ];
                          }
                      | Type.Callable
                          {
                            implementation = { parameters = Defined (_ :: index_parameter :: _); _ };
                            _;
                          }
                        when GlobalResolution.less_or_equal
                                global_resolution
                                ~left:Type.integer
                                ~right:
                                  (Type.Callable.Parameter.annotation index_parameter
                                  |> Option.value ~default:Type.Bottom) ->
                          true
                      | _ -> false
                    in

                    

                    match resolved with
                    | Type.Union elements when List.for_all ~f:is_valid_getitem elements ->
                        forward_expression ~resolution ~at_resolution call
                    | _ when is_valid_getitem resolved -> forward_expression ~resolution ~at_resolution call
                    | _ ->
                        let errors =
                          let { Resolved.resolved; _ } = forward_expression ~resolution ~at_resolution right in
                          (* Log.dump "Before : %a" Type.pp resolved;
                          let resolved =
                            (match resolved with
                            | Type.Union elements ->
                              let new_elements = List.filter elements ~f:(fun element -> 
                                Log.dump "??? %a" Type.pp element;
                                Type.resolve_class element
                                >>| List.fold ~f:resolve_in_call ~init:(resolution, errors, Type.Bottom)
                                |> Option.is_none
                              )
                              in
                              Type.Union new_elements
                            | _ -> resolved
                            )
                          in
                          Log.dump "After : %a" Type.pp resolved; *)
                          (* let default_kind = 
                            (Error.UnsupportedOperand
                                  (Unary
                                    {
                                      operator_name =
                                        Format.asprintf
                                          "%a"
                                          ComparisonOperator.pp_comparison_operator
                                          operator;
                                      operand = resolved;
                                    }))
                          in *)
                          (* Log.dump "HERE! %a => %a" Expression.pp expression Type.pp resolved; *)
                          let kind =
                            (Error.UnsupportedOperandWithReference
                                  (UnaryWithReference
                                    {
                                      operator_name =
                                        Format.asprintf
                                          "%a"
                                          ComparisonOperator.pp_comparison_operator
                                          operator;
                                      operand = resolved;
                                      reference=right;
                                    }))
                            (* (match Node.value right with
                            | Expression.Name name 
                            | Call { callee={ Node.value=Expression.Name name; _ }; _ } ->
                              (match name_to_reference name with
                              | Some reference -> 
                                (Error.UnsupportedOperandWithReference
                                  (UnaryWithReference
                                    {
                                      operator_name =
                                        Format.asprintf
                                          "%a"
                                          ComparisonOperator.pp_comparison_operator
                                          operator;
                                      operand = resolved;
                                      reference;
                                    }))
                              | _ ->
                                default_kind
                              )
                            | _ -> default_kind
                            ) *)
                          in
                          let x = 
                            emit_error
                              ~errors
                              ~location
                              ~kind
                          in
                          (* List.iter x ~f:(fun e -> Log.dump "OK : %a" Error.pp e); *)
                          x
                        in
                        { getitem_resolution with Resolved.resolved = Type.Unknown; errors }))
          in

          resolution, errors, GlobalResolution.join global_resolution joined_annotation resolved
        in
        let { Resolved.resolution; resolved; errors; _ } = forward_expression ~resolution ~at_resolution right in
        let resolution, errors, resolved =
          (* We should really error here if resolve_class fails *)
          Type.resolve_class resolved
          >>| List.fold ~f:resolve_in_call ~init:(resolution, errors, Type.Bottom)
          |> Option.value ~default:(resolution, errors, Type.Bottom)
        in

        let resolved = if Type.equal resolved Type.Bottom then Type.Unknown else resolved in
        { resolution; errors; resolved; resolved_annotation = None; base = None }
    | ComparisonOperator ({ ComparisonOperator.left; right; _ } as operator) -> (
        let operator = { operator with left } in
        match ComparisonOperator.override ~location operator with
        | Some expression ->
            let resolved = forward_expression ~resolution ~at_resolution expression in
            { resolved with errors = resolved.errors }
        | None ->

          (*Format.printf "\n\n%a binary %a\n\n" Expression.pp left Expression.pp right;*)
            let resolution, errors, resolved = forward_expression ~resolution ~at_resolution left
            |> (fun { Resolved.resolution; errors = left_errors; resolved = left_resolved; _ } ->
                  let { Resolved.resolution; errors = right_errors; Resolved.resolved; _ } =
                    forward_expression ~resolution ~at_resolution right
                  in
                  
                  let resolved =
                    if Type.can_unknown left_resolved 
                    then (
                      Type.bool
                    ) else (
                      Type.Literal (Boolean (GlobalResolution.less_or_equal global_resolution ~left:left_resolved ~right:resolved))
                    )
                  in
                  (* let update_resolution =
                  (match left.value with
                  | Name name ->
                    Resolution.refine_local_with_attributes resolution ~name ~annotation:(Annotation.create_mutable resolved)
                  | _ -> resolution
                  )
                  in
                  let final_resolution = Resolution.meet_refinements resolution update_resolution in
                  let _ = final_resolution in *)
                  resolution, List.append left_errors right_errors, resolved)
            in  
            {
              resolution;
              errors;
              resolved = resolved;
              resolved_annotation = None;
              base = None;
            })
    | Constant (Constant.Complex _) ->
        {
          resolution;
          errors = [];
          resolved = Type.complex;
          resolved_annotation = None;
          base = None;
        }
    | Dictionary { Dictionary.entries; keywords } (* e.g. { "a" : 1 } *) ->
        let key, value, fields, resolution, errors =
          let forward_entry (key, value, fields, resolution, errors) entry =
            let new_key, new_value, resolution, errors = forward_entry ~resolution ~errors ~entry in

            let new_field = Type.OurTypedDictionary.create_field ~annotation:new_value (Expression.show entry.key) in

            ( GlobalResolution.join global_resolution key new_key,
              GlobalResolution.join global_resolution value new_value,
              new_field::fields,
              resolution,
              errors )
          in
          List.fold entries ~f:forward_entry ~init:(Type.Unknown, Type.Unknown, [], resolution, [])
        in
        let key =
          if List.is_empty keywords && Type.is_unbound key then
            Type.variable "_KT" |> Type.Variable.mark_all_free_variables_as_escaped
          else if List.is_empty keywords && Type.is_unknown key then
            Type.Bottom
          else
            key
        in
        let value =
          if List.is_empty keywords && Type.is_unbound value then
            Type.variable "_VT" |> Type.Variable.mark_all_free_variables_as_escaped
          else if List.is_empty keywords && Type.is_unknown value then
            Type.Unknown
          else
            value
        in
        let resolved_key_and_value, resolved_fields, resolution, errors =
          let forward_keyword (resolved, fields, resolution, errors) keyword =
            match resolved with
            | None -> resolved, fields, resolution, errors
            | Some (key, value) -> (
                
                let { Resolved.resolution; resolved = source; errors = new_errors; _ } =
                  forward_expression ~resolution ~at_resolution keyword
                in

                let errors = List.append new_errors errors in
                let rec dict_extract_type source =
                  let source = Type.filter_unknown source in
                  (match source with
                  | Type.Top
                  | Bottom
                  | Any ->
                      (None, fields, resolution, errors)
                  | OurTypedDictionary  { general; typed_dict; } ->
                    let result_of_general = dict_extract_type general in
                    (match result_of_general with
                    | Some (key, value), general_fields, resolution, errors ->
                      let new_field = Type.OurTypedDictionary.join ~join:Type.union_join typed_dict general_fields in
                      Some (key, value), new_field, resolution, errors
                    | _ ->
                      result_of_general
                    )
                  | _ -> (
                      match
                        GlobalResolution.extract_type_parameters
                          global_resolution
                          ~source
                          ~target:"typing.Mapping"
                      with
                      | Some [new_key; new_value] ->
                          ( Some
                              ( GlobalResolution.join global_resolution key new_key,
                                GlobalResolution.join global_resolution value new_value ),
                            fields,
                            resolution,
                            errors )
                      | _ ->
                          let errors =
                            emit_error
                              ~errors
                              ~location
                              ~kind:
                                (Error.InvalidArgument
                                  (Error.Keyword
                                      {
                                        expression = Some keyword;
                                        annotation = source;
                                        require_string_keys = false;
                                      })
                                )
                          in
                          None, fields, resolution, errors)
                  )
                in 
                dict_extract_type source
              )
                
          in
          List.fold keywords ~f:forward_keyword ~init:(Some (key, value), fields, resolution, errors)
        in
        let typed_dict = Type.OurTypedDictionary.anonymous resolved_fields in

        

        let _ = typed_dict in

        let resolved =
          if List.length typed_dict = 0 || !Type.restrict_dict then
            resolved_key_and_value
            >>| (fun (key, value) -> Type.dictionary ~key ~value)
            |> Option.value ~default:Type.Unknown
          else
            resolved_key_and_value
            >>| (fun (key, value) -> Type.our_typed_dictionary ~key ~value ~typed_dict)
            |> Option.value ~default:Type.Unknown
        in

        { resolution; errors; resolved; resolved_annotation = None; base = None }
    | DictionaryComprehension { Comprehension.element; generators } ->
        let key, value, _, errors =
          List.fold
            generators
            ~f:(fun (resolution, errors) generator ->
              forward_generator ~resolution ~errors ~generator)
            ~init:(resolution, [])
          |> fun (resolution, errors) -> forward_entry ~resolution ~errors ~entry:element
        in
        (* Discard generator-local variables. *)
        {
          resolution;
          errors;
          resolved = Type.dictionary ~key ~value;
          resolved_annotation = None;
          base = None;
        }
    | Constant Constant.Ellipsis ->
        { resolution; errors = []; resolved = Type.Unknown; resolved_annotation = None; base = None }
    | Constant Constant.False ->
        {
          resolution;
          errors = [];
          resolved = Type.Literal (Type.Boolean false);
          resolved_annotation = None;
          base = None;
        }
    | Constant (Constant.Float _) ->
        { resolution; errors = []; resolved = Type.float; resolved_annotation = None; base = None }
    | Constant (Constant.Integer literal) ->
        {
          resolution;
          errors = [];
          resolved = Type.literal_integer literal;
          resolved_annotation = None;
          base = None;
        }
    | Constant (Constant.BigInteger _) ->
        {
          resolution;
          errors = [];
          resolved = Type.integer;
          resolved_annotation = None;
          base = None;
        }
    | Constant (Constant.String { StringLiteral.kind = StringLiteral.Bytes; value }) ->
        {
          resolution;
          errors = [];
          resolved = Type.literal_bytes value;
          resolved_annotation = None;
          base = None;
        }
    | Constant (Constant.String { StringLiteral.kind = StringLiteral.String; value }) ->
        {
          resolution;
          errors = [];
          resolved = Type.literal_string value;
          resolved_annotation = None;
          base = None;
        }
    | Constant Constant.True ->
        {
          resolution;
          errors = [];
          resolved = Type.Literal (Type.Boolean true);
          resolved_annotation = None;
          base = None;
        }
    | FormatString substrings ->
        let forward_substring ((resolution, errors) as sofar) = function
          | Substring.Literal _ -> sofar
          | Substring.Format expression ->
              forward_expression ~resolution ~at_resolution expression
              |> fun { resolution; errors = new_errors; _ } ->
              resolution, List.append new_errors errors
        in
        let resolution, errors = List.fold substrings ~f:forward_substring ~init:(resolution, []) in
        { resolution; errors; resolved = Type.string; resolved_annotation = None; base = None }
    | Generator { Comprehension.element; generators } ->
        let { Resolved.resolution; resolved; errors; _ } =
          forward_comprehension ~resolution ~errors:[] ~element ~generators
        in
        let has_async_generator = List.exists ~f:(fun generator -> generator.async) generators in
        let generator =
          match has_async_generator with
          | true -> Type.async_generator ~yield_type:resolved ()
          | false -> Type.generator_expression resolved
        in
        { resolution; errors; resolved = generator; resolved_annotation = None; base = None }
    | Lambda { Lambda.body; parameters } ->
        let resolution_with_parameters =
          let add_parameter resolution { Node.value = { Parameter.name; _ }; _ } =
            let name = String.chop_prefix name ~prefix:"*" |> Option.value ~default:name in
            Resolution.new_local
              resolution
              ~reference:(Reference.create name)
              ~annotation:(Annotation.create_mutable Type.Unknown)
          in
          List.fold ~f:add_parameter ~init:resolution parameters
        in
        let { Resolved.resolved; errors; _ } =
          forward_expression ~resolution:resolution_with_parameters ~at_resolution body
        in
        (* Judgement call, many more people want to pass in `lambda: 0` to `defaultdict` than want
            to write a function that take in callables with literal return types. If you really want
            that behavior you can always write a real inner function with a literal return type *)
        let resolved = Type.weaken_literals resolved in
        let create_parameter { Node.value = { Parameter.name; value; _ }; _ } =
          { Type.Callable.Parameter.name; annotation = Type.Unknown; default = Option.is_some value }
        in
        let parameters =
          List.map parameters ~f:create_parameter
          |> Type.Callable.Parameter.create
          |> fun parameters -> Type.Callable.Defined parameters
        in
        {
          resolution;
          errors;
          resolved = Type.Callable.create ~parameters ~annotation:resolved ();
          resolved_annotation = None;
          base = None;
        }
    | List elements ->
        let { Resolved.resolution; resolved; errors; _ } =
          forward_elements ~resolution ~errors:[] ~elements
        in

        (* Log.dump "%a => %a ... %a" Expression.pp expression Type.pp resolved Type.pp (Type.list resolved); *)

        {
          resolution;
          errors;
          resolved = Type.list resolved;
          resolved_annotation = None;
          base = None;
        }
    | ListComprehension { Comprehension.element; generators } ->
        let { Resolved.resolution; resolved; errors; _ } =
          forward_comprehension ~resolution ~errors:[] ~element ~generators
        in
        {
          resolution;
          errors;
          resolved = Type.list resolved;
          resolved_annotation = None;
          base = None;
        }
    | Name (Name.Identifier identifier) ->
        forward_reference ~resolution ~errors:[] (Reference.create identifier)
    | Name (Name.Attribute _ as name) 
      when OurDomain.is_recheck_mode (OurDomain.load_mode ()) && (
        match name_to_reference name with
        | Some reference ->
          let reference = Reference.delocalize_only_name reference in
          Reference.Map.existsi !OurDomain.skip_reference_map ~f:(fun ~key ~data ->
            let find_reference = (Reference.equal key reference) || (String.is_substring (Reference.show reference) ~substring:(Reference.show key)) in
            if find_reference then (
              Type.can_union ~f:(fun t -> Type.equal t Type.Unknown || Type.equal t Type.Any || Type.equal t Type.Top || Type.equal t Type.Bottom) data
            ) else false
          )
        | _ -> false
      ) -> 
        let resolved = Type.Any in
        { resolution; errors = []; resolved; resolved_annotation = None; base = None }
    | Name (Name.Attribute { base; attribute; special } as name) -> (
        (*
          * Attribute accesses are recursively resolved by stripping mames off
          * of the end and then trying
          * to resolve the prefix. For example, `foo().bar` will be stripped to
          * `foo()` first, then once that type is resolved we'll look up the
          * `bar` attribute.
          *
          * But to handle lazy module tracking, which requires us to only
          * support limited cases of implicit namespace modules, we also want
          * to check whether the reference can be directly resolved to a type
          * (for example `pandas.core.DataFrame`) and short-circuit the
          * recursion in that case.
          *
          * Our method for doing this is to decide whether a name can be
          * directly looked up, short ciruiting the recursion, by using
          * - `name_to_reference`, which produces a reference when a `Name`
          *    corresponds to a plain reference (for example `foo().bar` does
          *    not but `pandas.core.DataFrame` does, and
          * - `resolve_exports`, which does a principled syntax-based lookup
          *    to see if a name makes sense as a module top-level name
          *
          * TODO(T125828725) Use the resolved name coming from
          * resolve_exports, rather than throwing away that name and falling
          * back to legacy_resolve_exports.  This requires either using better
          * qualification architecture or refactors of existing python code
          * that relies on the legacy behaviror in the presence of ambiguous
          * fully-qualified names.
          *)
        (* let { StatementDefine.Signature.name=define_name; _ } = define_signature in
        if String.is_substring (Reference.show define_name) ~substring:"Order._eval_subs"
          && (String.is_substring (Expression.show expression) ~substring:"solveset.solveset") then (
        let x = 
          Ast.Expression.name_to_reference name
          >>= GlobalResolution.resolve_exports global_resolution
        in

        (match x with
        | Some x -> Log.dump "Some!";
          (match x with 
          | ModuleAttribute { from; name; remaining; _ } ->
            let _ = remaining in
            List.iter remaining ~f:(fun a -> Log.dump "HMM %s" a);
            Log.dump "%a %s" Reference.pp from name;
          | _ -> Log.dump "NOPE";
          )
        | _ -> Log.dump "NO...";
        );
        ); *)

        match
          Ast.Expression.name_to_reference name
          >>= GlobalResolution.resolve_exports global_resolution
          >>= UnannotatedGlobalEnvironment.ResolvedReference.as_module_toplevel_reference
          >>= fun _ ->
          Ast.Expression.name_to_reference name
          >>| fun reference -> GlobalResolution.legacy_resolve_exports global_resolution ~reference
        with
        | Some name_reference ->

          let resolved = forward_reference ~resolution ~errors:[] name_reference in
          let resolved =
          (match resolved.resolved with
          | Type.Any ->
            let final_model = !OurDomain.our_model in
            let prefix = Reference.prefix name_reference in
            (match prefix with
              | Some prefix ->
                let typ = OurDomain.OurSummary.get_module_var_type final_model prefix attribute in
                (* Log.dump "HMM %a => %a" Reference.pp prefix Type.pp typ; *)
              { resolved with resolved=typ }
              | _ -> resolved
            )
            
          | _ -> resolved
          )
          in

          let resolved =
          (match name_to_reference name with
          | Some reference when OurDomain.is_recheck_mode (OurDomain.load_mode ()) ->
            let reference = Reference.delocalize_only_name reference in
            let find_type =
              Reference.Map.fold !OurDomain.skip_reference_map ~init:None ~f:(fun ~key ~data acc ->
                if Option.is_some acc then acc
                else (
                let find_reference = (Reference.equal key reference) || (String.is_substring (Reference.show reference) ~substring:(Reference.show key)) in
                if find_reference then (
                  Some data
                ) else acc
                )
              )
            in
            (match find_type with
            | Some t ->
              let less_or_equal = GlobalResolution.less_or_equal global_resolution in
              let del_type = Type.del_type ~less_or_equal resolved.resolved t in
              { resolved with resolved=del_type; }
            | _ -> resolved
            )
            
          | _ -> resolved)
          in

          resolved
        | None ->
          (* let tt =
          Ast.Expression.name_to_reference base
          >>= GlobalResolution.resolve_exports global_resolution
          in
            (match tt with
            | Some m -> 
              Log.dump "%a ==> %a" Expression.pp base Module.pp m;
            | _ -> ()
            ); *)

            let ({ Resolved.errors; resolved = resolved_base; _ } as base_resolved) =
              forward_expression ~resolution ~at_resolution base
            in

            
            
            let errors, resolved_base =
              if Type.Variable.contains_escaped_free_variable resolved_base then
                let errors =
                  emit_error
                    ~errors
                    ~location
                    ~kind:
                      (Error.IncompleteType
                          {
                            target = base;
                            annotation = resolved_base;
                            attempted_action = Error.AttributeAccess attribute;
                          })
                in
                errors, Type.Variable.convert_all_escaped_free_variables_to_bottom resolved_base
              else
                errors, resolved_base
            in
            let x =
            resolve_attribute_access
              ~base_resolved:{ base_resolved with errors; resolved = resolved_base }
              ~base
              ~special
              ~attribute
              ~has_default:false
            in

            let resolved =
              (match name_to_reference name with
              | Some reference when OurDomain.is_recheck_mode (OurDomain.load_mode ()) ->
                let reference = Reference.delocalize_only_name reference in
                let find_type =
                  Reference.Map.fold !OurDomain.skip_reference_map ~init:None ~f:(fun ~key ~data acc ->
                    if Option.is_some acc then acc
                    else (
                    let find_reference = (Reference.equal key reference) || (String.is_substring (Reference.show reference) ~substring:(Reference.show key)) in
                    if find_reference then (
                      Some data
                    ) else acc
                    )
                  )
                in
                (match find_type with
                | Some t ->
                  let less_or_equal = GlobalResolution.less_or_equal global_resolution in
                  let del_type = Type.del_type ~less_or_equal x.resolved t in
                  { x with resolved=del_type; }
                | _ -> x
                )
                
              | _ -> x)
            in

            (* let x =
              match x.resolved with
              | Unknown ->
                if (String.is_suffix (Expression.show expression) ~suffix:"temp_stdout.write") then (
                  let t = (Type.Callable { 
                    kind = Named (Reference.create "temp_stdout.write"); 
                    implementation = { parameters = Defined [
                        Type.Callable.RecordParameter.PositionalOnly { index = 0; annotation = Type.bytes; default = false};
                        Type.Callable.RecordParameter.Keywords (Type.Any);
                      ]; annotation = Unknown 
                    }; 
                    overloads = [] }) in
                  { x with resolved = t }
                ) else (
                  x
                )
              | _ -> x
            in
            Log.dump "%a => %a" Expression.pp expression Type.pp x.resolved; *)

            (* Log.dump "%a => %a" Expression.pp expression Type.pp x.resolved; *)

            resolved
            )
    | Constant Constant.NoneLiteral ->
        {
          resolution;
          errors = [];
          resolved = Type.NoneType;
          resolved_annotation = None;
          base = None;
        }
    | Set elements ->
        let { Resolved.resolution; resolved; errors; _ } =
          forward_elements ~resolution ~errors:[] ~elements
        in
        {
          resolution;
          errors;
          resolved = Type.set resolved;
          resolved_annotation = None;
          base = None;
        }
    | SetComprehension { Comprehension.element; generators } ->
        let { Resolved.resolution; resolved; errors; _ } =
          forward_comprehension ~resolution ~errors:[] ~element ~generators
        in
        {
          resolution;
          errors;
          resolved = Type.set resolved;
          resolved_annotation = None;
          base = None;
        }
    | Starred starred ->
        let resolved =
          match starred with
          | Starred.Once expression
          | Starred.Twice expression ->
              forward_expression ~resolution ~at_resolution expression
        in
        { resolved with resolved = Type.Unknown; resolved_annotation = None; base = None }
    | Ternary { Ternary.target; test; alternative } ->
        let test_errors =
          let { Resolved.errors; _ } = forward_expression ~resolution ~at_resolution test in
          errors
        in
        let target_resolved, target_errors =
          let post_resolution = refine_resolution_for_assert ~resolution ~at_resolution test in

          (match post_resolution with
          | Value _ -> 
            let resolution = resolution_or_default post_resolution ~default:resolution in
            let { Resolved.resolved; errors; _ } = forward_expression ~resolution ~at_resolution target in
            resolved, errors
          | _ -> Type.Bottom, []
          )
          
        in
        let alternative_resolved, alternative_errors =
          let post_resolution =
            refine_resolution_for_assert ~resolution ~at_resolution (normalize (negate test))
          in

          (match post_resolution with
          | Value _ -> 
            let resolution = resolution_or_default post_resolution ~default:resolution in
            let { Resolved.resolved; errors; _ } = forward_expression ~resolution ~at_resolution alternative in
            resolved, errors
          | _ -> Type.Bottom, []
          )
          
        in
        let resolved =
          (* Joining Literals as their union is currently too expensive, so we do it only for
              ternary expressions. *)
          match target_resolved, alternative_resolved with
          | Type.Bottom, t | t, Type.Bottom -> t
          | Type.Literal (Type.String Type.AnyLiteral), Type.Literal (Type.String _)
          | Type.Literal (Type.String _), Type.Literal (Type.String Type.AnyLiteral) ->
              Type.Literal (Type.String Type.AnyLiteral)
          | Type.Literal (Type.Boolean _), Type.Literal (Type.Boolean _)
          | Type.Literal (Type.Integer _), Type.Literal (Type.Integer _)
          | Type.Literal (Type.String _), Type.Literal (Type.String _)
          | Type.Literal (Type.EnumerationMember _), Type.Literal (Type.EnumerationMember _) ->
              Type.union [target_resolved; alternative_resolved]
          | _ -> GlobalResolution.join global_resolution target_resolved alternative_resolved
        in
        let errors = List.concat [test_errors; target_errors; alternative_errors] in
        (* The resolution is local to the ternary expression and should not be propagated out. *)
        { resolution; errors; resolved; resolved_annotation = None; base = None }
    | Tuple elements ->
        let resolution, errors, resolved_elements =
          let forward_element (resolution, errors, resolved) expression =
            let resolution, new_errors, resolved_element =
              match expression with
              | { Node.value = Expression.Starred (Starred.Once expression); _ } ->
                  let { Resolved.resolution; resolved = resolved_element; errors = new_errors; _ } =
                    forward_expression ~resolution ~at_resolution expression
                  in
                  let new_errors, ordered_type =
                    match resolved_element with
                    | Type.Tuple ordered_type -> new_errors, ordered_type
                    | Type.Any ->
                        new_errors, Type.OrderedTypes.create_unbounded_concatenation Type.Unknown
                    | _ -> (
                        match
                          GlobalResolution.type_of_iteration_value
                            ~global_resolution
                            resolved_element
                        with
                        | Some element_type ->
                            ( new_errors,
                              Type.OrderedTypes.create_unbounded_concatenation element_type )
                        | None ->
                            ( emit_error
                                ~errors:new_errors
                                ~location
                                ~kind:
                                  (Error.TupleConcatenationError
                                      (UnpackingNonIterable { annotation = resolved_element })),
                              Type.OrderedTypes.create_unbounded_concatenation Type.Unknown ))
                  in
                  resolution, new_errors, ordered_type
              | _ ->
                  let { Resolved.resolution; resolved = resolved_element; errors = new_errors; _ } =
                    forward_expression ~resolution ~at_resolution expression
                  in
                  resolution, new_errors, Type.OrderedTypes.Concrete [resolved_element]
            in
            resolution, List.append new_errors errors, resolved_element :: resolved
          in
          List.fold elements ~f:forward_element ~init:(resolution, [], [])
        in
        let resolved, errors =
          let resolved_elements = List.rev resolved_elements in
          let narrow = 
            (fun t -> 
              Type.narrow_union 
              ~join:(GlobalResolution.join global_resolution) 
              ~less_or_equal:(GlobalResolution.less_or_equal global_resolution)
              (Type.Union t)
              |> (function
              | Type.Union t_list -> t_list
              | t -> [t]
              )
            )
          in
          let _ = narrow in
          let concatenated_elements =
            let concatenate sofar next =
              sofar >>= fun left -> Type.OrderedTypes.concatenate ~left ~right:next
            in
            List.fold resolved_elements ~f:concatenate ~init:(Some (Type.OrderedTypes.Concrete []))
          in
          match concatenated_elements with
          | Some (Type.OrderedTypes.Concrete []) -> Type.Tuple (Type.OrderedTypes.Concrete [Type.Unknown]), errors
          | Some concatenated_elements -> Type.Tuple concatenated_elements, errors
          | None ->
              let variadic_expressions =
                match List.zip elements resolved_elements with
                | Ok pairs ->
                    List.filter_map pairs ~f:(function
                        | expression, Type.OrderedTypes.Concatenation _ -> Some expression
                        | _ -> None)
                | Unequal_lengths -> elements
              in
              ( Type.Tuple (Type.OrderedTypes.create_unbounded_concatenation Type.Unknown),
                emit_error
                  ~errors
                  ~location
                  ~kind:(Error.TupleConcatenationError (MultipleVariadics { variadic_expressions }))
              )
        in
        { resolution; errors; resolved; resolved_annotation = None; base = None }
    | UnaryOperator ({ UnaryOperator.operand; _ } as operator) -> (
        match UnaryOperator.override operator with
        | Some expression -> forward_expression ~resolution ~at_resolution expression
        | None ->
            let resolved = forward_expression ~resolution ~at_resolution operand in

            if Type.is_falsy resolved.resolved then
              { resolved with resolved = Literal (Boolean true); resolved_annotation = None; base = None }
            else if Type.is_truthy resolved.resolved then
              { resolved with resolved = Literal (Boolean false); resolved_annotation = None; base = None}
            else
              { resolved with resolved = Type.bool; resolved_annotation = None; base = None }
            )
    
            
            (* { resolved with resolved = Type.bool; resolved_annotation = None; base = None }) *)
    | WalrusOperator { value; target } ->
        let resolution, errors =
          let post_resolution, errors =
            forward_assignment ~resolution ~at_resolution ~location ~target ~value ~annotation:None
          in
          resolution_or_default post_resolution ~default:resolution, errors
        in
        let resolved = forward_expression ~resolution ~at_resolution value in
        { resolved with errors = List.append errors resolved.errors }
    | Expression.Yield yielded ->
        let { Resolved.resolution; resolved = yield_type; errors; _ } =
          match yielded with
          | Some expression ->
              let { Resolved.resolution; resolved; errors; _ } =
                forward_expression ~resolution ~at_resolution expression
              in
              { resolution; errors; resolved; resolved_annotation = None; base = None }
          | None ->
              {
                resolution;
                errors = [];
                resolved = Type.none;
                resolved_annotation = None;
                base = None;
              }
        in
        let actual =
          if define_signature.async then
            Type.async_generator ~yield_type ()
          else
            Type.generator ~yield_type ()
        in
        let errors =
          validate_return ~location None ~resolution ~at_resolution ~errors ~actual ~is_implicit:false
        in
        let send_type, _ =
          return_annotation ~global_resolution
          |> GlobalResolution.type_of_generator_send_and_return ~global_resolution
        in
        (* Log.dump "Yield >>> %a" Type.pp send_type; *)
        { resolution; errors; resolved = send_type; resolved_annotation = None; base = None }
    | Expression.YieldFrom yielded_from ->
        let { Resolved.resolution; resolved; errors; _ } =
          forward_expression ~resolution ~at_resolution yielded_from
        in
        let yield_type =
          resolved
          |> GlobalResolution.type_of_iteration_value ~global_resolution
          |> Option.value ~default:Type.Unknown
        in
        let send_type, subgenerator_return_type =
          GlobalResolution.type_of_generator_send_and_return ~global_resolution resolved
        in

        let actual =
          if define_signature.async then
            Type.async_generator ~yield_type ~send_type ()
          else
            Type.generator ~yield_type ~send_type ()
        in
        let errors =
          validate_return ~location None ~resolution ~at_resolution ~errors ~actual ~is_implicit:false
        in
        {
          resolution;
          errors;
          resolved = subgenerator_return_type;
          resolved_annotation = None;
          base = None;
        }

    )
    in

    (* if String.is_substring (Reference.show define_name) ~substring:"airflow.www.app.create_app"
      then (
        Log.dump "END : %a" Expression.pp expression;
    ); *)

    xxx

  and refine_resolution_for_assert ~resolution ~at_resolution test =
    let global_resolution = Resolution.global_resolution resolution in
    let annotation_less_or_equal ~left ~right =
      Type.is_unknown (Annotation.annotation right) ||
      Annotation.less_or_equal
        ~type_less_or_equal:(GlobalResolution.less_or_equal global_resolution) ~left ~right
    in
    let parse_refinement_annotation annotation =
      let parse_meta annotation =
        match parse_and_check_annotation ~resolution annotation |> snd with
        | Type.Top -> (
            

            (* Try to resolve meta-types given as expressions. *)
            match resolve_expression_type ~resolution ~at_resolution annotation with
            | annotation when Type.is_meta annotation -> Type.single_parameter annotation
            | Type.Tuple (Concrete elements) when List.for_all ~f:Type.is_meta elements ->
                List.map ~f:Type.single_parameter elements |> Type.union
            | Type.Tuple (Concatenation concatenation) ->
                Type.OrderedTypes.Concatenation.extract_sole_unbounded_annotation concatenation
                >>= (fun element ->
                      if Type.is_meta element then
                        Some (Type.single_parameter element)
                      else
                        None)
                |> Option.value ~default:Type.Top
            | _ -> Type.Top)
        | annotation -> annotation
      in
      let x =
        match annotation with
        | { Node.value = Expression.Tuple elements; _ } ->
            List.map ~f:parse_meta elements |> fun elements -> Type.Union elements
        | _ -> parse_meta annotation
      in
      
      (* Log.dump "Parse Refinement %a" Type.pp x;
      *)
      x
    in
    let partition annotation ~boundary =
      let consistent_with_boundary, not_consistent_with_boundary =
        let unfolded_annotation =
          match annotation with
          | Type.RecursiveType recursive_type ->
              Type.RecursiveType.unfold_recursive_type recursive_type
          | _ -> annotation
        in
        let extract_union_members = function
          | Type.Union parameters -> parameters
          | annotation -> [annotation]
        in
        extract_union_members unfolded_annotation
        |> List.partition_tf ~f:(fun left ->
                Resolution.is_consistent_with resolution left boundary ~expression:None)
      in
      let not_consistent_with_boundary =
        if List.is_empty not_consistent_with_boundary then
          None
        else
          Some (Type.union not_consistent_with_boundary)
      in
      let consistent_with_boundary = Type.union consistent_with_boundary in
      { consistent_with_boundary; not_consistent_with_boundary }
    in
    let is_temporary_refinement (name: Name.t) =
      let refinable_annotation name =
        (match name_to_reference name with
        | Some reference ->
          if Resolution.has_temporary_annotation ~reference resolution
          then true
          else if Resolution.has_nontemporary_annotation ~reference resolution
          then false
          else (
            match name with
            | Name.Attribute { base = { Node.value = Name base; _ }; _ } when is_simple_name base ->
              let reference = name_to_reference_exn name in
              if Resolution.has_temporary_annotation ~reference resolution
              then true
              else if Resolution.has_nontemporary_annotation ~reference resolution
              then false
              else true
            | _ -> true
          )
        | _ -> true
        )
       (*  match
          Resolution.get_local_with_attributes ~global_fallback:false ~name resolution, name
        with
        | Some local_annotation, _ -> Some local_annotation
        | _, Name.Attribute { base = { Node.value = Name base; _ }; attribute; _ } -> (
            let attribute =
              refinable_annotation base
              >>| Annotation.annotation
              >>= fun parent ->
              Type.split parent
              |> fst
              |> Type.primitive_name
              >>= GlobalResolution.attribute_from_class_name
                    ~resolution:global_resolution
                    ~name:attribute
                    ~instantiated:parent
                    ~transitive:true
            in
            match
              ( attribute >>| AnnotatedAttribute.visibility,
                attribute >>| AnnotatedAttribute.defined,
                attribute >>| AnnotatedAttribute.annotation )
            with
            | Some (ReadOnly (Refinable _)), Some true, Some annotation -> Some annotation
            | _ -> None)
        | _ -> None *)
      in
      (* Option.is_none (refinable_annotation name) *)
      refinable_annotation name
    in
    let rec existing_annotation name =
      match Resolution.get_local_with_attributes ~global_fallback:false ~name resolution, name with
      | Some annotation, _ -> Some annotation
      | _, Name.Attribute { base = { Node.value = Name base; _ }; attribute; _ } -> 
        let base_annotation = existing_annotation base in
        (match base_annotation with
        | Some annotation ->
          let base_type = Annotation.annotation annotation in
          let final_model = !OurDomain.our_model in
          let less_or_equal = GlobalResolution.less_or_equal global_resolution in
          let type_join = GlobalResolution.join global_resolution in

          OurTypeSet.OurSummaryResolution.get_type_of_class_attribute ~type_join ~less_or_equal final_model (Type.class_name base_type) attribute
          >>| Annotation.create_mutable
          
        | _ -> None
        )
        (* (
          let attribute =
            existing_annotation base
            >>| Annotation.annotation
            >>= fun parent ->
            Type.split parent
            |> fst
            |> Type.primitive_name
            >>= GlobalResolution.attribute_from_class_name
                  ~resolution:global_resolution
                  ~name:attribute
                  ~instantiated:parent
                  ~transitive:true
          in
          match attribute with
          | Some attribute when AnnotatedAttribute.defined attribute ->
              Some (AnnotatedAttribute.annotation attribute)
          | _ -> None) *)
      | _ -> None
    in
    let refine_local ~name annotation =
      Resolution.refine_local_with_attributes
        ~temporary:(is_temporary_refinement name)
        resolution
        ~name
        ~annotation
    in

    (* let add_expression_to_local ~expression ~annotation resolution  =
      Resolution.new_local ~temporary:true ~reference:(Reference.create (Expression.show expression)) ~annotation resolution
    in *)
    

    match Node.value test with
    (* Explicit asserting falsy values. *)
    | t when check_empty_constant t -> Unreachable
    (* | Expression.Constant Constant.(False | NoneLiteral)
    | Expression.Constant (Constant.Integer 0)
    | Expression.Constant (Constant.Float 0.0)
    | Expression.Constant (Constant.Complex 0.0)
    | Expression.Constant (Constant.String { StringLiteral.value = ""; _ })
    | Expression.List []
    | Expression.Tuple []
    | Expression.Dictionary { Dictionary.entries = []; keywords = [] } ->
        Unreachable *)
    (* Type is the same as `annotation_expression` *)
    | ComparisonOperator
        {
          left =
            {
              Node.value =
                Call
                  {
                    callee = { Node.value = Name (Name.Identifier "type"); _ };
                    arguments =
                      [{ Call.Argument.name = None; value = { Node.value = Name name; _ } }];
                  };
              _;
            };
          operator = ComparisonOperator.Is;
          right = annotation_expression;
        }
    | ComparisonOperator
        {
          left =
            {
              Node.value =
                Call
                  {
                    callee = { Node.value = Name (Name.Identifier "type"); _ };
                    arguments =
                      [{ Call.Argument.name = None; value = { Node.value = Name name; _ } }];
                  };
              _;
            };
          operator = ComparisonOperator.Equals;
          right = annotation_expression;
        }
    | Call
        {
          callee = { Node.value = Name (Name.Identifier "isinstance"); _ };
          arguments =
            [
              { Call.Argument.name = None; value = { Node.value = Name name; _ } };
              { Call.Argument.name = None; value = annotation_expression };
            ];
        }
      when is_simple_name name ->
        


        let type_ = parse_refinement_annotation annotation_expression in
        
        (* Log.dump "Exp : %a ==> %a" Expression.pp annotation_expression Type.pp type_; *)
        let resolution =
          let refinement_unnecessary existing_annotation =
            annotation_less_or_equal
              ~left:existing_annotation
              ~right:(Annotation.create_mutable type_)
            && (not (Type.equal (Annotation.annotation existing_annotation) Type.Bottom))
            && not (Type.equal (Annotation.annotation existing_annotation) Type.Any)
            && not (Type.equal (Annotation.annotation existing_annotation) Type.Unknown)
          in
          match existing_annotation name with
          (* Allow Anys [especially from placeholder stubs] to clobber *)
          | Some _ when Type.is_any type_ ->
              Value (Annotation.create_mutable type_ |> refine_local ~name)
          | Some existing_annotation when refinement_unnecessary existing_annotation ->
              (* let existing_annotation =
                if Type.is_unknown type_ then (
                  if String.is_substring ~substring:"ConditionSet" (Expression.show annotation_expression) then (
                    let t = Type.primitive (Expression.show annotation_expression) in
                    let existing = Annotation.annotation existing_annotation |> Type.filter_unknown in
                    Annotation.create_mutable (GlobalResolution.join global_resolution existing t)
                  ) else (
                    existing_annotation
                  )
                )
                else
                  existing_annotation
              in *)
              (* Log.dump "OK %a" Annotation.pp existing_annotation; *)
              Value (refine_local ~name existing_annotation)
          (* Clarify Anys if possible *)
          | Some existing_annotation
            when Type.equal (Annotation.annotation existing_annotation) Type.Any ->
              Value (Annotation.create_mutable type_ |> refine_local ~name)
          | Some existing_annotation
            when Type.can_unknown (Annotation.annotation existing_annotation) ->
              (* let type_ = GlobalResolution.join global_resolution type_ (Annotation.annotation existing_annotation) in *)
              let existing_type = Annotation.annotation existing_annotation in
              let { consistent_with_boundary; _ } = partition existing_type ~boundary:type_ in
              if (not (Type.is_unknown consistent_with_boundary)) && not (Type.is_unbound consistent_with_boundary) then (
                Value (Annotation.create_mutable consistent_with_boundary |> refine_local ~name)
              )
              else (
                Value (Annotation.create_mutable type_ |> refine_local ~name)
              )
              
          | None -> Value resolution
          
          | Some existing_annotation ->
              (* Log.dump "???"; *)
              let existing_type = Annotation.annotation existing_annotation in
              let { consistent_with_boundary; _ } = partition existing_type ~boundary:type_ in
              if not (Type.is_unbound consistent_with_boundary) then (

                Value (Annotation.create_mutable consistent_with_boundary |> refine_local ~name)
              )
              else if GlobalResolution.types_are_orderable global_resolution existing_type type_
              then (

                Value (Annotation.create_mutable type_ |> refine_local ~name)
              )
              else
                Unreachable
        in
        resolution
      | Call
        {
          callee = { Node.value = Name (Name.Identifier "isinstance"); _ };
          arguments =
          [
            { Call.Argument.name = None; value = { Node.value = 
                Call { 
                  callee = {
                    Node.value = Name Attribute { base = { Node.value = Name name; _ }; attribute="__getitem__"; _ }; _
                  };
                  arguments = [{ Call.Argument.name = None; value = { Node.value = Constant _; _ } as value;}];
                }; _ 
              } 
            };
            { Call.Argument.name = None; value = annotation_expression };
          ];
          _
        } when is_simple_name name
        ->
        let _ = annotation_expression in
        (match existing_annotation name with
        | Some annotation when not !Type.restrict_dict ->
          let existing_type = Annotation.annotation annotation in
          let new_dict = Type.OurTypedDictionary.refine_dict_field existing_type (Expression.show value) (Type.dictionary ~key:Type.Any ~value:Type.Any) in

          let resolution = Resolution.refine_local_with_attributes resolution ~name ~annotation:(Annotation.create_mutable new_dict) in
          Value resolution
        | _ -> Value resolution
        )
        (* let _ = arguments in  *)
        (* let _ = arguments in *)
      | Call
      {
        callee = { Node.value = Name (Name.Identifier ident | Name.Attribute { attribute=ident; _ }); _ };
        arguments =
          [
            { Call.Argument.name = None; value = { Node.value = Name name; _ } };
          ];
      } when String.equal "is_dict_like" ident && is_simple_name name
      ->
        let type_ = Type.dictionary ~key:Type.Any ~value:Type.Any in
        let refinement_unnecessary existing_annotation =
          annotation_less_or_equal
            ~left:existing_annotation
            ~right:(Annotation.create_mutable type_)
          && (not (Type.equal (Annotation.annotation existing_annotation) Type.Bottom))
          && not (Type.equal (Annotation.annotation existing_annotation) Type.Any)
          && not (Type.equal (Annotation.annotation existing_annotation) Type.Unknown)
        in
        
        (match existing_annotation name with
        | Some _ when Type.is_any type_ ->
          Value (Annotation.create_mutable type_ |> refine_local ~name)
        | Some existing_annotation when refinement_unnecessary existing_annotation ->
            Value (refine_local ~name existing_annotation)
        (* Clarify Anys if possible *)
        | Some existing_annotation
          when Type.equal (Annotation.annotation existing_annotation) Type.Any ->
            Value (Annotation.create_mutable type_ |> refine_local ~name)
        | Some existing_annotation
          when Type.can_unknown (Annotation.annotation existing_annotation) ->
            (* let type_ = GlobalResolution.join global_resolution type_ (Annotation.annotation existing_annotation) in *)
            Value (Annotation.create_mutable type_ |> refine_local ~name)
        | None -> Value resolution
        | Some existing_annotation ->
            let existing_type = Annotation.annotation existing_annotation in
            let { consistent_with_boundary; _ } = partition existing_type ~boundary:type_ in
            if not (Type.is_unbound consistent_with_boundary) then
              Value (Annotation.create_mutable consistent_with_boundary |> refine_local ~name)
            else if GlobalResolution.types_are_orderable global_resolution existing_type type_
            then
              Value (Annotation.create_mutable type_ |> refine_local ~name)
            else
              Unreachable
        )
    | Call
      {
        callee = { Node.value = Name (Name.Identifier ident | Name.Attribute { attribute=ident; _ }); _ };
        arguments =
          [
            { Call.Argument.name = None; value = { Node.value = Name name; _ } };
          ];
      } when (String.equal "is_list_like" ident || String.equal "is_sequence" ident) && is_simple_name name
      ->
        let type_ = Type.sequence Type.Any in
        let refinement_unnecessary existing_annotation =
          annotation_less_or_equal
            ~left:existing_annotation
            ~right:(Annotation.create_mutable type_)
          && (not (Type.equal (Annotation.annotation existing_annotation) Type.Bottom))
          && not (Type.equal (Annotation.annotation existing_annotation) Type.Any)
          && not (Type.equal (Annotation.annotation existing_annotation) Type.Unknown)
        in
        
        (match existing_annotation name with
        | Some _ when Type.is_any type_ ->
          Value (Annotation.create_mutable type_ |> refine_local ~name)
        | Some existing_annotation when refinement_unnecessary existing_annotation ->
            Value (refine_local ~name existing_annotation)
        (* Clarify Anys if possible *)
        | Some existing_annotation
          when Type.equal (Annotation.annotation existing_annotation) Type.Any ->
            Value (Annotation.create_mutable type_ |> refine_local ~name)
        | Some existing_annotation
          when Type.can_unknown (Annotation.annotation existing_annotation) ->
            (* let type_ = GlobalResolution.join global_resolution type_ (Annotation.annotation existing_annotation) in *)
            Value (Annotation.create_mutable type_ |> refine_local ~name)
        | None -> Value resolution
        | Some existing_annotation ->
            let existing_type = Annotation.annotation existing_annotation in
            let { consistent_with_boundary; _ } = partition existing_type ~boundary:type_ in
            if not (Type.is_unbound consistent_with_boundary) then
              Value (Annotation.create_mutable consistent_with_boundary |> refine_local ~name)
            else if GlobalResolution.types_are_orderable global_resolution existing_type type_
            then
              Value (Annotation.create_mutable type_ |> refine_local ~name)
            else
              Unreachable
        )
      | Call
      {
        callee = { Node.value = Name (Name.Identifier ident | Name.Attribute { attribute=ident; _ }); _ };
        arguments =
          [
            { Call.Argument.name = None; value = { Node.value = Name name; _ } };
          ];
      } when String.equal "is_float" ident && is_simple_name name
      ->
        let type_ = Type.float in
        let refinement_unnecessary existing_annotation =
          annotation_less_or_equal
            ~left:existing_annotation
            ~right:(Annotation.create_mutable type_)
          && (not (Type.equal (Annotation.annotation existing_annotation) Type.Bottom))
          && not (Type.equal (Annotation.annotation existing_annotation) Type.Any)
          && not (Type.equal (Annotation.annotation existing_annotation) Type.Unknown)
        in
        
        (match existing_annotation name with
        | Some _ when Type.is_any type_ ->
          Value (Annotation.create_mutable type_ |> refine_local ~name)
        | Some existing_annotation when refinement_unnecessary existing_annotation ->
            Value (refine_local ~name existing_annotation)
        (* Clarify Anys if possible *)
        | Some existing_annotation
          when Type.equal (Annotation.annotation existing_annotation) Type.Any ->
            Value (Annotation.create_mutable type_ |> refine_local ~name)
        | Some existing_annotation
          when Type.can_unknown (Annotation.annotation existing_annotation) ->
            (* let type_ = GlobalResolution.join global_resolution type_ (Annotation.annotation existing_annotation) in *)
            Value (Annotation.create_mutable type_ |> refine_local ~name)
        | None -> Value resolution
        | Some existing_annotation ->
            let existing_type = Annotation.annotation existing_annotation in
            let { consistent_with_boundary; _ } = partition existing_type ~boundary:type_ in
            if not (Type.is_unbound consistent_with_boundary) then
              Value (Annotation.create_mutable consistent_with_boundary |> refine_local ~name)
            else if GlobalResolution.types_are_orderable global_resolution existing_type type_
            then
              Value (Annotation.create_mutable type_ |> refine_local ~name)
            else
              Unreachable
        )        

    | Call
    {
        callee = { Node.value = Name (Name.Identifier ident | Name.Attribute { attribute=ident; _ }); _ };
        arguments =
          [
            { Call.Argument.name = None; value = { Node.value = Name name; _ } };
          ];
      } when String.equal "is_integer" ident && is_simple_name name
    ->

      let type_ = Type.integer in
      let refinement_unnecessary existing_annotation =
        annotation_less_or_equal
          ~left:existing_annotation
          ~right:(Annotation.create_mutable type_)
        && (not (Type.equal (Annotation.annotation existing_annotation) Type.Bottom))
        && not (Type.equal (Annotation.annotation existing_annotation) Type.Any)
        && not (Type.equal (Annotation.annotation existing_annotation) Type.Unknown)
      in

      (match existing_annotation name with
      | Some _ when Type.is_any type_ ->
        Value (Annotation.create_mutable type_ |> refine_local ~name)
      | Some existing_annotation when refinement_unnecessary existing_annotation ->
          Value (refine_local ~name existing_annotation)
      (* Clarify Anys if possible *)
      | Some existing_annotation
        when Type.equal (Annotation.annotation existing_annotation) Type.Any ->
          Value (Annotation.create_mutable type_ |> refine_local ~name)
      | Some existing_annotation
        when Type.can_unknown (Annotation.annotation existing_annotation) ->
          (* let type_ = GlobalResolution.join global_resolution type_ (Annotation.annotation existing_annotation) in *)
          Value (Annotation.create_mutable type_ |> refine_local ~name)
      | None -> Value resolution
      | Some existing_annotation ->
          let existing_type = Annotation.annotation existing_annotation in
          let { consistent_with_boundary; _ } = partition existing_type ~boundary:type_ in
          if not (Type.is_unbound consistent_with_boundary) then
            Value (Annotation.create_mutable consistent_with_boundary |> refine_local ~name)
          else if GlobalResolution.types_are_orderable global_resolution existing_type type_
          then
            Value (Annotation.create_mutable type_ |> refine_local ~name)
          else
            Unreachable
      )       
      
    | Call
    {
        callee = { Node.value = Name (Name.Identifier ident | Name.Attribute { attribute=ident; _ }); _ };
        arguments =
          [
            { Call.Argument.name = None; value = { Node.value = Name name; _ } };
          ];
      } when String.equal "is_bool" ident && is_simple_name name
    ->

      let type_ = Type.bool in
      let refinement_unnecessary existing_annotation =
        annotation_less_or_equal
          ~left:existing_annotation
          ~right:(Annotation.create_mutable type_)
        && (not (Type.equal (Annotation.annotation existing_annotation) Type.Bottom))
        && not (Type.equal (Annotation.annotation existing_annotation) Type.Any)
        && not (Type.equal (Annotation.annotation existing_annotation) Type.Unknown)
      in

      (match existing_annotation name with
      | Some _ when Type.is_any type_ ->
        Value (Annotation.create_mutable type_ |> refine_local ~name)
      | Some existing_annotation when refinement_unnecessary existing_annotation ->
          Value (refine_local ~name existing_annotation)
      (* Clarify Anys if possible *)
      | Some existing_annotation
        when Type.equal (Annotation.annotation existing_annotation) Type.Any ->
          Value (Annotation.create_mutable type_ |> refine_local ~name)
      | Some existing_annotation
        when Type.can_unknown (Annotation.annotation existing_annotation) ->
          (* let type_ = GlobalResolution.join global_resolution type_ (Annotation.annotation existing_annotation) in *)
          Value (Annotation.create_mutable type_ |> refine_local ~name)
      | None -> Value resolution
      | Some existing_annotation ->
          let existing_type = Annotation.annotation existing_annotation in
          let { consistent_with_boundary; _ } = partition existing_type ~boundary:type_ in
          if not (Type.is_unbound consistent_with_boundary) then
            Value (Annotation.create_mutable consistent_with_boundary |> refine_local ~name)
          else if GlobalResolution.types_are_orderable global_resolution existing_type type_
          then
            Value (Annotation.create_mutable type_ |> refine_local ~name)
          else
            Unreachable
      )         

    | Call
    {
        callee = { Node.value = Name (Name.Identifier ident | Name.Attribute { attribute=ident; _ }); _ };
        arguments =
          [
            { Call.Argument.name = None; value = { Node.value = Name name; _ } };
          ];
      } when String.equal "is_complex" ident && is_simple_name name
    ->

      let type_ = Type.complex in
      let refinement_unnecessary existing_annotation =
        annotation_less_or_equal
          ~left:existing_annotation
          ~right:(Annotation.create_mutable type_)
        && (not (Type.equal (Annotation.annotation existing_annotation) Type.Bottom))
        && not (Type.equal (Annotation.annotation existing_annotation) Type.Any)
        && not (Type.equal (Annotation.annotation existing_annotation) Type.Unknown)
      in

      (match existing_annotation name with
      | Some _ when Type.is_any type_ ->
        Value (Annotation.create_mutable type_ |> refine_local ~name)
      | Some existing_annotation when refinement_unnecessary existing_annotation ->
          Value (refine_local ~name existing_annotation)
      (* Clarify Anys if possible *)
      | Some existing_annotation
        when Type.equal (Annotation.annotation existing_annotation) Type.Any ->
          Value (Annotation.create_mutable type_ |> refine_local ~name)
      | Some existing_annotation
        when Type.can_unknown (Annotation.annotation existing_annotation) ->
          (* let type_ = GlobalResolution.join global_resolution type_ (Annotation.annotation existing_annotation) in *)
          Value (Annotation.create_mutable type_ |> refine_local ~name)
      | None -> Value resolution
      | Some existing_annotation ->
          let existing_type = Annotation.annotation existing_annotation in
          let { consistent_with_boundary; _ } = partition existing_type ~boundary:type_ in
          if not (Type.is_unbound consistent_with_boundary) then
            Value (Annotation.create_mutable consistent_with_boundary |> refine_local ~name)
          else if GlobalResolution.types_are_orderable global_resolution existing_type type_
          then
            Value (Annotation.create_mutable type_ |> refine_local ~name)
          else
            Unreachable
      )   

    | Call
    {
        callee = { Node.value = Name (Name.Identifier ident | Name.Attribute { attribute=ident; _ }); _ };
        arguments =
          [
            { Call.Argument.name = None; value = { Node.value = Name name; _ } };
          ];
      } when String.equal "is_named_tuple" ident && is_simple_name name
    ->

      let type_ = Type.tuple [Type.Any] in
      let refinement_unnecessary existing_annotation =
        annotation_less_or_equal
          ~left:existing_annotation
          ~right:(Annotation.create_mutable type_)
        && (not (Type.equal (Annotation.annotation existing_annotation) Type.Bottom))
        && not (Type.equal (Annotation.annotation existing_annotation) Type.Any)
        && not (Type.equal (Annotation.annotation existing_annotation) Type.Unknown)
      in

      (match existing_annotation name with
      | Some _ when Type.is_any type_ ->
        Value (Annotation.create_mutable type_ |> refine_local ~name)
      | Some existing_annotation when refinement_unnecessary existing_annotation ->
          Value (refine_local ~name existing_annotation)
      (* Clarify Anys if possible *)
      | Some existing_annotation
        when Type.equal (Annotation.annotation existing_annotation) Type.Any ->
          Value (Annotation.create_mutable type_ |> refine_local ~name)
      | Some existing_annotation
        when Type.can_unknown (Annotation.annotation existing_annotation) ->
          (* let type_ = GlobalResolution.join global_resolution type_ (Annotation.annotation existing_annotation) in *)
          Value (Annotation.create_mutable type_ |> refine_local ~name)
      | None -> Value resolution
      | Some existing_annotation ->
          let existing_type = Annotation.annotation existing_annotation in
          let { consistent_with_boundary; _ } = partition existing_type ~boundary:type_ in
          if not (Type.is_unbound consistent_with_boundary) then
            Value (Annotation.create_mutable consistent_with_boundary |> refine_local ~name)
          else if GlobalResolution.types_are_orderable global_resolution existing_type type_
          then
            Value (Annotation.create_mutable type_ |> refine_local ~name)
          else
            Unreachable
      )   
  

    (* Type is *not* the same as `annotation_expression` *)
    | ComparisonOperator
        {
          left =
            {
              Node.value =
                Call
                  {
                    callee = { Node.value = Name (Name.Identifier "type"); _ };
                    arguments = [{ Call.Argument.name = None; value }];
                  };
              _;
            };
          operator = ComparisonOperator.IsNot;
          right = annotation_expression;
        }
    | ComparisonOperator
        {
          left =
            {
              Node.value =
                Call
                  {
                    callee = { Node.value = Name (Name.Identifier "type"); _ };
                    arguments = [{ Call.Argument.name = None; value }];
                  };
              _;
            };
          operator = ComparisonOperator.NotEquals;
          right = annotation_expression;
        }
    | UnaryOperator
        {
          UnaryOperator.operator = UnaryOperator.Not;
          operand =
            {
              Node.value =
                Call
                  {
                    callee = { Node.value = Name (Name.Identifier "isinstance"); _ };
                    arguments =
                      [
                        { Call.Argument.name = None; value };
                        { Call.Argument.name = None; value = annotation_expression };
                      ];
                  };
              _;
            };
        } -> (
        let mismatched_type = parse_refinement_annotation annotation_expression in

        (* Log.dump "??? %a %a" Type.pp mismatched_type Resolution.pp resolution; *)

        let { Resolved.resolved; _ } = forward_expression ~resolution ~at_resolution value in
        let contradiction =
          if Type.contains_top mismatched_type || Type.is_any mismatched_type || Type.is_unknown mismatched_type then
            false
          else
            
            (not (Type.is_unbound resolved))
            && (not (Type.contains_top resolved))
            && (not (Type.is_any resolved))
            && (not (Type.can_unknown resolved))
            && GlobalResolution.less_or_equal
                  global_resolution
                  ~left:resolved
                  ~right:mismatched_type
        in

        let resolve ~name =
          match Resolution.get_local_with_attributes resolution ~name with
          | Some { annotation = previous_annotation; _ } ->
              let { not_consistent_with_boundary; _ } =
                partition previous_annotation ~boundary:mismatched_type
              in

              (match not_consistent_with_boundary with
              | Some t ->
                let r =
                t 
                |> Annotation.create_mutable
                |> refine_local ~name
                in
                r
              | None when Type.can_unknown mismatched_type ->
                (* Log.dump "HM????"; *)
                resolution
              | None -> 

                

                (match resolved with
                | Union t_list -> 
                  let new_list = List.filter t_list ~f:(fun t -> not (GlobalResolution.less_or_equal global_resolution ~left:t ~right:mismatched_type)) in
                  let new_list =
                    if Type.can_unknown resolved
                    then Type.Unknown::new_list
                    else new_list
                  in
                  if List.length new_list > 1 then
                    Type.Union new_list
                    |> Annotation.create_mutable
                    |> refine_local ~name
                  else if List.length new_list = 1 then
                    List.nth_exn new_list 0
                    |> Annotation.create_mutable
                    |> refine_local ~name
                  else
                    resolution
                | _ -> resolution
                )
              )

              (* not_consistent_with_boundary
              >>| Annotation.create_mutable
              >>| refine_local ~name
              |> Option.value ~default:resolution *)
          | _ -> resolution
        in
        match contradiction, value with
        | true, _ -> Unreachable
        | _, { Node.value = Name name; _ } when is_simple_name name -> 
          let x = (resolve ~name) in

         (*  Log.dump "??? %a" Resolution.pp resolution; *)

          Value x
        | _ -> Value resolution)

    | UnaryOperator
    {
      UnaryOperator.operator = UnaryOperator.Not;
      operand =
        {
          Node.value =
            Call
            {
              callee = { Node.value = Name (Name.Identifier ident | Name.Attribute { attribute=ident; _ }); _ };
              arguments =
                [
                  { Call.Argument.name = None; value };
                ];
            };
          _;
        };
    } when String.equal "is_list_like" ident -> (
    let mismatched_type = Type.sequence Type.Any in


    let { Resolved.resolved; _ } = forward_expression ~resolution ~at_resolution value in
    let contradiction =
      if Type.contains_top mismatched_type || Type.is_any mismatched_type then
        false
      else
        
        (not (Type.is_unbound resolved))
        && (not (Type.contains_top resolved))
        && (not (Type.is_any resolved))
        && (not (Type.can_unknown resolved))
        && GlobalResolution.less_or_equal
              global_resolution
              ~left:resolved
              ~right:mismatched_type
    in

    let resolve ~name =
      match Resolution.get_local_with_attributes resolution ~name with
      | Some { annotation = previous_annotation; _ } ->
          let { not_consistent_with_boundary; _ } =
            partition previous_annotation ~boundary:mismatched_type
          in

          (match not_consistent_with_boundary with
          | Some t ->
            t 
            |> Annotation.create_mutable
            |> refine_local ~name
          | None -> 
            (match resolved with
            | Union t_list -> 
              let new_list = List.filter t_list ~f:(fun t -> not (GlobalResolution.less_or_equal global_resolution ~left:t ~right:mismatched_type)) in
              let new_list =
                if Type.can_unknown resolved
                then Type.Unknown::new_list
                else new_list
              in
              if List.length new_list > 1 then
                Type.Union new_list
                |> Annotation.create_mutable
                |> refine_local ~name
              else if List.length new_list = 1 then
                List.nth_exn new_list 0
                |> Annotation.create_mutable
                |> refine_local ~name
              else
                resolution
            | _ -> resolution
            )
          )

          (* not_consistent_with_boundary
          >>| Annotation.create_mutable
          >>| refine_local ~name
          |> Option.value ~default:resolution *)
      | _ -> resolution
    in
    match contradiction, value with
    | true, _ -> Unreachable
    | _, { Node.value = Name name; _ } when is_simple_name name -> 
      let x = (resolve ~name) in
      Value x
    | _ -> Value resolution)

    | UnaryOperator
    {
      UnaryOperator.operator = UnaryOperator.Not;
      operand =
        {
          Node.value =
            Call
            {
              callee = { Node.value = Name (Name.Identifier ident | Name.Attribute { attribute=ident; _ }); _ };
              arguments =
                [
                  { Call.Argument.name = None; value };
                ];
            };
          _;
        };
    } when String.equal "is_dict_like" ident -> (
      let mismatched_type = Type.dictionary ~key:Type.Any ~value:Type.Any in


      let { Resolved.resolved; _ } = forward_expression ~resolution ~at_resolution value in
      let contradiction =
        if Type.contains_top mismatched_type || Type.is_any mismatched_type then
          false
        else
          
          (not (Type.is_unbound resolved))
          && (not (Type.contains_top resolved))
          && (not (Type.is_any resolved))
          && (not (Type.can_unknown resolved))
          && GlobalResolution.less_or_equal
                global_resolution
                ~left:resolved
                ~right:mismatched_type
      in

      let resolve ~name =
        match Resolution.get_local_with_attributes resolution ~name with
        | Some { annotation = previous_annotation; _ } ->
            let { not_consistent_with_boundary; _ } =
              partition previous_annotation ~boundary:mismatched_type
            in

            (match not_consistent_with_boundary with
            | Some t ->
              t 
              |> Annotation.create_mutable
              |> refine_local ~name
            | None -> 
              (match resolved with
              | Union t_list -> 
                let new_list = List.filter t_list ~f:(fun t -> not (GlobalResolution.less_or_equal global_resolution ~left:t ~right:mismatched_type)) in
                let new_list =
                  if Type.can_unknown resolved
                  then Type.Unknown::new_list
                  else new_list
                in
                if List.length new_list > 1 then
                  Type.Union new_list
                  |> Annotation.create_mutable
                  |> refine_local ~name
                else if List.length new_list = 1 then
                  List.nth_exn new_list 0
                  |> Annotation.create_mutable
                  |> refine_local ~name
                else
                  resolution
              | _ -> resolution
              )
            )

            (* not_consistent_with_boundary
            >>| Annotation.create_mutable
            >>| refine_local ~name
            |> Option.value ~default:resolution *)
        | _ -> resolution
      in
      match contradiction, value with
      | true, _ -> Unreachable
      | _, { Node.value = Name name; _ } when is_simple_name name -> 
        let x = (resolve ~name) in
        Value x
      | _ -> Value resolution)

 
      | UnaryOperator
      {
        UnaryOperator.operator = UnaryOperator.Not;
        operand =
          {
            Node.value =
              Call
              {
                callee = { Node.value = Name (Name.Identifier ident | Name.Attribute { attribute=ident; _ }); _ };
              arguments =
                [
                  { Call.Argument.name = None; value };
                ];
            };
          _;
        };
    } when String.equal "is_float" ident -> (
          let mismatched_type = Type.float in
    
    
          let { Resolved.resolved; _ } = forward_expression ~resolution ~at_resolution value in
          let contradiction =
            if Type.contains_top mismatched_type || Type.is_any mismatched_type then
              false
            else
              
              (not (Type.is_unbound resolved))
              && (not (Type.contains_top resolved))
              && (not (Type.is_any resolved))
              && (not (Type.can_unknown resolved))
              && GlobalResolution.less_or_equal
                    global_resolution
                    ~left:resolved
                    ~right:mismatched_type
          in
    
          let resolve ~name =
            match Resolution.get_local_with_attributes resolution ~name with
            | Some { annotation = previous_annotation; _ } ->
                let { not_consistent_with_boundary; _ } =
                  partition previous_annotation ~boundary:mismatched_type
                in
    
                (match not_consistent_with_boundary with
                | Some t ->
                  t 
                  |> Annotation.create_mutable
                  |> refine_local ~name
                | None -> 
                  (match resolved with
                  | Union t_list -> 
                    let new_list = List.filter t_list ~f:(fun t -> not (GlobalResolution.less_or_equal global_resolution ~left:t ~right:mismatched_type)) in
                    let new_list =
                      if Type.can_unknown resolved
                      then Type.Unknown::new_list
                      else new_list
                    in
                    if List.length new_list > 1 then
                      Type.Union new_list
                      |> Annotation.create_mutable
                      |> refine_local ~name
                    else if List.length new_list = 1 then
                      List.nth_exn new_list 0
                      |> Annotation.create_mutable
                      |> refine_local ~name
                    else
                      resolution
                  | _ -> resolution
                  )
                )
    
                (* not_consistent_with_boundary
                >>| Annotation.create_mutable
                >>| refine_local ~name
                |> Option.value ~default:resolution *)
            | _ -> resolution
          in
          match contradiction, value with
          | true, _ -> Unreachable
          | _, { Node.value = Name name; _ } when is_simple_name name -> 
            let x = (resolve ~name) in
            Value x
          | _ -> Value resolution)

      | UnaryOperator
      {
        UnaryOperator.operator = UnaryOperator.Not;
        operand =
          {
            Node.value =
              Call
              {
                callee = { Node.value = Name (Name.Identifier ident | Name.Attribute { attribute=ident; _ }); _ };
              arguments =
                [
                  { Call.Argument.name = None; value };
                ];
            };
          _;
        };
    } when String.equal "is_integer" ident -> (

          let mismatched_type = Type.integer in
    
    
          let { Resolved.resolved; _ } = forward_expression ~resolution ~at_resolution value in
          let contradiction =
            if Type.contains_top mismatched_type || Type.is_any mismatched_type then
              false
            else
              
              (not (Type.is_unbound resolved))
              && (not (Type.contains_top resolved))
              && (not (Type.is_any resolved))
              && (not (Type.can_unknown resolved))
              && GlobalResolution.less_or_equal
                    global_resolution
                    ~left:resolved
                    ~right:mismatched_type
          in
    
          let resolve ~name =
            match Resolution.get_local_with_attributes resolution ~name with
            | Some { annotation = previous_annotation; _ } ->
                let { not_consistent_with_boundary; _ } =
                  partition previous_annotation ~boundary:mismatched_type
                in
    
                (match not_consistent_with_boundary with
                | Some t ->
                  t 
                  |> Annotation.create_mutable
                  |> refine_local ~name
                | None -> 
                  (match resolved with
                  | Union t_list -> 
                    let new_list = List.filter t_list ~f:(fun t -> not (GlobalResolution.less_or_equal global_resolution ~left:t ~right:mismatched_type)) in
                    let new_list =
                      if Type.can_unknown resolved
                      then Type.Unknown::new_list
                      else new_list
                    in
                    if List.length new_list > 1 then
                      Type.Union new_list
                      |> Annotation.create_mutable
                      |> refine_local ~name
                    else if List.length new_list = 1 then
                      List.nth_exn new_list 0
                      |> Annotation.create_mutable
                      |> refine_local ~name
                    else
                      resolution
                  | _ -> resolution
                  )
                )
    
                (* not_consistent_with_boundary
                >>| Annotation.create_mutable
                >>| refine_local ~name
                |> Option.value ~default:resolution *)
            | _ -> resolution
          in

          match contradiction, value with
          | true, _ -> Unreachable
          | _, { Node.value = Name name; _ } when is_simple_name name -> 
            let x = (resolve ~name) in
            Value x
          | _ -> Value resolution)

    | UnaryOperator
    {
      UnaryOperator.operator = UnaryOperator.Not;
      operand =
        {
          Node.value =
            Call
            {
              callee = { Node.value = Name (Name.Identifier ident | Name.Attribute { attribute=ident; _ }); _ };
            arguments =
              [
                { Call.Argument.name = None; value };
              ];
          };
        _;
      };
  } when String.equal "is_bool" ident -> (

        let mismatched_type = Type.bool in
  
  
        let { Resolved.resolved; _ } = forward_expression ~resolution ~at_resolution value in
        let contradiction =
          if Type.contains_top mismatched_type || Type.is_any mismatched_type then
            false
          else
            
            (not (Type.is_unbound resolved))
            && (not (Type.contains_top resolved))
            && (not (Type.is_any resolved))
            && (not (Type.can_unknown resolved))
            && GlobalResolution.less_or_equal
                  global_resolution
                  ~left:resolved
                  ~right:mismatched_type
        in
  
        let resolve ~name =
          match Resolution.get_local_with_attributes resolution ~name with
          | Some { annotation = previous_annotation; _ } ->
              let { not_consistent_with_boundary; _ } =
                partition previous_annotation ~boundary:mismatched_type
              in
  
              (match not_consistent_with_boundary with
              | Some t ->
                t 
                |> Annotation.create_mutable
                |> refine_local ~name
              | None -> 
                (match resolved with
                | Union t_list -> 
                  let new_list = List.filter t_list ~f:(fun t -> not (GlobalResolution.less_or_equal global_resolution ~left:t ~right:mismatched_type)) in
                  let new_list =
                    if Type.can_unknown resolved
                    then Type.Unknown::new_list
                    else new_list
                  in
                  if List.length new_list > 1 then
                    Type.Union new_list
                    |> Annotation.create_mutable
                    |> refine_local ~name
                  else if List.length new_list = 1 then
                    List.nth_exn new_list 0
                    |> Annotation.create_mutable
                    |> refine_local ~name
                  else
                    resolution
                | _ -> resolution
                )
              )
  
              (* not_consistent_with_boundary
              >>| Annotation.create_mutable
              >>| refine_local ~name
              |> Option.value ~default:resolution *)
          | _ -> resolution
        in

        match contradiction, value with
        | true, _ -> Unreachable
        | _, { Node.value = Name name; _ } when is_simple_name name -> 
          let x = (resolve ~name) in
          Value x
        | _ -> Value resolution)

    | UnaryOperator
    {
      UnaryOperator.operator = UnaryOperator.Not;
      operand =
        {
          Node.value =
            Call
            {
              callee = { Node.value = Name (Name.Identifier ident | Name.Attribute { attribute=ident; _ }); _ };
            arguments =
              [
                { Call.Argument.name = None; value };
              ];
          };
        _;
      };
  } when String.equal "is_complex" ident -> (

        let mismatched_type = Type.complex in
  
  
        let { Resolved.resolved; _ } = forward_expression ~resolution ~at_resolution value in
        let contradiction =
          if Type.contains_top mismatched_type || Type.is_any mismatched_type then
            false
          else
            
            (not (Type.is_unbound resolved))
            && (not (Type.contains_top resolved))
            && (not (Type.is_any resolved))
            && (not (Type.can_unknown resolved))
            && GlobalResolution.less_or_equal
                  global_resolution
                  ~left:resolved
                  ~right:mismatched_type
        in
  
        let resolve ~name =
          match Resolution.get_local_with_attributes resolution ~name with
          | Some { annotation = previous_annotation; _ } ->
              let { not_consistent_with_boundary; _ } =
                partition previous_annotation ~boundary:mismatched_type
              in
  
              (match not_consistent_with_boundary with
              | Some t ->
                t 
                |> Annotation.create_mutable
                |> refine_local ~name
              | None -> 
                (match resolved with
                | Union t_list -> 
                  let new_list = List.filter t_list ~f:(fun t -> not (GlobalResolution.less_or_equal global_resolution ~left:t ~right:mismatched_type)) in
                  let new_list =
                    if Type.can_unknown resolved
                    then Type.Unknown::new_list
                    else new_list
                  in
                  if List.length new_list > 1 then
                    Type.Union new_list
                    |> Annotation.create_mutable
                    |> refine_local ~name
                  else if List.length new_list = 1 then
                    List.nth_exn new_list 0
                    |> Annotation.create_mutable
                    |> refine_local ~name
                  else
                    resolution
                | _ -> resolution
                )
              )
  
              (* not_consistent_with_boundary
              >>| Annotation.create_mutable
              >>| refine_local ~name
              |> Option.value ~default:resolution *)
          | _ -> resolution
        in

        match contradiction, value with
        | true, _ -> Unreachable
        | _, { Node.value = Name name; _ } when is_simple_name name -> 
          let x = (resolve ~name) in
          Value x
        | _ -> Value resolution)

    | UnaryOperator
    {
      UnaryOperator.operator = UnaryOperator.Not;
      operand =
        {
          Node.value =
            Call
            {
              callee = { Node.value = Name (Name.Identifier ident | Name.Attribute { attribute=ident; _ }); _ };
            arguments =
              [
                { Call.Argument.name = None; value };
              ];
          };
        _;
      };
    } when String.equal "is_named_tuple" ident -> (

        let mismatched_type = Type.tuple [Type.Any] in
  
  
        let { Resolved.resolved; _ } = forward_expression ~resolution ~at_resolution value in
        let contradiction =
          if Type.contains_top mismatched_type || Type.is_any mismatched_type then
            false
          else
            
            (not (Type.is_unbound resolved))
            && (not (Type.contains_top resolved))
            && (not (Type.is_any resolved))
            && (not (Type.can_unknown resolved))
            && GlobalResolution.less_or_equal
                  global_resolution
                  ~left:resolved
                  ~right:mismatched_type
        in
  
        let resolve ~name =
          match Resolution.get_local_with_attributes resolution ~name with
          | Some { annotation = previous_annotation; _ } ->
              let { not_consistent_with_boundary; _ } =
                partition previous_annotation ~boundary:mismatched_type
              in
  
              (match not_consistent_with_boundary with
              | Some t ->
                t 
                |> Annotation.create_mutable
                |> refine_local ~name
              | None -> 
                (match resolved with
                | Union t_list -> 
                  let new_list = List.filter t_list ~f:(fun t -> not (GlobalResolution.less_or_equal global_resolution ~left:t ~right:mismatched_type)) in
                  let new_list =
                    if Type.can_unknown resolved
                    then Type.Unknown::new_list
                    else new_list
                  in
                  if List.length new_list > 1 then
                    Type.Union new_list
                    |> Annotation.create_mutable
                    |> refine_local ~name
                  else if List.length new_list = 1 then
                    List.nth_exn new_list 0
                    |> Annotation.create_mutable
                    |> refine_local ~name
                  else
                    resolution
                | _ -> resolution
                )
              )
  
              (* not_consistent_with_boundary
              >>| Annotation.create_mutable
              >>| refine_local ~name
              |> Option.value ~default:resolution *)
          | _ -> resolution
        in

        match contradiction, value with
        | true, _ -> Unreachable
        | _, { Node.value = Name name; _ } when is_simple_name name -> 
          let x = (resolve ~name) in
          Value x
        | _ -> Value resolution)

    (* Is/is not callable *)
    | Call
        {
          callee = { Node.value = Name (Name.Identifier "callable"); _ };
          arguments = [{ Call.Argument.name = None; value = { Node.value = Name name; _ } }];
        }
      when is_simple_name name ->
        let resolution =
          match existing_annotation name with
          | Some existing_annotation ->
              let undefined =
                Type.Callable.create ~parameters:Undefined ~annotation:Type.object_primitive ()
              in
              let { consistent_with_boundary; _ } =
                partition (Annotation.annotation existing_annotation) ~boundary:undefined
              in
              if Type.equal consistent_with_boundary Type.Bottom then
                Annotation.create_mutable undefined |> refine_local ~name
              else
                Annotation.create_mutable consistent_with_boundary |> refine_local ~name
          | _ -> resolution
        in
        Value resolution
    | UnaryOperator
        {
          UnaryOperator.operator = UnaryOperator.Not;
          operand =
            {
              Node.value =
                Call
                  {
                    callee = { Node.value = Name (Name.Identifier "callable"); _ };
                    arguments =
                      [{ Call.Argument.name = None; value = { Node.value = Name name; _ } }];
                  };
              _;
            };
        }
      when is_simple_name name ->
        let resolution =
          match existing_annotation name with
          | Some existing_annotation ->
              let { not_consistent_with_boundary; _ } =
                partition
                  (Annotation.annotation existing_annotation)
                  ~boundary:
                    (Type.Callable.create
                        ~parameters:Undefined
                        ~annotation:Type.object_primitive
                        ())
              in
              not_consistent_with_boundary
              >>| Annotation.create_mutable
              >>| refine_local ~name
              |> Option.value ~default:resolution
          | _ -> resolution
        in
        Value resolution
    (* `is` and `in` refinement *)
    | ComparisonOperator
        {
          ComparisonOperator.left = { Node.value = Name name; _ };
          operator = ComparisonOperator.Is;
          right;
        }
      when is_simple_name name -> (
        
        let { Resolved.resolved = refined; _ } = forward_expression ~resolution ~at_resolution right in
        let refined = Annotation.create_mutable refined in
        
        match existing_annotation name with
        | Some previous ->
          
            if annotation_less_or_equal ~left:refined ~right:previous then (
              Value (refine_local ~name refined)
            
            )
            else (
              (* Keeping previous state, since it is more refined. *)
              (* TODO: once T38750424 is done, we should really return bottom if previous is not <=
                  refined and refined is not <= previous, as this is an obvious contradiction. *)
              Value resolution
            )
        | None -> Value resolution)
      | ComparisonOperator
        {
          ComparisonOperator.left = { Node.value = Name name; _};
          operator = ComparisonOperator.IsNot;
          right = { Node.value = Constant Constant.NoneLiteral; _ };
        } when is_simple_name name -> (
        
          (* let { StatementDefine.Signature.name=define_name; _ } = define_signature in
          if String.is_substring (Reference.show define_name) ~substring:"entity_component.EntityComponent"
            then (
              Log.dump "QQQ %a\n %a >>>" Resolution.pp resolution Name.pp name;
            ); *)

          match existing_annotation name with
          | Some { Annotation.annotation = Type.NoneType; _ } -> 
            (* Log.dump ">>> %a" Name.pp name; *)
            (* if String.is_substring (Reference.show define_name) ~substring:"entity_component.EntityComponent"
              then (
                Log.dump "OKOK %a >>> %a" Name.pp name Type.pp Type.NoneType;
              ); *)
  
            Unreachable
          | Some ({ Annotation.annotation = Type.Union parameters; _ } as annotation) ->
              let refined_annotation =
                List.filter parameters ~f:(fun parameter -> not ((Type.is_none parameter)))
              in
              (* if String.is_substring (Reference.show define_name) ~substring:"entity_component.EntityComponent"
                then (
                  Log.dump "OKOK %a >>> %a" Name.pp name Type.pp (Type.union refined_annotation);
                ); *)
              (* Log.dump "Name : %a => %a" Name.pp name Type.pp (Type.union refined_annotation); *)
              let resolution =
                refine_local
                  ~name
                  { annotation with Annotation.annotation = Type.union refined_annotation }
              in
              Value resolution
          | _ -> Value resolution
        )
    | ComparisonOperator
        {
          ComparisonOperator.left = { Node.value = Name name; _ };
          operator = ComparisonOperator.IsNot;
          right;
        }
      when is_simple_name name -> (
        let { Resolved.resolved = refined_type; _ } = forward_expression ~resolution ~at_resolution right in
        let refined = Annotation.create_mutable refined_type in
        
        match existing_annotation name with
        | Some previous ->
            let filter_refined_type =
              (match previous.annotation with
              | Type.Union t_list -> 
                let new_list = (List.filter t_list ~f:(fun t -> Type.is_unknown t || not (GlobalResolution.less_or_equal global_resolution ~left:t ~right:refined_type))) in
                if List.length new_list > 0
                then Type.Union new_list
                else Bottom
              | Unknown -> Unknown
              | t -> 
                if GlobalResolution.less_or_equal global_resolution ~left:t ~right:refined_type
                then Bottom
                else t
              )
            in

            

            if Type.is_bottom filter_refined_type then Unreachable
            else (
              let new_annotation = { refined with annotation=filter_refined_type; } in
              Value (refine_local ~name new_annotation)
            )

        | None -> Value resolution)
    | ComparisonOperator
        {
          ComparisonOperator.left = { Node.value = Name name; _ };
          operator = ComparisonOperator.In;
          right;
        }
      when is_simple_name name -> (
        let reference = name_to_reference_exn name in
        
        let { Resolved.resolved; _ } = forward_expression ~resolution ~at_resolution right in
        match
          GlobalResolution.extract_type_parameters
            global_resolution
            ~target:"typing.Iterable"
            ~source:resolved
        with
        | Some [element_type] -> (
            let annotation =
              Resolution.get_local_with_attributes ~global_fallback:false ~name resolution
            in
            match annotation with
            | Some previous ->
                let refined =
                  if Annotation.is_immutable previous then
                    Annotation.create_immutable
                      ~original:(Some (Annotation.original previous))
                      element_type
                  else
                    Annotation.create_mutable element_type
                in
                if annotation_less_or_equal ~left:refined ~right:previous then
                  Value (refine_local ~name refined)
                else (* Keeping previous state, since it is more refined. *)
                  Value resolution
            | None when not (Resolution.is_global resolution ~reference) ->
                let resolution = refine_local ~name (Annotation.create_mutable element_type) in
                Value resolution
            | _ -> Value resolution)
        | _ -> Value resolution)

    | ComparisonOperator
        {
          ComparisonOperator.left = { Node.value = Constant Constant.String { value = literal; kind = StringLiteral.String }; _ };
          operator = ComparisonOperator.NotIn;
          right = ({ Node.value = Name name; _ } as right);
        } when is_simple_name name
        ->  (
        let { Resolved.resolved; _ } = forward_expression ~resolution ~at_resolution right in
        let check_exist_field t name =
          (match t with
          | Type.OurTypedDictionary { typed_dict; _ } when not !Type.restrict_dict ->
            Type.OurTypedDictionary.get_field_annotation typed_dict name
            |> Option.is_some
          | _ -> false
          )
        in
        match resolved with
        | Type.Union t_list ->
            let new_list = (List.filter t_list ~f:(fun t -> not (check_exist_field t ("\"" ^ literal ^ "\"")))) in
            if List.length new_list > 0 then (
              let new_type = Type.union new_list in
              let refined = Annotation.create_mutable new_type in
              Value (refine_local ~name refined)
            ) else (
              Unreachable
            )
        | t when Type.is_dict t ->
          if check_exist_field t ("\"" ^ literal ^ "\"")
          then (
            Unreachable
          )
          else Value resolution
        | _ -> Value resolution
        )
    (* Not-none checks (including ones that work over containers) *)

          
        (* refine_resolution_for_assert ~resolution ~at_resolution left *)
    | Name name when is_simple_name name -> (
        
        match existing_annotation name with
        | Some { Annotation.annotation = Type.NoneType | Type.Literal (Boolean (false)) ; _ } -> 
          (* Log.dump ">>> %a" Name.pp name; *)
          Unreachable
        | Some ({ Annotation.annotation = Type.Union parameters; _ } as annotation) ->
            let refined_annotation =
              List.filter parameters ~f:(fun parameter -> not ((Type.is_none parameter) || Type.is_falsy parameter))
            in
            (* Log.dump "Name : %a => %a" Name.pp name Type.pp (Type.union refined_annotation); *)
            let resolution =
              refine_local
                ~name
                { annotation with Annotation.annotation = Type.union refined_annotation }
            in
            (* Log.dump "%a" Resolution.pp resolution; *)
            Value resolution
        | _ -> Value resolution)
    | UnaryOperator
      {
        UnaryOperator.operator = UnaryOperator.Not;
        operand =
          {
            Node.value =
              Name name
            ;
            _;
          };
      }
      
       when is_simple_name name -> (
          match existing_annotation name with
          | Some { Annotation.annotation; _ } when Type.is_truthy annotation -> 
            (* Log.dump ">>> %a" Name.pp name; *)
            Unreachable
          | Some { Annotation.annotation = Type.OurTypedDictionary _ ; _ } ->
            Unreachable
          | Some ({ Annotation.annotation = Type.Union parameters; _ } as annotation) ->
              let refined_annotation =
                List.filter parameters ~f:(fun parameter -> not (Type.is_ourtyped_dictionary parameter || Type.is_truthy parameter))
              in
              (* Log.dump "Name : %a => %a" Name.pp name Type.pp (Type.union refined_annotation); *)
              if List.length refined_annotation > 0 then (
                let resolution =
                  refine_local
                    ~name
                    { annotation with Annotation.annotation = Type.union refined_annotation }
                in
                Value resolution
              ) else (
                Unreachable
              )
          | _ -> Value resolution)
    | UnaryOperator
      {
        UnaryOperator.operator = UnaryOperator.Not;
        operand =
          {
            Node.value =
              (Expression.Constant _ | Expression.List _ | Expression.Dictionary _ | Expression.Tuple _ | Expression.Set _) as test
            ;
            _;
          };
      } when not (check_empty_constant test) ->
        (* Log.dump "WHAT?? %a" Expression.pp_expression test; *)
        Unreachable
    | Name _ ->
      (* Log.dump "Name : %a" Name.pp name; *)
      Value resolution

    | ComparisonOperator
      {
        ComparisonOperator.left = { Node.value = Call { 
          callee={ Node.value=Expression.Name (Name.Attribute { base={ Node.value=Expression.Name name; _ } as base; attribute; _ }); _ };
          arguments = [{ Call.Argument.name = None; value; }];
        }; _ };
        operator = ComparisonOperator.Is;
        right;
      } when String.equal attribute "__getitem__" ->
        let annotation_type = resolve_expression_type ~resolution ~at_resolution base in
        let value_type = resolve_expression_type ~resolution ~at_resolution base in
        let key_string = Expression.show value in

        let value_type = Type.get_dict_value_type ~with_key:(Some key_string) ~value_type annotation_type in


        let { Resolved.resolved = refined_type; _ } = forward_expression ~resolution ~at_resolution right in
        
        if (not !Type.restrict_dict) && GlobalResolution.less_or_equal global_resolution ~left:refined_type ~right:value_type then (
          let new_type = Type.OurTypedDictionary.set_dict_field annotation_type key_string refined_type in
          let resolution =
            refine_local
              ~name
              (Annotation.create_mutable new_type)
          in
          Value resolution
        )
        else (
          
          (* Keeping previous state, since it is more refined. *)
          (* TODO: once T38750424 is done, we should really return bottom if previous is not <=
              refined and refined is not <= previous, as this is an obvious contradiction. *)
          Value resolution
        )


    | ComparisonOperator
      {
        ComparisonOperator.left = { Node.value = Call { 
          callee={ Node.value=Expression.Name (Name.Attribute { base={ Node.value=Expression.Name name; _ } as base; attribute; _ }); _ };
          arguments = [{ Call.Argument.name = None; value; }];
        }; _ };
        operator = ComparisonOperator.IsNot;
        right;
      } when String.equal attribute "__getitem__" ->
        let annotation_type = resolve_expression_type ~resolution ~at_resolution base in
        let value_type = resolve_expression_type ~resolution ~at_resolution base in
        let key_string = Expression.show value in

        let value_type = Type.get_dict_value_type ~with_key:(Some key_string) ~value_type annotation_type in


        let { Resolved.resolved = refined_type; _ } = forward_expression ~resolution ~at_resolution right in
        
        let new_value_type = 
          (match value_type with
          | Type.Union t_list -> 
            let new_list = (List.filter t_list ~f:(fun t -> Type.is_unknown t || not (GlobalResolution.less_or_equal global_resolution ~left:t ~right:refined_type))) in
            if List.length new_list > 0
            then Type.Union new_list
            else Bottom
          | Unknown -> Unknown
          | t -> 
            if GlobalResolution.less_or_equal global_resolution ~left:t ~right:refined_type
            then Bottom
            else t
          )
        in

        if (not !Type.restrict_dict) && Type.is_bottom new_value_type then Unreachable
        else (
          let new_type = Type.OurTypedDictionary.set_dict_field annotation_type key_string new_value_type in
          let resolution =
            refine_local
              ~name
              (Annotation.create_mutable new_type)
          in
          Value resolution
        )

        
    | Call { 
        callee={ Node.value=Expression.Name (Name.Attribute { base={ Node.value=Expression.Name name; _ } as base; attribute; _ }); _ };
        arguments = [{ Call.Argument.name = None; value; }];
      } when String.equal attribute "__getitem__" -> (
        let annotation_type = resolve_expression_type ~resolution ~at_resolution base in
        let value_type = resolve_expression_type ~resolution ~at_resolution base in
        let key_string = Expression.show value in

        let value_type = Type.get_dict_value_type ~with_key:(Some key_string) ~value_type annotation_type in
        (match value_type with
        | Type.NoneType -> Unreachable
        | Type.Union parameters when (not !Type.restrict_dict) ->
          let refined_annotation =
            List.filter parameters ~f:(fun parameter -> not (Type.is_none parameter))
          in
          
          let new_type = Type.OurTypedDictionary.set_dict_field annotation_type key_string (Type.union refined_annotation) in
          let resolution =
            refine_local
              ~name
              (Annotation.create_mutable new_type)
          in
          Value resolution
        | _ ->  
          
          Value resolution
        )
      )

    | ComparisonOperator
        {
          ComparisonOperator.left = { Node.value = Constant Constant.NoneLiteral; _ };
          operator = ComparisonOperator.NotIn;
          right = { Node.value = Name name; _ };
        }
      when is_simple_name name -> (
        let annotation =
          Resolution.get_local_with_attributes ~global_fallback:false ~name resolution
        in
        match annotation with
        | Some annotation -> (
            match Annotation.annotation annotation with
            | Type.Parametric
                {
                  name = "list";
                  parameters =
                    [Single (Type.Union ([Type.NoneType; parameter] | [parameter; Type.NoneType]))];
                } ->
                let resolution =
                  refine_local ~name { annotation with Annotation.annotation = Type.list parameter }
                in
                Value resolution
            | _ -> Value resolution)
        | _ -> Value resolution)
    | Call
        {
          callee = { Node.value = Name (Name.Identifier "all"); _ };
          arguments = [{ Call.Argument.name = None; value = { Node.value = Name name; _ } }];
        }
      when is_simple_name name ->
        let resolution =
          match Resolution.get_local_with_attributes resolution ~name with
          | Some
              {
                Annotation.annotation =
                  Type.Parametric
                    { name = parametric_name; parameters = [Single (Type.Union parameters)] } as
                  annotation;
                _;
              }
            when GlobalResolution.less_or_equal
                    global_resolution
                    ~left:annotation
                    ~right:(Type.iterable (Type.Union parameters)) ->
              let parameters =
                List.filter parameters ~f:(fun parameter -> not (Type.is_none parameter))
              in
              refine_local
                ~name
                (Annotation.create_mutable
                    (Type.parametric parametric_name [Single (Type.union parameters)]))
          | _ -> resolution
        in
        Value resolution
    (* TypeGuard support *)
    | Call
        { arguments = { Call.Argument.name = None; value = { Node.value = Name name; _ } } :: _; _ }
      when is_simple_name name -> (
        let { Annotation.annotation = callee_type; _ } = resolve_expression ~resolution ~at_resolution test in
        match Type.typeguard_annotation callee_type with
        | Some guard_type ->
            let resolution = refine_local ~name (Annotation.create_mutable guard_type) in
            Value resolution
        | None -> Value resolution)
    (* Compound assertions *)
    | WalrusOperator { target; _ } -> refine_resolution_for_assert ~resolution ~at_resolution target
    | BooleanOperator { BooleanOperator.left; operator; right } -> (
        match operator with
        | BooleanOperator.And ->
            let left_state = refine_resolution_for_assert ~resolution ~at_resolution left in
            let right_state =
              left_state
              |> function
              | Unreachable -> Unreachable
              | Value resolution -> 
                (* Log.dump "HMM? %a" Resolution.pp resolution; *)
                refine_resolution_for_assert ~resolution ~at_resolution right
            in
            let state =
              match left_state, right_state with
              | Unreachable, _ -> Unreachable
              | _, Unreachable -> Unreachable
              | Value left_resolution, Value right_resolution ->
                  Value (Resolution.meet_refinements left_resolution right_resolution)
            in
            state
        | BooleanOperator.Or ->
            (* let left_state = refine_resolution_for_assert ~resolution ~at_resolution left in
            let right_state = refine_resolution_for_assert ~resolution ~at_resolution right in
            (match left_state, right_state with
            | Unreachable, Unreachable -> Unreachable *)
            let update resolution expression =
              refine_resolution_for_assert ~resolution ~at_resolution expression
              (*| > function
              | Value post_resolution -> post_resolution
              | Unreachable -> resolution *)
            in

            (* let left_state = refine_resolution_for_assert ~resolution ~at_resolution left *)

            let check_right resolution =
              match update resolution (normalize (negate left)) with
              | Unreachable -> Unreachable
              | Value resolution ->
                update resolution right
            in

            (match update resolution left with
            | Unreachable ->
              (* Log.dump "HE??"; *)
              check_right resolution
            | Value left_resolution -> 
              (match check_right resolution with
              | Unreachable ->
                (* Log.dump "Left %a \n Right %a" Expression.pp left Expression.pp right;
                Log.dump "Test LEft ==> %a" Resolution.pp left_resolution; *)
                Value left_resolution
              | Value right_resolution ->
                (* Log.dump "Left %a \n Right %a" Expression.pp left Expression.pp right;
                Log.dump "Test LEft With Right ==> %a" Resolution.pp (Resolution.outer_join_refinements left_resolution right_resolution); *)
                Value (Resolution.outer_join_refinements left_resolution right_resolution)
              )
            )
              (* let left_resolution = update resolution left in

              Log.dump "Test LEft %a ==> %a" Expression.pp left Resolution.pp left_resolution;

              let right_resolution =
                update resolution (normalize (negate left))
                |> fun resolution -> update resolution right
              in
              Value (Resolution.outer_join_refinements left_resolution right_resolution)) *)
    )
            
    (* Everything else has no refinement *)
    | _ -> (* Log.dump "Expression : %a" Expression.pp test;  *)Value resolution


  and forward_assert ?(origin = Assert.Origin.Assertion) ~resolution ~at_resolution test =
    let { Resolved.resolution; errors; _ } = forward_expression ~resolution ~at_resolution test in
    
    (* Log.dump "TEST : %a" Expression.pp test;

    Log.dump "%s" (Format.asprintf "[ Before Refined Resolution ]\n%a\n\n" Resolution.pp resolution); *)
    
    let resolution = refine_resolution_for_assert ~resolution ~at_resolution test in

    
    
  (*   (match resolution with
    | Value resolution -> Log.dump "%s" (Format.asprintf "[ Refined Resolution ]\n%a\n\n" Resolution.pp resolution);
    | Unreachable -> Log.dump "Unreachable";
    ); *)
    

    
    
    
    (* Ignore type errors from the [assert (not foo)] in the else-branch because it's the same [foo]
        as in the true-branch. This duplication of errors is normally ok because the errors get
        deduplicated in the error map and give one final error. However, it leads to two separate
        errors for [a < b] and [a >= b] (negation of <) since their error messages are different. So,
        ignore all else-branch assertion errors. *)
    let errors =
      match origin with
      | Assert.Origin.If { true_branch = false; _ }
      | Assert.Origin.While { true_branch = false; _ } 
        when (OurDomain.is_error_mode (OurDomain.load_mode ())) || OurDomain.is_recheck_mode (OurDomain.load_mode ()) ->
          []
      | _ -> errors
    in
    resolution, errors


  and forward_assignment ~resolution ~at_resolution ~location ~target ~annotation ~value =
    (* Log.dump "[Forward Assignment] Target %a \n %a" Expression.pp target Resolution.pp resolution; *)
    
    let { Node.value = { Define.signature = { name; parent; _ }; _ } as define; _ } = Context.define in
    let global_resolution = Resolution.global_resolution resolution in
    let errors, is_final, original_annotation =
      match annotation with
      | None -> [], false, None
      | Some annotation ->
          let annotation_errors, parsed_annotation =
            parse_and_check_annotation ~resolution annotation
          in
          let final_annotation, is_final =
            match Type.final_value parsed_annotation with
            | `Ok final_annotation -> Some final_annotation, true
            | `NoParameter -> None, true
            | `NotFinal -> Some parsed_annotation, false
          in
          let unwrap_class_variable annotation =
            Type.class_variable_value annotation |> Option.value ~default:annotation
          in
          annotation_errors, is_final, Option.map final_annotation ~f:unwrap_class_variable
    in
    match Node.value target with
    | Expression.Name (Name.Identifier _)
      when 
        let alias = delocalize target
            |> Expression.show
            |> GlobalResolution.aliases global_resolution
        in
        Option.is_some alias && not (String.equal (Option.value_exn ~message:"Alias Error" alias |> Type.show_alias) "(Type.TypeAlias top)") ->
        (* The statement has been recognized as a type alias definition instead of an actual value
            assignment. *)
        
        let parsed =
          GlobalResolution.parse_annotation ~validation:NoValidation global_resolution value
        in

        (* TODO(T35601774): We need to suppress subscript related errors on generic classes. *)
        let add_annotation_errors errors =
          add_invalid_type_parameters_errors ~resolution:global_resolution ~location ~errors parsed
          |> fun (errors, _) ->
          let errors =
            List.append
              errors
              (get_untracked_annotation_errors ~resolution:global_resolution ~location parsed)
          in
          errors
        in
        let add_type_variable_errors errors =
          match parsed with
          | Variable variable when Type.Variable.Unary.contains_subvariable variable ->
              emit_error
                ~errors
                ~location
                ~kind:
                  (AnalysisError.InvalidType
                      (AnalysisError.NestedTypeVariables (Type.Variable.Unary variable)))
          | Variable { constraints = Explicit [explicit]; _ } ->
              emit_error
                ~errors
                ~location
                ~kind:(AnalysisError.InvalidType (AnalysisError.SingleExplicit explicit))
          | _ -> errors
        in
        let add_prohibited_any_errors errors =
          let reference =
            match target.value with
            | Expression.Name (Name.Identifier identifier) -> Reference.create identifier
            | _ -> failwith "not possible"
          in
          if Type.expression_contains_any value && Type.contains_prohibited_any parsed then
            emit_error
              ~errors
              ~location
              ~kind:
                (Error.ProhibitedAny
                    {
                      missing_annotation =
                        {
                          Error.name = reference;
                          annotation = None;
                          given_annotation = Some parsed;
                          evidence_locations = [instantiate_path ~global_resolution target.location];
                          thrown_at_source = true;
                        };
                      is_type_alias = true;
                    })
          else
            errors
        in
        ( Value resolution,
          add_annotation_errors errors |> add_type_variable_errors |> add_prohibited_any_errors )
    | _ ->
        (* Processing actual value assignments. *)
        let resolution, errors, resolved_value =
          let { Resolved.resolution; errors = new_errors; resolved; _ } =
            let _ = name in
            (* forward_expression ~resolution ~at_resolution value *)
            (* 여기서 expression의 resolved_value가 정해지고 이것의 타입이 곧 annotation이 된다 *)
            (* if (OurDomain.is_inference_mode (OurDomain.load_mode ())) then 
              (match Node.value value with
              | Expression.Constant _ when String.equal (Reference.last name) "__init__" ->
                { Resolved.resolution; errors; resolved=Type.Unknown; resolved_annotation=None; base=None }
              | _ -> forward_expression ~resolution ~at_resolution value
              )
            else *)
              forward_expression ~resolution ~at_resolution value
          in
          resolution, List.append new_errors errors, resolved
        in


        (* Log.dump "Assign %a = %a : %a" Expression.pp target Expression.pp value Type.pp resolved_value; *)
        


        let guide =
          (* This is the annotation determining how we recursively break up the assignment. *)
          match original_annotation with
          | Some annotation when not (Type.contains_top annotation) -> annotation
          | _ -> resolved_value
        in
        let explicit = Option.is_some annotation in

        (*
        let guide =
          match guide with
          | Type.Union t_list -> 
            let t = (List.filter t_list ~f:(fun t -> not (Type.is_unknown t))) in
            if List.length t = 1 then List.nth_exn t 0 else Type.Union t
          | _ -> guide
        in
        *)

        (* __init__ method인 경우 attribute 기억하기 *)

        let rec forward_assign
            ~resolution
            ~errors
            ~target:({ Node.location; value = target_value } as target)
            ~guide
            ~resolved_value
            expression
          =

          let uniform_sequence_parameter annotation =
            let get_unbounded_annotation annotation = 
              let unbounded_annotation =
                match annotation with
                | Type.Tuple (Concatenation concatenation) ->
                    Type.OrderedTypes.Concatenation.extract_sole_unbounded_annotation concatenation
                | _ -> None
              in
              match unbounded_annotation with
              | Some annotation -> annotation
              | None -> (
                  match
                    GlobalResolution.extract_type_parameters
                      global_resolution
                      ~target:"typing.Iterable"
                      ~source:annotation
                  with
                  | Some [element_type] -> element_type
                  | _ -> Type.Unknown)
            in

            match annotation with
            | Type.Union t_list -> Type.Union (List.map t_list ~f:get_unbounded_annotation)
            | _ -> get_unbounded_annotation annotation

          in
          let nonuniform_sequence_parameters expected_size annotation =
            match annotation with
            | Type.Tuple (Concrete parameters) -> Some parameters
            | annotation when NamedTuple.is_named_tuple ~global_resolution ~annotation ->
                NamedTuple.field_annotations ~global_resolution annotation
            | annotation ->
                let parameters_from_getitem () =
                  (* Simulate __getitem__ in the fallback. *)
                  let synthetic = "$getitem_host" in
                  let resolution =
                    Resolution.new_local
                      resolution
                      ~reference:(Reference.create synthetic)
                      ~annotation:(Annotation.create_mutable annotation)
                  in
                  let getitem_type =
                    let callee =
                      let base =
                        Node.create_with_default_location
                          (Expression.Name (Name.Identifier synthetic))
                      in
                      Node.create_with_default_location
                        (Expression.Name
                            (Name.Attribute { base; attribute = "__getitem__"; special = true }))
                    in
                    

                    Resolution.resolve_expression_to_type
                      resolution
                      (Node.create_with_default_location
                          (Expression.Call
                            {
                              callee;
                              arguments =
                                [
                                  {
                                    Call.Argument.value =
                                      Node.create_with_default_location
                                        (Expression.Constant (Constant.Integer 0));
                                    name = None;
                                  };
                                ];
                            }))
                  in
                  match getitem_type with
                  | Type.Top
                  | Type.Any ->
                      None
                  | getitem_annotation ->
                      Some (List.init ~f:(fun _ -> getitem_annotation) expected_size)
                in
                Option.first_some
                  (Type.type_parameters_for_bounded_tuple_union annotation)
                  (parameters_from_getitem ())
          in
          let rec is_uniform_sequence annotation =
            match annotation with
            | Type.Tuple (Concatenation concatenation)
              when Type.OrderedTypes.Concatenation.is_fully_unbounded concatenation ->
                true
            (* Bounded tuples subclass iterable, but should be handled in the nonuniform case. *)
            | Type.Tuple _ -> false
            | Type.Union t_list
              when List.exists t_list ~f:Type.is_unknown ->
                is_uniform_sequence (Type.filter_unknown annotation)
            | Type.Union (Type.Tuple _ :: _)
              when Option.is_some (Type.type_parameters_for_bounded_tuple_union annotation) ->
                false
            | _ ->
                (not (NamedTuple.is_named_tuple ~global_resolution ~annotation))
                && Option.is_some
                      (GlobalResolution.type_of_iteration_value ~global_resolution annotation)
          in

          (*
          (* for get class attrs *)
          let rec get_class_attribute (attribute: Name.Attribute.t) =
            match attribute.base.value with
            | Expression.Name name ->
              (match name with
              | Name.Identifier identifier ->
                let self_identifier = Define.Signature.self_identifier define.signature in
                if String.equal identifier self_identifier 
                then (Some attribute.attribute)
                else None 
              | Name.Attribute attribute -> 
                get_class_attribute attribute 
              )
            | _ -> None
          in
          *)

          match target_value with
          | Expression.Name name -> (
              let resolved_base =
                match name with
                | Name.Identifier identifier -> 
                  `Identifier identifier
                | Name.Attribute attribute ->
                  (*
                    if (OurTypeSet.is_inference_mode (OurTypeSet.load_mode ())) && 
                      (Define.Signature.is_method define.signature) &&
                      (Reference.is_suffix ~suffix:(Reference.create_from_list ["__init__";]) define_name) then
                      let attr_opt = get_class_attribute attribute in
                      (match attr_opt with
                        | Some attr ->
                          let our_model = OurTypeSet.load_summary define_name in
                          let our_model = OurTypeSet.OurSummary.add_class_attribute our_model (Option.value_exn parent) attr in
                          OurTypeSet.save_summary our_model define_name
                        | _ -> ()
                      );
                    else
                      ();
                  *)
                    let resolved = resolve_expression_type ~resolution ~at_resolution attribute.base in
                    `Attribute (attribute, resolved)
              in

              let inner_assignment resolution errors resolved_base =
                let reference, attribute, target_annotation =
                  match resolved_base with
                  | `Identifier identifier ->
                      let reference = Reference.create identifier in
                      ( Some reference,
                        None,
                        from_reference ~location:Location.any reference
                        |> resolve_expression ~resolution ~at_resolution )
                  | `Attribute ({ Name.Attribute.base; attribute; _ }, resolved) ->
                      let name = attribute in
                      let parent, accessed_through_class =
                        if Type.is_meta resolved then
                          Type.single_parameter resolved, true
                        else
                          resolved, false
                      in
                      let parent_class_name = Type.split parent |> fst |> Type.primitive_name in
                      let reference =
                        match base with
                        | { Node.value = Name name; _ } when is_simple_name name ->
                            Some (Reference.create ~prefix:(name_to_reference_exn name) attribute)
                        | _ ->
                            parent_class_name
                            >>| Reference.create
                            >>| fun prefix -> Reference.create ~prefix attribute
                      in


                      let attribute =
                        parent_class_name
                        >>= GlobalResolution.attribute_from_class_name
                              ~resolution:global_resolution
                              ~name:attribute
                              ~instantiated:parent
                              ~transitive:true
                              ~accessed_through_class
                        >>| fun annotated -> annotated, attribute
                      in


                      let target_annotation =
                        match attribute with
                        | Some (attribute, _) -> AnnotatedAttribute.annotation attribute
                        | _ ->
                            (* The reason why we need to do resolve_expression on the entire target
                                again is to deal with imported globals. To fix it, we ought to stop
                                representing imported globals as `Expression.Name.Attribute`. *)
                            resolve_expression ~resolution ~at_resolution target
                      in

                      (* TODO : is_valid? *)
                      let target_annotation =
                        match Annotation.annotation target_annotation with
                        | Type.Top -> Annotation.create_mutable Type.Unknown
                        | _ -> target_annotation
                      in

                      begin
                        match attribute with
                        | Some (attribute, _)
                          when AnnotatedAttribute.property attribute
                                && AnnotatedAttribute.(
                                    [%compare.equal: visibility] (visibility attribute) ReadWrite)
                          ->
                            Context.Builder.add_property_setter_callees
                              ~attribute
                              ~instantiated_parent:parent
                              ~name
                              ~location:
                                (Location.with_module ~module_reference:Context.qualifier location)
                        | _ -> ()
                      end;
                      reference, attribute, target_annotation
                in
                let expected, is_immutable =
                  match original_annotation, target_annotation with
                  | Some original, _ when not (Type.is_type_alias original) -> 
                    original, true
                  | _, target_annotation when Annotation.is_immutable target_annotation ->
                      Annotation.original target_annotation, true
                  | _ -> Type.Unknown, false
                in
                
                (* Log.dump "Resolution : %a" Resolution.pp resolution; *)
                (* Log.dump "Expression : %a = %a" Expression.pp target Expression.pp value;
                Log.dump "Expected : %a" Type.pp expected; *)
               
                let find_getattr parent =
                  let attribute =
                    match Type.resolve_class parent with
                    | Some [{ instantiated; class_name; _ }] ->
                        GlobalResolution.attribute_from_class_name
                          class_name
                          ~accessed_through_class:false
                          ~transitive:true
                          ~resolution:global_resolution
                          ~name:"__getattr__"
                          ~instantiated
                    | _ -> None
                  in
                  match attribute with
                  | Some attribute when Annotated.Attribute.defined attribute -> (
                      match Annotated.Attribute.annotation attribute |> Annotation.annotation with
                      | Type.Parametric
                          { name = "BoundMethod"; parameters = [Single (Callable _); _] }
                      | Type.Callable _ ->
                          Some attribute
                      | _ -> None)
                  | _ -> None
                in
                let name_reference =
                  match name with
                  | Identifier identifier -> Reference.create identifier |> Option.some
                  | Attribute _ as name when is_simple_name name ->
                      name_to_reference_exn name |> Option.some
                  | _ -> None
                in
                let is_global =
                  name_reference
                  >>| (fun reference -> Resolution.is_global resolution ~reference)
                  |> Option.value ~default:false
                in
                let is_locally_initialized =
                  match name_reference with
                  | Some reference -> Resolution.has_nontemporary_annotation ~reference resolution
                  | None -> false
                in
                let check_errors errors resolved =
                  match reference with
                  | Some reference ->
                      let modifying_read_only_error =
                        match attribute, original_annotation with
                        | None, _ when is_locally_initialized || not explicit ->
                            Option.some_if
                              (Annotation.is_final target_annotation)
                              (AnalysisError.FinalAttribute reference)
                        | None, _ -> None
                        | Some _, Some _ ->
                            (* We presume assignments to annotated targets are valid re: Finality *)
                            None
                        | Some (attribute, _), None -> (
                            let open AnnotatedAttribute in
                            match
                              visibility attribute, property attribute, initialized attribute
                            with
                            | ReadOnly _, false, OnlyOnInstance when Define.is_constructor define ->
                                None
                            | ReadOnly _, false, OnClass when Define.is_class_toplevel define ->
                                None
                            | ReadOnly _, false, _ -> Some (AnalysisError.FinalAttribute reference)
                            | ReadOnly _, true, _ -> Some (ReadOnly reference)
                            | _ -> None)
                      in
                      
                      let check_assignment_compatibility errors =
                        let is_valid_enumeration_assignment =
                          let parent_annotation =
                            match parent with
                            | None -> Type.Top
                            | Some reference -> Type.Primitive (Reference.show reference)
                          in
                          let compatible =
                            if explicit then
                              GlobalResolution.less_or_equal
                                global_resolution
                                ~left:expected
                                ~right:resolved
                            else
                              true
                          in
                          GlobalResolution.less_or_equal
                            global_resolution
                            ~left:parent_annotation
                            ~right:Type.enumeration
                          && compatible
                        in
                        let is_incompatible =
                          let expression_is_ellipses =
                            match expression with
                            | Some { Node.value = Expression.Constant Constant.Ellipsis; _ } -> true
                            | _ -> false
                          in
                          is_immutable
                          && (not expression_is_ellipses)
                          && (not
                                (GlobalResolution.constraints_solution_exists
                                    global_resolution
                                    ~left:resolved
                                    ~right:expected))
                          && not is_valid_enumeration_assignment
                        in
                        let open Annotated in
                        match attribute with
                        | Some (attribute, name) when is_incompatible ->
                            Error.IncompatibleAttributeType
                              {
                                parent = Primitive (Attribute.parent attribute);
                                incompatible_type =
                                  {
                                    Error.name = Reference.create name;
                                    mismatch =
                                      Error.create_mismatch
                                        ~resolution:global_resolution
                                        ~actual:resolved
                                        ~expected
                                        ~covariant:true;
                                  };
                              }
                            |> fun kind -> emit_error ~errors ~location ~kind
                        | None when is_incompatible ->
                            Error.IncompatibleVariableType
                              {
                                incompatible_type =
                                  {
                                    Error.name = reference;
                                    mismatch =
                                      Error.create_mismatch
                                        ~resolution:global_resolution
                                        ~actual:resolved
                                        ~expected
                                        ~covariant:true;
                                  };
                                declare_location = instantiate_path ~global_resolution location;
                              }
                            |> fun kind -> emit_error ~errors ~location ~kind
                        | _ -> errors
                      in
                      
                      let check_assign_class_variable_on_instance errors =
                        match
                          ( resolved_base,
                            attribute >>| fst >>| Annotated.Attribute.class_variable,
                            attribute >>| fst >>| Annotated.Attribute.name )
                        with
                        | `Attribute (_, parent), Some true, Some class_variable
                          when Option.is_none original_annotation && not (Type.is_meta parent) ->
                            emit_error
                              ~errors
                              ~location
                              ~kind:
                                (Error.InvalidAssignment
                                    (ClassVariable { class_name = Type.show parent; class_variable }))
                        | _ -> errors
                      in
                      let check_final_is_outermost_qualifier errors =
                        original_annotation
                        >>| (fun annotation ->
                              if Type.contains_final annotation then
                                emit_error
                                  ~errors
                                  ~location
                                  ~kind:(Error.InvalidType (FinalNested annotation))
                              else
                                errors)
                        |> Option.value ~default:errors
                      in
                      let check_undefined_attribute_target errors =
                        match resolved_base, attribute with
                        | `Attribute ({ base; _ }, parent), Some (attribute, _)
                          when not (Annotated.Attribute.defined attribute) ->
                            let is_meta_typed_dictionary =
                              Type.is_meta parent
                              && GlobalResolution.is_typed_dictionary
                                    ~resolution:global_resolution
                                    (Type.single_parameter parent)
                            in
                            let is_getattr_returning_any_defined =
                              match
                                find_getattr parent
                                >>| AnnotatedAttribute.annotation
                                >>| Annotation.annotation
                              with
                              | Some
                                  (Type.Parametric
                                    {
                                      name = "BoundMethod";
                                      parameters =
                                        [
                                          Single (Callable { implementation = { annotation; _ }; _ });
                                          _;
                                        ];
                                    })
                              | Some (Type.Callable { implementation = { annotation; _ }; _ }) ->
                                  Type.is_any annotation
                              | _ -> false
                            in
                            let is_parent_class = 
                              match Type.resolve_class parent with
                              | Some _ -> true
                              | _ -> false
                            in
                            if is_meta_typed_dictionary || is_getattr_returning_any_defined || is_parent_class then
                              (* Ignore the error from the attribute declaration `Movie.name = ...`,
                                  which would raise an error because `name` was removed as an
                                  attribute from the TypedDictionary. *)
                              
                              errors
                            else
                              (* TODO(T64156088): To catch errors against the implicit call to a
                                  custom definition of `__setattr__`, we should run signature select
                                  against the value type. *)
                              let parent_module_path =
                                let ast_environment =
                                  GlobalResolution.ast_environment global_resolution
                                in
                                GlobalResolution.class_summary global_resolution parent
                                >>| Node.value
                                >>= fun { ClassSummary.qualifier; _ } ->
                                AstEnvironment.ReadOnly.get_module_path ast_environment qualifier
                              in

                              let skip_error = check_attribute ~class_origin:(ClassType parent) (AnnotatedAttribute.public_name attribute) in

                              if skip_error then
                                errors
                              else (
                              
                                emit_error
                                  ~errors
                                  ~location
                                  ~kind:
                                    (Error.UndefinedAttributeWithReference
                                        {
                                          reference = base;
                                          attribute = AnnotatedAttribute.public_name attribute;
                                          origin =
                                            Error.Class
                                              { class_origin = ClassType parent; parent_module_path };
                                        })
                              )
                        | _ -> errors
                      in
                      let check_nested_explicit_type_alias errors =
                        match name, original_annotation with
                        | Name.Identifier identifier, Some annotation
                          when Type.is_type_alias annotation && not (Define.is_toplevel define) ->
                            emit_error
                              ~errors
                              ~location
                              ~kind:(Error.InvalidType (NestedAlias identifier))
                        | _ -> errors
                      in
                      let check_enumeration_literal errors =
                        original_annotation
                        >>| emit_invalid_enumeration_literal_errors ~resolution ~at_resolution ~location ~errors
                        |> Option.value ~default:errors
                      in
                      let check_previously_annotated errors =
                        match name with
                        | Name.Identifier identifier ->
                            let is_defined =
                              Option.is_some
                                (Resolution.get_local
                                    ~global_fallback:true
                                    ~reference:(Reference.create identifier)
                                    resolution)
                            in
                            let is_reannotation_with_same_type =
                              (* TODO(T77219514): special casing for re-annotation in loops can be
                                  removed when fixpoint is gone *)
                              Annotation.is_immutable target_annotation
                              && Type.equal expected (Annotation.original target_annotation)
                            in
                            if
                              explicit
                              && (not (Define.is_toplevel define))
                              && is_defined
                              && not is_reannotation_with_same_type
                            then
                              emit_error
                                ~errors
                                ~location
                                ~kind:
                                  (Error.IllegalAnnotationTarget { target; kind = Reassignment })
                            else
                              errors
                        | _ -> errors
                      in
                      let errors =
                        match modifying_read_only_error with
                        | Some error ->
                            emit_error ~errors ~location ~kind:(Error.InvalidAssignment error)
                        | None ->
                            (* We don't check compatibility when we're already erroring about Final
                                reassingment *)
                            check_assignment_compatibility errors
                      in
                      check_assign_class_variable_on_instance errors
                      |> check_final_is_outermost_qualifier
                      |> check_undefined_attribute_target
                      |> check_nested_explicit_type_alias
                      |> check_enumeration_literal
                      |> check_previously_annotated
                  | _ -> errors
                in
                let check_for_missing_annotations errors resolved =
                  let insufficiently_annotated, thrown_at_source =
                    let is_reassignment =
                      (* Special-casing re-use of typed parameters as attributes *)
                      match name, Node.value value with
                      | ( Name.Attribute
                            { base = { Node.value = Name (Name.Identifier self); _ }; attribute; _ },
                          Name _ )
                        when String.equal (Identifier.sanitized self) "self" ->
                          let sanitized =
                            Ast.Transform.sanitize_expression value |> Expression.show
                          in
                          is_immutable
                          && (not (Type.contains_top expected))
                          && (String.equal attribute sanitized
                              || String.equal attribute ("_" ^ sanitized))
                      | _ -> false
                    in
                    match annotation with
                    | Some annotation when Type.expression_contains_any annotation ->
                        original_annotation
                        >>| Type.contains_prohibited_any
                        |> Option.value ~default:false
                        |> fun insufficient -> insufficient, true
                    | None when is_immutable && not is_reassignment ->
                        let thrown_at_source =
                          match define, attribute with
                          | _, None -> Define.is_toplevel define
                          | ( { StatementDefine.signature = { parent = Some parent; _ }; _ },
                              Some (attribute, _) ) ->
                              Type.Primitive.equal
                                (Reference.show parent)
                                (AnnotatedAttribute.parent attribute)
                              && (Define.is_class_toplevel define || Define.is_constructor define)
                          | _ -> false
                        in
                        ( Type.equal expected Type.Top || Type.contains_prohibited_any expected,
                          thrown_at_source )
                    | _ -> false, false
                  in
                  let actual_annotation, evidence_locations =
                    if Type.equal resolved Type.Top then
                      None, []
                    else
                      Some resolved, [instantiate_path ~global_resolution location]
                  in
                  let is_illegal_attribute_annotation attribute =
                    let attribute_parent = AnnotatedAttribute.parent attribute in
                    let parent_annotation =
                      match parent with
                      | None -> Type.Top
                      | Some reference -> Type.Primitive (Reference.show reference)
                    in
                    explicit
                    (* [Movie.items: int] would raise an error because [Mapping] also has [items]. *)
                    && (not
                          (GlobalResolution.is_typed_dictionary
                              ~resolution:global_resolution
                              parent_annotation))
                    && not (Type.equal parent_annotation (Primitive attribute_parent))
                  in
                  let parent_class =
                    match resolved_base with
                    | `Attribute (_, base_type) -> Type.resolve_class base_type
                    | _ -> None
                  in
                  match name, parent_class with
                  | Name.Identifier identifier, _ ->
                      let reference = Reference.create identifier in
                      if Resolution.is_global ~reference resolution && insufficiently_annotated then
                        let global_location =
                          Reference.delocalize reference
                          |> GlobalResolution.global_location global_resolution
                          >>| Location.strip_module
                          |> Option.value ~default:location
                        in
                        ( emit_error
                            ~errors
                            ~location:global_location
                            ~kind:
                              (Error.MissingGlobalAnnotation
                                  {
                                    Error.name = reference;
                                    annotation = actual_annotation;
                                    given_annotation = Option.some_if is_immutable expected;
                                    evidence_locations;
                                    thrown_at_source;
                                  }),
                          true )
                      else if explicit && insufficiently_annotated then
                        ( emit_error
                            ~errors
                            ~location
                            ~kind:
                              (Error.ProhibitedAny
                                  {
                                    missing_annotation =
                                      {
                                        Error.name = reference;
                                        annotation = actual_annotation;
                                        given_annotation = Option.some_if is_immutable expected;
                                        evidence_locations;
                                        thrown_at_source = true;
                                      };
                                    is_type_alias = false;
                                  }),
                          true )
                      else
                        errors, true
                  | Name.Attribute { base = { Node.value = Name base; _ }; attribute; _ }, None
                    when is_simple_name base && insufficiently_annotated ->
                      (* Module *)
                      let reference = name_to_reference_exn base in
                      if
                        explicit && not (GlobalResolution.module_exists global_resolution reference)
                      then
                        ( emit_error
                            ~errors
                            ~location
                            ~kind:
                              (Error.ProhibitedAny
                                  {
                                    missing_annotation =
                                      {
                                        Error.name = Reference.create ~prefix:reference attribute;
                                        annotation = actual_annotation;
                                        given_annotation = Option.some_if is_immutable expected;
                                        evidence_locations;
                                        thrown_at_source = true;
                                      };
                                    is_type_alias = false;
                                  }),
                          true )
                      else
                        errors, true
                  | ( Name.Attribute { attribute; _ },
                      Some ({ Type.instantiated; accessed_through_class; class_name } :: _) ) -> (
                      (* Instance *)
                      let reference = Reference.create attribute in
                      let attribute =
                        GlobalResolution.attribute_from_class_name
                          ~resolution:global_resolution
                          ~name:attribute
                          ~instantiated
                          ~accessed_through_class
                          ~transitive:true
                          class_name
                      in
                      match attribute with
                      | Some attribute ->
                          if is_illegal_attribute_annotation attribute then
                            (* Non-self attributes may not be annotated. *)
                            ( emit_error
                                ~errors
                                ~location
                                ~kind:
                                  (Error.IllegalAnnotationTarget
                                      { target; kind = InvalidExpression }),
                              false )
                          else if
                            Annotated.Attribute.defined attribute
                            && (not (Annotated.Attribute.property attribute))
                            && insufficiently_annotated
                          then
                            ( emit_error
                                ~errors
                                ~location
                                ~kind:
                                  (Error.MissingAttributeAnnotation
                                      {
                                        parent = Primitive (Annotated.Attribute.parent attribute);
                                        missing_annotation =
                                          {
                                            Error.name = reference;
                                            annotation = actual_annotation;
                                            given_annotation = Option.some_if is_immutable expected;
                                            evidence_locations;
                                            thrown_at_source;
                                          };
                                      }),
                              true )
                          else if insufficiently_annotated && explicit then
                            ( emit_error
                                ~errors
                                ~location
                                ~kind:
                                  (Error.ProhibitedAny
                                      {
                                        missing_annotation =
                                          {
                                            Error.name = reference;
                                            annotation = actual_annotation;
                                            given_annotation = Option.some_if is_immutable expected;
                                            evidence_locations;
                                            thrown_at_source = true;
                                          };
                                        is_type_alias = false;
                                      }),
                              true )
                          else
                            errors, true
                      | None ->
                          if
                            insufficiently_annotated
                            && GlobalResolution.is_typed_dictionary
                                  ~resolution:global_resolution
                                  (Type.Primitive class_name)
                          then
                            ( emit_error
                                ~errors
                                ~location
                                ~kind:
                                  (Error.ProhibitedAny
                                      {
                                        missing_annotation =
                                          {
                                            Error.name = reference;
                                            annotation = actual_annotation;
                                            given_annotation = Option.some_if is_immutable expected;
                                            evidence_locations;
                                            thrown_at_source = true;
                                          };
                                        is_type_alias = false;
                                      }),
                              true )
                          else
                            errors, true)
                  | _ ->
                      if explicit then
                        ( emit_error
                            ~errors
                            ~location
                            ~kind:
                              (Error.IllegalAnnotationTarget { target; kind = InvalidExpression }),
                          false )
                      else
                        errors, true
                in

                let propagate_annotations ~errors ~is_valid_annotation ~resolved_value_weakened =
                  let is_not_local = is_global && not (Define.is_toplevel Context.define.value) in
                  let refine_annotation annotation refined =
                    GlobalResolution.refine ~global_resolution annotation refined
                  in
                  (* 1. annotation을 만들고 : pyre_extensions or Int??
                    => resolve_value (Type.t) 따라간다
                  *)

                  let annotation =
                    (* Do not refine targets explicitly annotated as 'Any' to allow for escape hatch *)
                    (* Do not refine targets with invariance mismatch as we cannot keep the inferred
                        type up to date for mutable containers *)
                    let invariance_mismatch =
                      GlobalResolution.is_invariance_mismatch
                        global_resolution
                        ~right:expected
                        ~left:resolved_value
                    in

                    if explicit && is_valid_annotation then (
                      let guide_annotation = Annotation.create_immutable ~final:is_final guide in
                      if
                        Type.is_concrete resolved_value
                        && (not (Type.is_any guide))
                        && not invariance_mismatch
                      then
                        refine_annotation guide_annotation resolved_value
                      else
                        guide_annotation
                    )
                    else if is_immutable && (Type.is_unknown resolved_value) then (
                      if Type.is_any (Annotation.original target_annotation) || invariance_mismatch
                      then (
                        target_annotation
                      )
                      else(
                        refine_annotation target_annotation guide
                      )
                    )
                    else
                      Annotation.create_mutable resolved_value(* guide *) (* Guide Modify*)
                  in

                  
                  (* Log.dump "Annotation >>> %a / expected : %a / resolved : %a" Annotation.pp annotation Type.pp expected Type.pp resolved_value; *)
                  

                  (* 2. 또 업데이트??? *)
                  let errors, annotation =
                    if
                      (not explicit)
                      && Type.Variable.contains_escaped_free_variable
                            (Annotation.annotation annotation)
                    then
                      let kind =
                        Error.IncompleteType
                          {
                            target = { Node.location; value = target_value };
                            annotation = resolved_value_weakened;
                            attempted_action = Naming;
                          }
                      in
                      let converted =
                        Type.Variable.convert_all_escaped_free_variables_to_bottom
                          (Annotation.annotation annotation)
                        |> Type.top_to_bottom
                      in
                      emit_error ~errors ~location ~kind, { annotation with annotation = converted }
                    else
                      errors, annotation
                  in


                  let annotation =
                    if !OurDomain.on_any
                    then annotation
                    else (
                      if Type.can_unknown (annotation |> Annotation.annotation) then
                        Annotation.create_mutable Type.Any
                      else
                        annotation
                    )
                  in
                  (* 
                    * Annotation을 Update 한 후 Resolution 업데이트
                    * 그래서 Annotation을 잘 만들어야 한다!
                  *)

                  let resolution =
                    match name with
                    | Identifier identifier ->
                        Resolution.new_local
                          resolution
                          ~temporary:is_not_local
                          ~reference:(Reference.create identifier)
                          ~annotation
                    | Attribute _ as name when is_simple_name name -> (
                        match resolved_base, attribute with
                        | `Attribute (_, parent), Some (attribute, _)
                          when not
                                  (Annotated.Attribute.property attribute
                                  || Option.is_some (find_getattr parent)) ->
                            Resolution.new_local_with_attributes
                              ~temporary:(is_not_local || Annotated.Attribute.defined attribute)
                              resolution
                              ~name
                              ~annotation
                        | _ -> resolution)
                    | _ -> resolution
                in

                (* Log.dump "AFTER %a" Resolution.pp resolution; *)

                resolution, errors
              in

              let resolved_value_weakened =
                GlobalResolution.resolve_mutable_literals
                  global_resolution
                  ~resolve:(resolve_expression_type ~resolution ~at_resolution)
                  ~expression
                  ~resolved:resolved_value
                  ~expected
              in

              match resolved_value_weakened with
              | { resolved = resolved_value_weakened; typed_dictionary_errors = [] } ->
                  let errors = check_errors errors resolved_value_weakened in
                  let errors, is_valid_annotation =
                    check_for_missing_annotations errors resolved_value_weakened
                  in
                  propagate_annotations ~errors ~is_valid_annotation ~resolved_value_weakened
              | { typed_dictionary_errors; _ } ->
                  propagate_annotations
                    ~errors:(emit_typed_dictionary_errors ~errors typed_dictionary_errors)
                    ~is_valid_annotation:false
                    ~resolved_value_weakened:Type.Unknown
            in


            match resolved_base with
            | `Attribute (attribute, Type.Union types) ->
                (* Union[A,B].attr is valid iff A.attr and B.attr is valid *)
                let propagate (resolution, errors) t =
                  inner_assignment resolution errors (`Attribute (attribute, t))
                in
                let _, errors = List.fold types ~init:(resolution, errors) ~f:propagate in
                (* We process type as union again to populate resolution *)
                propagate (resolution, errors) (Union types)
            | resolved -> inner_assignment resolution errors resolved)
          | List elements
          | Tuple elements
            when is_uniform_sequence guide ->
              let propagate (resolution, errors) element =
                match Node.value element with
                | Expression.Starred (Starred.Once target) ->
                    let guide = uniform_sequence_parameter guide |> Type.list in
                    let resolved_value = uniform_sequence_parameter resolved_value |> Type.list in
                    
                    forward_assign ~resolution ~errors ~target ~guide ~resolved_value None
                | _ ->
                    let guide = uniform_sequence_parameter guide in
                    let resolved_value = uniform_sequence_parameter resolved_value in
                    forward_assign ~resolution ~errors ~target:element ~guide ~resolved_value None
              in
              List.fold elements ~init:(resolution, errors) ~f:propagate
          | List elements
          | Tuple elements ->
              let left, starred, right =
                let is_starred { Node.value; _ } =
                  match value with
                  | Expression.Starred (Starred.Once _) -> true
                  | _ -> false
                in
                let left, tail =
                  List.split_while elements ~f:(fun element -> not (is_starred element))
                in
                let starred, right =
                  let starred, right = List.split_while tail ~f:is_starred in
                  let starred =
                    match starred with
                    | [{ Node.value = Starred (Starred.Once starred); _ }] -> [starred]
                    | _ -> []
                  in
                  starred, right
                in
                left, starred, right
              in
              let assignees = left @ starred @ right in
              let errors, annotations =
                let split_types guide = 
                  match guide with
                  | Type.Any -> errors, List.map assignees ~f:(fun _ -> Type.Unknown)
                  | Type.Top -> errors, List.map assignees ~f:(fun _ -> Type.Top)
                  | Type.Unknown -> errors, List.map assignees ~f:(fun _ -> Type.Unknown)
                  | _ -> (
                      match nonuniform_sequence_parameters (List.length assignees) guide with
                      | None ->
                          let errors =
                            emit_error
                              ~errors
                              ~location
                              ~kind:
                                (Error.Unpack
                                    {
                                      expected_count = List.length assignees;
                                      unpack_problem = UnacceptableType guide;
                                    })
                          in
                          errors, List.map assignees ~f:(fun _ -> Type.Unknown)
                      | Some annotations ->
                          let annotations =
                            let has_starred_assignee = not (List.is_empty starred) in
                            let left, tail = List.split_n annotations (List.length left) in
                            let starred, right =
                              List.split_n tail (List.length tail - List.length right)
                            in
                            let starred =
                              if not (List.is_empty starred) then
                                let annotation =
                                  List.fold
                                    starred
                                    ~init:Type.Bottom
                                    ~f:(GlobalResolution.join global_resolution)
                                  |> Type.list
                                in
                                [annotation]
                              else if has_starred_assignee then
                                [Type.tuple []]
                              else
                                []
                            in
                            left @ starred @ right
                          in
                          if List.length annotations <> List.length assignees then
                            let errors =
                              emit_error
                                ~errors
                                ~location
                                ~kind:
                                  (Error.Unpack
                                      {
                                        expected_count = List.length assignees;
                                        unpack_problem = CountMismatch (List.length annotations);
                                      })
                            in
                            errors, List.map assignees ~f:(fun _ -> Type.Unknown)
                          else
                            errors, annotations)
                in

                match guide with
                | Type.Union t_list ->
                  List.fold t_list ~init:(errors, List.map assignees ~f:(fun _ -> Type.Unknown)) ~f:(fun (errors, types) t ->
                    let new_errors, new_types = split_types t in
                    errors@new_errors, List.map2_exn types new_types ~f:(GlobalResolution.join global_resolution)
                  )
                | _ -> split_types guide
              in
              List.zip_exn assignees annotations
              |> List.fold
                    ~init:(resolution, errors)
                    ~f:(fun (resolution, errors) (target, guide) ->
                      forward_assign ~resolution ~errors ~target ~guide ~resolved_value:guide None)
          | _ ->
              if Option.is_some annotation then
                ( resolution,
                  emit_error
                    ~errors
                    ~location
                    ~kind:(Error.IllegalAnnotationTarget { target; kind = InvalidExpression }) )
              else
                resolution, errors
        in
        
        (* Log.dump "BEFORE"; *)

        let after_resolution, errors =
          forward_assign ~resolution ~errors ~target ~guide ~resolved_value (Some value)
        in

        (* Log.dump "AFTER"; *)

        let resolution =
          (match Node.value target with
          | Expression.Name (Name.Identifier ident) ->
            let target_ref = Reference.create ident in
            if Reference.is_target target_ref && (String.is_substring ~substring:"__iter__().__next__()" (Expression.show value))
              then (
                let target_before_type = Resolution.get_local ~reference:target_ref resolution in
                match target_before_type with
                | Some t ->
                  let target_after_type = 
                    Resolution.get_local ~reference:target_ref after_resolution 
                    |> Option.value ~default:(Annotation.create_mutable Type.Unknown)
                  in
                  Resolution.refine_local resolution ~reference:target_ref ~annotation:(Annotation.join ~type_join:(GlobalResolution.join global_resolution) target_after_type t)
                | _ -> after_resolution
              )
              else
                after_resolution
          | _ ->
            after_resolution
          )
        in

        Value resolution, errors


  and resolve_expression ~resolution ~at_resolution expression =
    forward_expression ~resolution ~at_resolution expression
    |> fun { Resolved.resolved; resolved_annotation; _ } ->
    resolved_annotation |> Option.value ~default:(Annotation.create_mutable resolved)



  and resolve_expression_type ~resolution ~at_resolution expression =
    resolve_expression ~resolution ~at_resolution expression |> Annotation.annotation


  and resolve_expression_type_with_locals ~resolution ~at_resolution ~locals expression =
    let new_local resolution (reference, annotation) =
      Resolution.new_local resolution ~reference ~annotation
    in
    let resolution_with_locals = List.fold ~init:resolution ~f:new_local locals in
    resolve_expression ~resolution:resolution_with_locals ~at_resolution expression |> Annotation.annotation


  and resolve_reference_type ~resolution ~at_resolution reference =
    from_reference ~location:Location.any reference |> resolve_expression_type ~resolution ~at_resolution


  and emit_invalid_enumeration_literal_errors ~resolution ~at_resolution ~location ~errors annotation =
    let invalid_enumeration_literals =
      let is_invalid_enumeration_member = function
        | Type.Literal (Type.EnumerationMember { enumeration_type; member_name }) ->
            let global_resolution = Resolution.global_resolution resolution in
            let is_enumeration =
              GlobalResolution.class_exists global_resolution (Type.show enumeration_type)
              && GlobalResolution.less_or_equal
                    global_resolution
                    ~left:enumeration_type
                    ~right:Type.enumeration
            in
            let is_member_of_enumeration =
              let literal_expression =
                Node.create
                  ~location
                  (Expression.Name
                      (Attribute
                        {
                          base = Type.expression enumeration_type;
                          attribute = member_name;
                          special = false;
                        }))
              in
              let { Resolved.resolved = resolved_member_type; _ } =
                forward_expression ~resolution ~at_resolution literal_expression
              in
              GlobalResolution.less_or_equal
                global_resolution
                ~left:resolved_member_type
                ~right:enumeration_type
            in
            not (is_enumeration && is_member_of_enumeration)
        | _ -> false
      in
      Type.collect annotation ~predicate:is_invalid_enumeration_member
    in
    List.fold invalid_enumeration_literals ~init:errors ~f:(fun errors annotation ->
        emit_error
          ~errors
          ~location
          ~kind:(Error.InvalidType (InvalidType { annotation; expected = "an Enum member" })))


  let forward_statement ~resolution ~at_resolution ~statement:({ Node.location; value } as statement) =
    let _ = statement in
    (* Log.dump "%s" (Statement.show statement); *)
    let global_resolution = Resolution.global_resolution resolution in
    let validate_return = validate_return ~location in
    match value with
    | Statement.Assign { Assign.target; annotation; value } ->
        let x = forward_assignment ~resolution ~at_resolution ~location ~target ~annotation ~value in

        x

    | Assert { Assert.test; origin; _ } -> 
      forward_assert ~resolution ~at_resolution ~origin test
    | Delete expressions ->
        let process_expression (resolution, errors_sofar) expression =
          let { Resolved.resolution; errors; _ } = forward_expression ~resolution ~at_resolution expression in
          let resolution =
            match Node.value expression with
            | Name (Identifier identifier) ->
                Resolution.unset_local resolution ~reference:(Reference.create identifier)
            | _ -> resolution
          in
          resolution, List.append errors errors_sofar
        in
        let resolution, errors =
          List.fold expressions ~init:(resolution, []) ~f:process_expression
        in
        (Value resolution, errors)
    | Expression
        { Node.value = Call { callee; arguments = { Call.Argument.value = test; _ } :: _ }; _ }
      when Core.Set.mem Recognized.assert_functions (Expression.show callee) ->
        forward_assert ~resolution ~at_resolution test
    | Expression expression ->
        let { Resolved.resolution; resolved; errors; _ } =
          forward_expression ~resolution ~at_resolution expression
        in
        if Type.is_noreturn resolved then
          (Unreachable, errors)
        else
          (Value resolution, errors)
    | Raise { Raise.expression = Some expression; _ } ->
        let { Resolved.resolution; resolved; errors; _ } =
          forward_expression ~resolution ~at_resolution expression
        in
        let expected = Type.Primitive "BaseException" in
        let actual =
          if Type.is_meta resolved then
            Type.single_parameter resolved
          else
            resolved
        in
        let errors =
          if GlobalResolution.less_or_equal global_resolution ~left:actual ~right:expected then
            errors
          else
            emit_error
              ~errors
              ~location
              ~kind:(Error.InvalidException { expression; annotation = resolved })
        in
        (Value resolution, errors)
    | Raise _ -> Value resolution, []
    | Return { Return.expression; is_implicit } ->
        let { Resolved.resolution; resolved = return_type; errors; _ } =
          Option.value_map
            expression
            ~default:
              {
                Resolved.resolution;
                errors = [];
                resolved = Type.none;
                resolved_annotation = None;
                base = None;
              }
            ~f:(fun expression -> (* Log.dump "?? %a" Expression.pp expression; *) 
            forward_expression ~resolution ~at_resolution expression)
        in

        let ignore_lines = Context.ignore_lines in
        let is_ignore = 
          List.exists ignore_lines ~f:(fun { Ignore.location=ignore_location; _ } -> 
            let ignore_line = Location.line ignore_location in
            let node_line = Location.line location in

            ignore_line = node_line
          )
        in

        let actual =
          if is_ignore then 
            Type.Unknown
          else if define_signature.generator && not define_signature.async then
            Type.generator ~return_type ()
          else (
            match expression with
            | Some ({ Node.value=Expression.Name name; _ }) when is_simple_name name && (Reference.is_self (name_to_reference_exn name)) ->
              
              (* let x = 
                Resolution.get_local_with_attributes_of_anno ~name resolution
                >>| Annotation.annotation
                |> Option.value ~default:Type.Unknown
              in

              x *)
              return_type
            | _ ->
              return_type
          )
        in

        
        
        
        (* Log.dump "Before %a" Type.pp actual; *)
        let actual =
          Type.narrow_union ~join:(GlobalResolution.join global_resolution) ~less_or_equal:(GlobalResolution.less_or_equal global_resolution) actual
        in
        (* Log.dump "After %a" Type.pp actual; *)

        let { StatementDefine.Signature.name; _ } = define_signature in

        
        
        if (* OurDomain.is_inference_mode (OurDomain.load_mode ()) && *) (not (Reference.is_initialize name)) && (not is_ignore) then
          let our_summary = !Context.our_summary in
          let entry_arg_types = !Context.entry_arg_types in
          let convert_actual =
            actual
            |> Type.Variable.convert_all_escaped_free_variables_to_bottom
          in

          let convert_actual =
            if Type.is_any convert_actual || Type.is_top convert_actual then
              Type.Unknown
            else
              convert_actual
          in

          (* Log.dump "After %a" Type.pp convert_actual; *)

          (* (match expression with
          | Some expression ->
            let { StatementDefine.Signature.name=define_name; _ } = define_signature in
            if String.is_substring (Reference.show define_name) ~substring:"MultiIndex.format"
              && (String.equal (Expression.show expression) "$local_pandas?core?indexes?multi?MultiIndex?format$result_levels")
              then (
                Log.dump "%a" Resolution.pp resolution;
                
                Log.dump "RETURN %a ==> %a (%a) (%a)" Expression.pp expression Type.pp (return_type) Type.pp actual Type.pp convert_actual;
              );
          | _ -> ()
          ); *)
          
          OurDomain.OurSummary.add_return_type ~type_join:(GlobalResolution.join global_resolution) our_summary name entry_arg_types convert_actual;
          (* Context.our_summary := our_summary; *)
        else ();
        (Value resolution, validate_return expression ~resolution ~at_resolution ~errors ~actual ~is_implicit)
    | Define { signature = { Define.Signature.name; _ } as signature; _ } (* 이거 signature만 봄 *) ->
        let resolution =
          if Reference.is_local name then (* 내장 함수 *)
              type_of_signature ~resolution signature
              |> Type.Variable.mark_all_variables_as_bound
                    ~specific:(Resolution.all_type_variables_in_scope resolution)
(*             in
            let modified_signature = 
              (match signature with                    
              | Callable t -> (* TODO : Modify Resolution of callable *)
              (* Log.dump "Before %s... %a" name Type.pp (Callable t); *)
              let type_join = GlobalResolution.join global_resolution in
              let final_model = !OurDomain.our_model in
              let callable = OurDomain.OurSummary.get_callable ~type_join final_model t in
              (Type.Callable callable)

              | Parametric { name = "BoundMethod"; parameters = [Single (Callable t); other]} ->
              (* Log.dump "Before %s... %a" name Type.pp (Callable t); *)
              let type_join = GlobalResolution.join global_resolution in
              let final_model = !OurDomain.our_model in
              let callable = OurDomain.OurSummary.get_callable ~type_join final_model t in
              (Type.Parametric { name = "BoundMethod"; parameters = [Single (Callable callable); other]})
              

              | _ -> signature
              )
            in
            Log.dump "MOD : %a" Type.pp modified_signature;
            modified_signature *)
            |> Annotation.create_mutable
            |> fun annotation -> Resolution.new_local resolution ~reference:name ~annotation
            
          else (* class method는 여기로 *)
          (
            
            resolution
          )
        in
        (Value resolution, [])
    | Import { Import.from; imports } ->
        let undefined_imports =
          match from with
          | None ->
              List.filter_map imports ~f:(fun { Node.value = { Import.name; _ }; _ } ->
                  match GlobalResolution.module_exists global_resolution name with
                  | true -> None
                  | false -> (
                      match GlobalResolution.is_suppressed_module global_resolution name with
                      | true -> None
                      | false -> Some (Error.UndefinedModule name)))
          | Some from -> (
              match GlobalResolution.get_module_metadata global_resolution from with
              | None ->
                  if GlobalResolution.is_suppressed_module global_resolution from then
                    []
                  else
                    [Error.UndefinedModule from]
              | Some module_metadata ->
                  let ast_environment = GlobalResolution.ast_environment global_resolution in
                  List.filter_map
                    imports
                    ~f:(fun { Node.value = { Import.name = name_reference; _ }; _ } ->
                      let name = Reference.show name_reference in
                      match Module.get_export module_metadata name with
                      | Some _ ->
                          (* `name` is defined inside the module. *)
                          None
                      | None -> (
                          match Module.get_export module_metadata "__getattr__" with
                          | Some Module.Export.(Name (Define { is_getattr_any = true })) ->
                              (* The current module has `__getattr__: str -> Any` defined. *)
                              None
                          | _ ->
                              if
                                (* `name` is a submodule of the current package. *)
                                GlobalResolution.module_exists
                                  global_resolution
                                  (Reference.combine from name_reference)
                                || (* The current module is descendant of a placeholder-stub module. *)
                                GlobalResolution.is_suppressed_module global_resolution from
                              then
                                None
                              else
                                let origin_module =
                                  match
                                    AstEnvironment.ReadOnly.get_module_path ast_environment from
                                  with
                                  | Some source_path -> Error.ExplicitModule source_path
                                  | None -> Error.ImplicitModule from
                                in
                                Some (Error.UndefinedName { from = origin_module; name }))))
        in
        ( Value resolution,
          List.fold undefined_imports ~init:[] ~f:(fun errors undefined_import ->
              emit_error ~errors ~location ~kind:(Error.UndefinedImport undefined_import)))
    | Class class_statement ->
        (* Check that variance isn't widened on inheritence. Don't check for other errors. Nested
            classes and functions are analyzed separately. *)
        (* Class 에 모든 define body가 담겨 있음 *)
        if OurDomain.is_check_preprocess_mode (OurDomain.load_mode ()) then (
          (* List.iter class_statement.top_level_unbound_names ~f:(fun { name; _ } -> Log.dump "HMM %s" name); *)

          (*let { StatementDefine.Signature.name; _ } = define_signature in*)
          List.iter class_statement.body ~f:(fun ({ Node.value; _ } as statement) -> 
            match value with
            | Define { Define.signature={ Define.Signature.name=define_name; parameters; parent; decorators; _ }; _ } ->

              
              let our_model = !Context.our_summary in

              let exist_unknown_decorator = List.exists decorators ~f:(fun decorator ->
                let deco_str = Expression.show decorator in
                not (
                  String.equal deco_str "staticmethod" 
                || String.equal deco_str "classmethod" 
                || String.equal deco_str "property"
                || String.equal deco_str "asyncio.coroutine"
                || String.equal deco_str "callback"
                || String.equal deco_str "timeit"
                || String.is_substring deco_str ~substring:"Appender"
                )
              )
              in
              if exist_unknown_decorator then
                OurDomain.OurSummary.set_unknown_decorator our_model define_name;

              let attribute_storage = AttributeAnalysis.AttributeStorage.empty in
              let attribute_storage, _ = AttributeAnalysis.forward_statement (attribute_storage, AttributeAnalysis.SkipMap.empty) ~statement in
              

              
                (match parent, List.nth parameters 0 with
                | Some class_name, Some { Node.value={ Parameter.name=class_var; _ }; _ } -> (* class 함수 *)
                
                  let rec update_parent_model ~visit_set our_model class_name =
                    let visit_set = Reference.Set.add visit_set class_name in
                    (* 부모 클래스에 attribute 추가하기 *)
                    let class_summary = GlobalResolution.class_summary global_resolution (Type.Primitive (Reference.show class_name)) in
                    (match class_summary with
                    | Some { Node.value = class_summary; _ } ->
                      List.fold ~init:our_model (ClassSummary.base_classes class_summary) 
                        ~f:(fun model { Node.value = parent_class_exp; _ }  ->
                          match parent_class_exp with
                          | Name name ->
                            let class_name = name_to_reference name |> Option.value ~default:Reference.empty in
                            if not (Reference.Set.mem visit_set class_name) then (
                              OurTypeSet.OurSummaryResolution.add_parent_attributes model attribute_storage class_name class_var;
                              update_parent_model ~visit_set model class_name
                            ) else (
                              model
                            )
                          | _ -> model
                        )
                    | _ -> our_model
                    )
                  in


                  let our_model = update_parent_model ~visit_set:Reference.Set.empty our_model class_name in

                  let x =
                  OurDomain.OurSummary.add_usage_attributes our_model define_name attribute_storage ~class_name ~class_var
                  in

                  x
                  
                | _ -> 
                  OurDomain.OurSummary.add_usage_attributes our_model define_name attribute_storage
                );
              
              (* Context.our_summary := our_model; *)
              ()
            | _ -> ()
          )
        )
        else ();


        
        (* Log.dump "HMM >>> %a" OurDomain.OurSummary.pp !Context.our_summary; *)
          
        let check_base errors base =
          let check_pair errors extended actual =
            match extended, actual with
            | ( Type.Variable { Type.Record.Variable.RecordUnary.variance = left; _ },
                Type.Variable { Type.Record.Variable.RecordUnary.variance = right; _ } ) -> (
                match left, right with
                | Type.Variable.Covariant, Type.Variable.Invariant
                | Type.Variable.Contravariant, Type.Variable.Invariant
                | Type.Variable.Covariant, Type.Variable.Contravariant
                | Type.Variable.Contravariant, Type.Variable.Covariant ->
                    emit_error
                      ~errors
                      ~location
                      ~kind:
                        (Error.InvalidTypeVariance
                            { annotation = extended; origin = Error.Inheritance actual })
                | _ -> errors)
            | _, _ -> errors
          in
          let check_duplicate_typevars errors parameters base =
            let rec get_duplicate_typevars parameters duplicates =
              match parameters with
              | parameter :: rest when List.exists ~f:(Type.Variable.equal parameter) rest ->
                  get_duplicate_typevars rest (parameter :: duplicates)
              | _ -> duplicates
            in
            let emit_duplicate_errors errors variable =
              emit_error ~errors ~location ~kind:(Error.DuplicateTypeVariables { variable; base })
            in
            List.fold_left
              ~f:emit_duplicate_errors
              ~init:errors
              (get_duplicate_typevars (Type.Variable.all_free_variables parameters) [])
          in
          match GlobalResolution.parse_annotation global_resolution base with
          | Type.Parametric { name; _ } as parametric when String.equal name "typing.Generic" ->
              check_duplicate_typevars errors parametric GenericBase
          | Type.Parametric { name; parameters = extended_parameters } as parametric ->
              let errors =
                if String.equal name "typing.Protocol" then
                  check_duplicate_typevars errors parametric ProtocolBase
                else
                  errors
              in
              Type.Parameter.all_singles extended_parameters
              >>| (fun extended_parameters ->
                    let actual_parameters =
                      GlobalResolution.variables global_resolution name
                      >>= Type.Variable.all_unary
                      >>| List.map ~f:(fun unary -> Type.Variable unary)
                      |> Option.value ~default:[]
                    in
                    match
                      List.fold2 extended_parameters actual_parameters ~init:errors ~f:check_pair
                    with
                    | Ok errors -> errors
                    | Unequal_lengths -> errors)
              |> Option.value ~default:errors
          | _ -> errors
        in

        if OurDomain.is_check_preprocess_mode (OurDomain.load_mode ()) then
          (*let { StatementDefine.Signature.name=define_name; _ } = define_signature in*)
          let default_types = [
              "list";
              "tuple";
              "dict";
              "set";
              "str";
              "int";
              "float";
              "bool";
            ]
          in
          let rec get_attributes_of_class ?(is_first=false) ~our_model ~done_attrs ~visit_set name = 
            
            let class_summary = GlobalResolution.class_summary global_resolution (Type.Primitive (Reference.show name)) in
            let visit_set = Reference.Set.add visit_set name in
            (match class_summary with
            | Some { Node.value = class_summary; _ } 
              when not (List.exists default_types ~f:(fun default_type ->
                String.equal default_type (Reference.show name)
              ))
              ->
              
              let class_attrs = ClassSummary.attributes class_summary in

              if not (Reference.is_test name) then (
                let only_explicit =
                  Identifier.SerializableMap.fold (fun _ { Node.value={ClassSummary.Attribute.kind; name=attr_name; }; _ } only_explicit -> 
                    match kind with
                    | Simple { values; _ } ->
                      if List.length values = 1 then (
                        let { ClassSummary.Attribute.value; origin; } = List.hd_exn values in
                        match origin, Node.value value with
                        | Explicit, Expression.Constant _ ->
                          let t = Resolution.resolve_expression_to_type resolution value in
                          (match t with
                          | Type.Unknown -> only_explicit
                          | _ -> Identifier.Map.set ~key:attr_name ~data:t only_explicit
                          )
                        | _ -> only_explicit
                      ) else (
                        only_explicit
                      )
                    | _ -> only_explicit
                  ) class_attrs Identifier.Map.empty
                in

                Identifier.Map.iteri only_explicit ~f:(fun ~key ~data ->
                  (* Log.dump "%s => %a" key Type.pp data; *)
                  OurDomain.OurSummary.add_implicit_to_join our_model class_statement.name (Reference.create key) data
                );
              );
            
              let done_attrs = Identifier.SerializableMap.fold (fun _ { Node.value={ClassSummary.Attribute.kind; name=attr_name; }; _ } done_attrs -> 

                

                (match kind with
                | _ when Identifier.Set.exists done_attrs ~f:(fun done_attr -> String.equal done_attr attr_name) -> ()
                | Simple { values; implicit; _ } ->
                  let _ = implicit, is_first in



                  let is_column =
                    List.exists values ~f:(fun { value; _ } ->
                      (* if String.is_substring ~substring:"State" (Reference.show name) then
                        Log.dump "%a TEST %s ==> %a" Reference.pp name attr_name Expression.pp value; *)
                        (* Log.dump "%a TEST %s ==> %a (%b, %b, %b, %b, %b)" Reference.pp name attr_name Expression.pp value toplevel frozen primitive implicit nested_class; *)
                      match Node.value value with
                      | Expression.Call { callee = { Node.value = Name n; _ }; _ } when is_simple_name n ->
                        let name_reference = name_to_reference n in
                        (match name_reference with
                        | Some reference when String.is_substring ~substring:"sqlalchemy.Column" (Reference.show reference) -> 
                          true
                        | _ -> false
                        )
                      | _ -> false
                    )
                  in

                  let is_luigi_param =
                    List.exists values ~f:(fun { value; _ } ->
                      (* if String.is_substring ~substring:"State" (Reference.show name) then
                        Log.dump "%a TEST %s ==> %a" Reference.pp name attr_name Expression.pp value; *)

                      match Node.value value with
                      | Expression.Call { callee = { Node.value = Name n; _ }; _ } when is_simple_name n ->
                        let name_reference = name_to_reference n in
                        (match name_reference with
                        | Some reference when String.is_substring ~substring:"luigi.parameter.Parameter" (Reference.show reference) -> 
                          true
                        | _ -> false
                        )
                      | _ -> false
                    )
                  in

                  if is_column || is_luigi_param then ()
                  else (
                    OurDomain.OurSummary.add_class_attribute our_model class_statement.name attr_name
                  )
                | Property _ ->
                  OurDomain.OurSummary.add_class_property our_model class_statement.name attr_name
                | Method { signatures; _ } ->
                  List.iter signatures ~f:(fun signature ->
                    let arguments = AttributeAnalysis.CallInfo.of_parameters signature.parameters in
                    OurDomain.OurSummary.add_class_method our_model class_statement.name arguments attr_name
                  )
                );
                  
                Identifier.Set.add done_attrs attr_name
                ) class_attrs done_attrs
              in

              let base_classes = ClassSummary.base_classes class_summary in

              

              List.iter base_classes ~f:(fun { Node.value=base_class; _ } -> 
                match base_class with
                | Expression.Name n -> 
                  name_to_reference n |> (function
                    | Some reference when not (Reference.Set.mem visit_set reference)
                      -> 
                        
                        get_attributes_of_class ~our_model ~done_attrs ~visit_set reference
                    | _ -> ()
                  )
                | _ -> ()
              )
            | None when String.equal (Reference.last name) "TypedDict" ->
              OurDomain.OurSummary.add_class_attribute our_model class_statement.name "__getitem__";
              OurDomain.OurSummary.add_class_attribute our_model class_statement.name "__setitem__";
              ()
            | _ -> ()
            )
          in
          let our_model = !Context.our_summary in
          get_attributes_of_class ~is_first:true ~our_model ~done_attrs:Identifier.Set.empty ~visit_set:Reference.Set.empty class_statement.name;

          (* if String.is_substring (Reference.show class_statement.name) ~substring:"pandas.core.indexes.multi.MultiIndex"
            then (
              Log.dump ">>> %a" OurDomain.OurSummary.pp our_model;
            );  *)
          (* Context.our_summary := our_model; *)
          ()
          
            (*
            let our_model = OurTypeSet.load_summary saved_name in
            let our_model = 
              if StatementDefine.Signature.is_class_property signature
              then
                OurTypeSet.OurSummary.add_class_property our_model parent (Reference.last name)
              else
                our_model
            in
            OurTypeSet.save_summary our_model saved_name;
            *)
          
        else ();
        (Value resolution, List.fold (Class.base_classes class_statement) ~f:check_base ~init:[])
    | For _
    | If _
    | Match _
    | Try _
    | With _
    | While _ ->
        (* Check happens implicitly in the resulting control flow. *)
        (Value resolution, [])
    | Break
    | Continue
    | Global _
    | Nonlocal _
    | Pass ->
        (Value resolution, [])


  let initial ~resolution =
    let global_resolution = Resolution.global_resolution resolution in
    let {
      Node.location;
      value =
        {
          Define.signature =
            {
              name;
              parent;
              parameters;
              return_annotation;
              decorators;
              async;
              nesting_define;
              generator;
              _;
            } as signature;
          captures;
          unbound_names;
          _;
        } as define;
    }
      =
      Context.define
    in
    (* Add type variables *)
    let outer_scope_variables, current_scope_variables =
      let type_variables_of_class class_name =
        let unarize unary =
          let fix_invalid_parameters_in_bounds unary =
            match
              GlobalResolution.check_invalid_type_parameters global_resolution (Type.Variable unary)
            with
            | _, Type.Variable unary -> unary
            | _ -> failwith "did not transform"
          in
          fix_invalid_parameters_in_bounds unary |> fun unary -> Type.Variable.Unary unary
        in  
        let extract = function
          | Type.Variable.Unary unary -> unarize unary
          | ParameterVariadic variable -> ParameterVariadic variable
          | TupleVariadic variable -> TupleVariadic variable
        in
        Reference.show class_name
        |> GlobalResolution.variables global_resolution
        >>| List.map ~f:extract
        |> Option.value ~default:[]
      in
      let type_variables_of_define signature =
        let parser =
          GlobalResolution.annotation_parser ~allow_invalid_type_parameters:true global_resolution
        in
        let variables = GlobalResolution.variables global_resolution in
        let define_variables =
          AnnotatedCallable.create_overload_without_applying_decorators ~parser ~variables signature
          |> (fun { parameters; _ } -> Type.Callable.create ~parameters ~annotation:Type.Unknown ())
          |> Type.Variable.all_free_variables
          |> List.dedup_and_sort ~compare:Type.Variable.compare
        in
        let parent_variables =
          let { Define.Signature.parent; _ } = signature in
          (* PEP484 specifies that scope of the type variables of the outer class doesn't cover the
              inner one. We are able to inspect only 1 level of nesting class as a result. *)
          Option.value_map parent ~f:type_variables_of_class ~default:[]
        in
        List.append parent_variables define_variables
      in
      match Define.is_class_toplevel define with
      | true ->
          let class_name = Option.value_exn parent in
          [], type_variables_of_class class_name
      | false ->
          let define_variables = type_variables_of_define signature in
          let nesting_define_variables =
            let rec walk_nesting_define sofar = function
              | None -> sofar
              | Some define_name -> (
                  (* TODO (T57339384): This operation should only depend on the signature, not the
                      body *)
                  match GlobalResolution.define_body global_resolution define_name with
                  | None -> sofar
                  | Some
                      {
                        Node.value =
                          {
                            Define.signature = { Define.Signature.nesting_define; _ } as signature;
                            _;
                          };
                        _;
                      } ->
                      let sofar = List.rev_append (type_variables_of_define signature) sofar in
                      walk_nesting_define sofar nesting_define)
            in
            walk_nesting_define [] nesting_define
          in
          nesting_define_variables, define_variables
    in
    let resolution =
      List.append current_scope_variables outer_scope_variables
      |> List.fold ~init:resolution ~f:(fun resolution variable ->
              Resolution.add_type_variable resolution ~variable)
    in
    
    (*
    Log.dump "\n\n[[[ Initial Resolution ]]] \n%a\n\n" Resolution.pp resolution;
    *)

    let check_decorators resolution errors =
      let check_final_decorator errors =
        if Option.is_none parent && Define.is_final_method define then
          emit_error
            ~errors
            ~location
            ~kind:(Error.InvalidInheritance (NonMethodFunction "typing.final"))
        else
          errors
      in
      let check_override_decorator errors =
        let override_decorator_name = "pyre_extensions.override" in
        let has_override_decorator = StatementDefine.has_decorator define override_decorator_name in
        if has_override_decorator then
          match define with
          | { Ast.Statement.Define.signature = { parent = Some parent; _ }; _ } -> (
              let possibly_overridden_attribute =
                GlobalResolution.overrides
                  (Reference.show parent)
                  ~resolution:global_resolution
                  ~name:(StatementDefine.unqualified_name define)
              in
              match possibly_overridden_attribute with
              | Some _ -> errors
              | None ->
                  emit_error
                    ~errors
                    ~location
                    ~kind:
                      (Error.InvalidOverride
                          { parent = Reference.show parent; decorator = NothingOverridden }))
          | { Ast.Statement.Define.signature = { parent = None; _ }; _ } ->
              emit_error
                ~errors
                ~location
                ~kind:(Error.InvalidOverride { parent = ""; decorator = IllegalOverrideDecorator })
        else
          errors
      in
      let check_decorator errors decorator =
        let get_allowlisted decorator =
          match Decorator.from_expression decorator with
          | None -> None
          | Some decorator ->
              let has_suffix
                  { Ast.Statement.Decorator.name = { Node.value = name; _ }; arguments }
                  suffix
                =
                Option.is_none arguments && String.equal (Reference.last name) suffix
              in
              let is_property_derivative decorator =
                has_suffix decorator "setter"
                || has_suffix decorator "getter"
                || has_suffix decorator "deleter"
                (* || has_suffix decorator "timeit" *)
              in
              let is_attr_validator decorator = has_suffix decorator "validator" in
              let is_click_derivative decorator = has_suffix decorator "command" in
              (* TODO (T41383196): Properly deal with @property and @click *)
              Option.some_if
                (is_property_derivative decorator
                || is_click_derivative decorator
                || is_attr_validator decorator)
                decorator
        in
        match get_allowlisted decorator with
        | Some { Ast.Statement.Decorator.name = { Node.value = decorator_name; _ }; _ } -> (
            match Reference.as_list decorator_name |> List.rev with
            | "setter" :: decorated_property_name :: _ ->
                if String.equal (Reference.last name) decorated_property_name then
                  errors
                else
                  emit_error
                    ~errors
                    ~location
                    ~kind:
                      (Error.InvalidDecoration
                          (Error.SetterNameMismatch
                            {
                              name = decorator_name;
                              actual = decorated_property_name;
                              expected = Reference.last name;
                            }))
            | _ -> errors)
        | None ->
            let { Resolved.errors = decorator_errors; _ } =
              forward_expression ~resolution ~at_resolution:None decorator
            in
            List.append decorator_errors errors
      in
      List.fold decorators ~init:errors ~f:check_decorator
      |> check_final_decorator
      |> check_override_decorator
    in
    let check_unbound_names errors =
      let add_unbound_name_error errors { Define.NameAccess.name; location } =
        match GlobalResolution.get_module_metadata global_resolution Reference.empty with
        | Some module_metadata when Option.is_some (Module.get_export module_metadata name) ->
            (* Do not error on names defined in empty qualifier space, e.g. custom builtins. *)
            errors
        | _ -> emit_error ~errors ~location ~kind:(AnalysisError.UnboundName name)
      in
      List.fold unbound_names ~init:errors ~f:add_unbound_name_error
    in
    let check_return_annotation resolution errors =
      let add_missing_return_error ~errors annotation =
        let return_annotation =
          let annotation =
            let parser = GlobalResolution.annotation_parser global_resolution in
            Annotated.Callable.return_annotation_without_applying_decorators ~signature ~parser
          in
          if async && not generator then
            Type.coroutine_value annotation |> Option.value ~default:Type.Unknown
          else
            annotation
        in
        let return_annotation = Type.Variable.mark_all_variables_as_bound return_annotation in
        let contains_literal_any =
          Type.contains_prohibited_any return_annotation
          && annotation >>| Type.expression_contains_any |> Option.value ~default:false
        in
        if
          ((not (Define.is_toplevel define)) && not (Define.is_class_toplevel define))
          && not (Option.is_some annotation)
          || contains_literal_any
        then
          emit_error
            ~errors
            ~location
            ~kind:
              (Error.MissingReturnAnnotation
                  {
                    name = Reference.create "$return_annotation";
                    annotation = None;
                    given_annotation =
                      Option.some_if (Define.has_return_annotation define) return_annotation;
                    evidence_locations = [];
                    thrown_at_source = true;
                  })
        else
          errors
      in
      let add_variance_error ~errors annotation =
        match annotation with
        | Type.Variable variable when Type.Variable.Unary.is_contravariant variable ->
            emit_error
              ~errors
              ~location
              ~kind:(Error.InvalidTypeVariance { annotation; origin = Error.Return })
        | _ -> errors
      in
      let add_async_generator_error ~errors annotation =
        if async && generator then
          let async_generator_type =
            Type.parametric "typing.AsyncGenerator" [Single Type.Unknown; Single Type.Unknown]
          in
          if
            GlobalResolution.less_or_equal
              ~left:async_generator_type
              ~right:annotation
              global_resolution
          then
            errors
          else
            emit_error
              ~errors
              ~location
              ~kind:(Error.IncompatibleAsyncGeneratorReturnType annotation)
        else
          errors
      in
      let errors = add_missing_return_error ~errors return_annotation in
      match return_annotation with
      | None -> errors
      | Some return_annotation ->
          let annotation_errors, annotation =
            parse_and_check_annotation ~resolution return_annotation
          in
          List.append annotation_errors errors
          |> fun errors ->
          add_async_generator_error ~errors annotation
          |> fun errors -> add_variance_error ~errors annotation
    in
    let add_capture_annotations resolution errors =
      let process_signature ({ Define.Signature.name; _ } as signature) =
        if Reference.is_local name then
          type_of_signature ~resolution signature
          |> Type.Variable.mark_all_variables_as_bound ~specific:outer_scope_variables
          |> Annotation.create_mutable
          |> fun annotation -> Resolution.new_local resolution ~reference:name ~annotation
        else
          resolution
      in
      let process_capture (resolution, errors) { Define.Capture.name; kind } =
        let resolution, errors, annotation =
          match kind with
          | Define.Capture.Kind.Annotation None ->
              ( resolution,
                emit_error ~errors ~location ~kind:(Error.MissingCaptureAnnotation name),
                Type.Unknown )
          | Define.Capture.Kind.Annotation (Some annotation_expression) ->
              let annotation_errors, annotation =
                parse_and_check_annotation ~resolution annotation_expression
              in
              resolution, List.append annotation_errors errors, annotation
          | Define.Capture.Kind.DefineSignature signature ->
              ( resolution,
                errors,
                type_of_signature ~resolution signature
                |> Type.Variable.mark_all_variables_as_bound ~specific:outer_scope_variables )
          | Define.Capture.Kind.Self parent ->
              resolution, errors, type_of_parent ~global_resolution parent
          | Define.Capture.Kind.ClassSelf parent ->
              resolution, errors, type_of_parent ~global_resolution parent |> Type.meta
        in
        let annotation = Annotation.create_mutable annotation in
        let resolution =
          let reference = Reference.create name in
          Resolution.new_local resolution ~reference ~annotation
        in
        resolution, errors
      in
      let resolution = process_signature signature in
      List.fold captures ~init:(resolution, errors) ~f:process_capture
    in
    let check_parameter_annotations resolution errors =
      let make_parameter_name name =
        name
        |> String.filter ~f:(function
                | '*' -> false
                | _ -> true)
        |> Reference.create
      in
      let check_parameter
          index
          (new_resolution, errors)
          { Node.location; value = { Parameter.name; value; annotation } }
        =
        let add_incompatible_variable_error ~errors annotation default =
          if
            Type.is_any default
            || GlobalResolution.less_or_equal global_resolution ~left:default ~right:annotation
            || GlobalResolution.constraints_solution_exists
                  global_resolution
                  ~left:default
                  ~right:annotation
          then
            errors
          else
            emit_error
              ~errors
              ~location
              ~kind:
                (Error.IncompatibleVariableType
                    {
                      incompatible_type =
                        {
                          name = Reference.create name;
                          mismatch =
                            Error.create_mismatch
                              ~resolution:global_resolution
                              ~expected:annotation
                              ~actual:default
                              ~covariant:true;
                        };
                      declare_location = instantiate_path ~global_resolution location;
                    })
        in
        let add_missing_parameter_annotation_error ~errors ~given_annotation annotation =
          let name = name |> Identifier.sanitized in
          let is_dunder_new_method_for_named_tuple =
            Define.is_method define
            && Reference.is_suffix ~suffix:(Reference.create ".__new__") define.signature.name
            && Option.value_map
                  ~default:false
                  ~f:(name_is ~name:"typing.NamedTuple")
                  return_annotation
          in
          if
            String.equal name "*"
            || String.is_prefix ~prefix:"_" name
            || Option.is_some given_annotation
                && (String.is_prefix ~prefix:"**" name || String.is_prefix ~prefix:"*" name)
            || is_dunder_new_method_for_named_tuple
            || String.equal name "/"
          then
            errors
          else
            emit_error
              ~errors
              ~location
              ~kind:
                (Error.MissingParameterAnnotation
                    {
                      name = Reference.create name;
                      annotation;
                      given_annotation;
                      evidence_locations = [];
                      thrown_at_source = true;
                    })
        in
        let add_final_parameter_annotation_error ~errors =
          emit_error ~errors ~location ~kind:(Error.InvalidType (FinalParameter name))
        in
        let add_variance_error errors annotation =
          match annotation with
          | Type.Variable variable
            when (not (Define.is_constructor define)) && Type.Variable.Unary.is_covariant variable
            ->
              emit_error
                ~errors
                ~location
                ~kind:(Error.InvalidTypeVariance { annotation; origin = Error.Parameter })
          | _ -> errors
        in
        let parse_as_unary () =
          let errors, annotation =
            match index, parent with
            | 0, Some parent
            (* __new__ does not require an annotation for __cls__, even though it is a static
                method. *)
              when not
                      (Define.is_class_toplevel define
                      || Define.is_static_method define
                        && not (String.equal (Define.unqualified_name define) "__new__")) -> (
                let resolved, is_class_method =
                  let parent_annotation = type_of_parent ~global_resolution parent in
                  if Define.is_class_method define || Define.is_class_property define then
                    (* First parameter of a method is a class object. *)
                    Type.meta parent_annotation, true
                  else (* First parameter of a method is the callee object. *)
                    parent_annotation, false
                in
                match annotation with
                | Some annotation ->
                    let errors, annotation =
                      let annotation_errors, annotation =
                        parse_and_check_annotation ~resolution ~bind_variables:false annotation
                      in
                      List.append annotation_errors errors, annotation
                    in
                    let enforce_here =
                      let is_literal_classmethod decorator =
                        match Decorator.from_expression decorator with
                        | None -> false
                        | Some { Decorator.name = { Node.value = name; _ }; _ } -> (
                            match Reference.as_list name with
                            | ["classmethod"] -> true
                            | _ -> false)
                      in
                      match List.rev decorators with
                      | [] -> true
                      | last :: _ when is_literal_classmethod last -> true
                      | _ :: _ -> false
                    in
                    let errors =
                      if enforce_here then
                        let name = Identifier.sanitized name in
                        let kind =
                          let compatible =
                            GlobalResolution.constraints_solution_exists
                              global_resolution
                              ~left:resolved
                              ~right:annotation
                          in
                          if compatible then
                            None
                          else if
                            (is_class_method && String.equal name "cls")
                            || ((not is_class_method) && String.equal name "self")
                          then
                            (* Assume the user incorrectly tried to type the implicit parameter *)
                            Some
                              (Error.InvalidMethodSignature { annotation = Some annotation; name })
                          else (* Assume the user forgot to specify the implicit parameter *)
                            Some
                              (Error.InvalidMethodSignature
                                  {
                                    annotation = None;
                                    name = (if is_class_method then "cls" else "self");
                                  })
                        in
                        match kind with
                        | Some kind -> emit_error ~errors ~location ~kind
                        | None -> errors
                      else
                        errors
                    in
                    errors, Annotation.create_mutable annotation
                | None -> errors, Annotation.create_mutable resolved)
            | _ -> (
              
                let errors, parsed_annotation =
                  match annotation with
                  | None -> errors, None
                  | Some annotation ->
                      let anntation_errors, annotation =
                        parse_and_check_annotation ~resolution ~bind_variables:false annotation
                      in
                      let errors = List.append anntation_errors errors in
                      let errors = add_variance_error errors annotation in
                      errors, Some annotation
                in
                let contains_prohibited_any parsed_annotation =
                  let contains_literal_any =
                    annotation >>| Type.expression_contains_any |> Option.value ~default:false
                  in
                  contains_literal_any && Type.contains_prohibited_any parsed_annotation
                in
                let value_annotation =
                  value
                  >>| (fun expression -> forward_expression ~resolution ~at_resolution:None expression)
                  >>| fun { resolved; _ } -> resolved
                in
                let errors =
                  match parsed_annotation, value_annotation with
                  | Some annotation, Some value_annotation ->
                      add_incompatible_variable_error ~errors annotation value_annotation
                  | _ -> errors
                in
                match parsed_annotation, value_annotation with
                | Some annotation, Some _ when Type.contains_final annotation ->
                    ( add_final_parameter_annotation_error ~errors,
                      Annotation.create_mutable annotation )
                | Some annotation, Some value_annotation when contains_prohibited_any annotation ->
                    ( add_missing_parameter_annotation_error
                        ~errors
                        ~given_annotation:(Some annotation)
                        (Some value_annotation),
                      Annotation.create_mutable annotation )
                | Some annotation, _ when Type.contains_final annotation ->
                    ( add_final_parameter_annotation_error ~errors,
                      Annotation.create_mutable annotation )
                | Some annotation, None when contains_prohibited_any annotation ->
                    ( add_missing_parameter_annotation_error
                        ~errors
                        ~given_annotation:(Some annotation)
                        None,
                      Annotation.create_mutable annotation )
                | Some annotation, _ ->
                    let errors =
                      emit_invalid_enumeration_literal_errors
                        ~resolution
                        ~at_resolution: None
                        ~location
                        ~errors
                        annotation
                    in
                    errors, Annotation.create_mutable annotation
                | None, Some value_annotation ->
                    ( add_missing_parameter_annotation_error
                        ~errors
                        ~given_annotation:None
                        (Some value_annotation),
                      Annotation.create_mutable Type.Unknown )
                | None, None ->
                    ( add_missing_parameter_annotation_error ~errors ~given_annotation:None None,
                      Annotation.create_mutable Type.Unknown ))
          in
          let apply_starred_annotations annotation =
            if String.is_prefix ~prefix:"**" name then
              Type.dictionary ~key:Type.string ~value:annotation
            else if String.is_prefix ~prefix:"*" name then
              Type.Tuple (Type.OrderedTypes.create_unbounded_concatenation annotation)
            else
              annotation
          in
          let transform type_ =
            Type.Variable.mark_all_variables_as_bound type_ |> apply_starred_annotations
          in
          errors, Annotation.transform_types ~f:transform annotation
        in
        let errors, annotation =
          if String.is_prefix ~prefix:"*" name && not (String.is_prefix ~prefix:"**" name) then
            annotation
            >>= Type.OrderedTypes.concatenation_from_unpack_expression
                  ~parse_annotation:(GlobalResolution.parse_annotation global_resolution)
            >>| (fun concatenation ->
                  Type.Tuple (Concatenation concatenation)
                  |> Type.Variable.mark_all_variables_as_bound
                  |> Annotation.create_mutable
                  |> fun annotation -> errors, annotation)
            |> Option.value ~default:(parse_as_unary ())
          else
            parse_as_unary ()
        in
        
        ( Resolution.new_local ~reference:(make_parameter_name name) ~annotation new_resolution,
          errors )
      in
      let number_of_stars name = Identifier.split_star name |> fst |> String.length in
      match List.rev parameters, parent with
      | [], Some _ when not (Define.is_class_toplevel define || Define.is_static_method define) ->
          let errors =
            let name =
              if Define.is_class_method define || Define.is_class_property define then
                "cls"
              else
                "self"
            in
            emit_error
              ~errors
              ~location
              ~kind:(Error.InvalidMethodSignature { annotation = None; name })
          in
          resolution, errors
      | ( {
            Node.value = { name = second_name; value = None; annotation = Some second_annotation };
            _;
          }
          :: {
                Node.value = { name = first_name; value = None; annotation = Some first_annotation };
                _;
              }
              :: reversed_head,
          _ )
        when number_of_stars first_name = 1 && number_of_stars second_name = 2 -> (
          match
            GlobalResolution.parse_as_parameter_specification_instance_annotation
              global_resolution
              ~variable_parameter_annotation:first_annotation
              ~keywords_parameter_annotation:second_annotation
          with
          | Some variable ->
              let add_annotations_to_resolution
                  {
                    Type.Variable.Variadic.Parameters.Components.positional_component;
                    keyword_component;
                  }
                =
                resolution
                |> Resolution.new_local
                      ~reference:(make_parameter_name first_name)
                      ~annotation:(Annotation.create_mutable positional_component)
                |> Resolution.new_local
                      ~reference:(make_parameter_name second_name)
                      ~annotation:(Annotation.create_mutable keyword_component)
              in
              if Resolution.type_variable_exists resolution ~variable:(ParameterVariadic variable)
              then
                let new_resolution =
                  Type.Variable.Variadic.Parameters.mark_as_bound variable
                  |> Type.Variable.Variadic.Parameters.decompose
                  |> add_annotations_to_resolution
                in
                List.rev reversed_head
                |> List.foldi ~init:(new_resolution, errors) ~f:check_parameter
              else
                let errors =
                  let origin =
                    if Define.is_toplevel (Node.value Context.define) then
                      Error.Toplevel
                    else if Define.is_class_toplevel (Node.value Context.define) then
                      Error.ClassToplevel
                    else
                      Error.Define
                  in
                  emit_error
                    ~errors
                    ~location
                    ~kind:
                      (Error.InvalidTypeVariable { annotation = ParameterVariadic variable; origin })
                in
                ( add_annotations_to_resolution
                    { positional_component = Top; keyword_component = Top },
                  errors )
          | None -> List.foldi ~init:(resolution, errors) ~f:check_parameter parameters)
      | _ -> List.foldi ~init:(resolution, errors) ~f:check_parameter parameters
    in
    let check_base_annotations resolution errors =
      let current_class_name = parent >>| Reference.show in
      let is_current_class_typed_dictionary =
        current_class_name
        >>| (fun class_name ->
              GlobalResolution.is_typed_dictionary
                ~resolution:global_resolution
                (Primitive class_name))
        |> Option.value ~default:false
      in
      if Define.is_class_toplevel define then
        let open Annotated in
        let check_base old_errors base =
          let annotation_errors, parsed = parse_and_check_annotation ~resolution base in
          let errors = List.append annotation_errors old_errors in
          
          match parsed with
          | Type.Parametric { name = "type"; parameters = [Single Type.Unknown] } ->
              (* Inheriting from type makes you a metaclass, and we don't want to
                * suggest that instead you need to use typing.Type[Something] *)
              old_errors
          | Primitive base_name ->
              if
                is_current_class_typed_dictionary
                && not
                      (GlobalResolution.is_typed_dictionary
                        ~resolution:global_resolution
                        (Primitive base_name)
                      || Type.TypedDictionary.is_builtin_typed_dictionary_class base_name)
              then
                emit_error
                  ~errors
                  ~location:(Node.location base)
                  ~kind:
                    (InvalidInheritance
                        (UninheritableType
                          { annotation = parsed; is_parent_class_typed_dictionary = true }))
              else
                errors
          | Top
          (* There's some other problem we already errored on *)
          | Parametric _
          | Tuple _ ->
              errors
          | Any when GlobalResolution.base_is_from_placeholder_stub global_resolution base -> errors
          | annotation ->
              emit_error
                ~errors
                ~location:(Node.location base)
                ~kind:
                  (InvalidInheritance
                      (UninheritableType { annotation; is_parent_class_typed_dictionary = false }))
        in
        let bases =
          Node.create define ~location
          |> Define.create
          |> Define.parent_definition ~resolution:global_resolution
          >>| Node.value
          >>| ClassSummary.base_classes
          |> Option.value ~default:[]
        in
        let errors = List.fold ~init:errors ~f:check_base bases in
        if is_current_class_typed_dictionary then
          let open Type.Record.TypedDictionary in
          let superclass_pairs_with_same_field_name =
            let field_name_to_successor_fields_map =
              let get_typed_dictionary_fields class_name =
                GlobalResolution.get_typed_dictionary
                  ~resolution:global_resolution
                  (Type.Primitive class_name)
                >>| (fun { fields; _ } -> fields)
                |> Option.value ~default:[]
              in
              let get_successor_map_entries successor_name =
                get_typed_dictionary_fields successor_name
                |> List.map ~f:(fun ({ name; annotation = _; _ } as field) ->
                        name, (successor_name, field))
              in
              let base_classes =
                current_class_name
                >>| GlobalResolution.immediate_parents ~resolution:global_resolution
                |> Option.value ~default:[]
              in
              List.concat_map base_classes ~f:get_successor_map_entries
              |> Map.of_alist_multi (module String)
            in
            let all_pairs items =
              List.cartesian_product items items
              |> List.filter ~f:(fun ((class_name1, _), (class_name2, _)) ->
                      String.compare class_name1 class_name2 < 0)
            in
            Map.data field_name_to_successor_fields_map |> List.concat_map ~f:all_pairs
          in
          let emit_requiredness_error
              errors
              ((class_name1, { name; required = required1; _ }), (class_name2, _))
            =
            let mismatch =
              if required1 then
                Error.RequirednessMismatch
                  {
                    required_field_class = class_name1;
                    non_required_field_class = class_name2;
                    field_name = name;
                  }
              else
                Error.RequirednessMismatch
                  {
                    required_field_class = class_name2;
                    non_required_field_class = class_name1;
                    field_name = name;
                  }
            in
            emit_error
              ~errors
              ~location
              ~kind:(InvalidInheritance (TypedDictionarySuperclassCollision mismatch))
          in
          let emit_type_mismatch_error
              errors
              ( (class_name1, { name = field_name; annotation = annotation1; _ }),
                (class_name2, { annotation = annotation2; _ }) )
            =
            emit_error
              ~errors
              ~location
              ~kind:
                (InvalidInheritance
                    (TypedDictionarySuperclassCollision
                      (Error.TypeMismatch
                          {
                            field_name;
                            annotation_and_parent1 =
                              { annotation = annotation1; parent = class_name1 };
                            annotation_and_parent2 =
                              { annotation = annotation2; parent = class_name2 };
                          })))
          in
          let errors =
            List.filter superclass_pairs_with_same_field_name ~f:(fun ((_, field1), (_, field2)) ->
                Type.TypedDictionary.same_name_different_requiredness field1 field2)
            |> List.fold ~init:errors ~f:emit_requiredness_error
          in
          let errors =
            List.filter superclass_pairs_with_same_field_name ~f:(fun ((_, field1), (_, field2)) ->
                Type.TypedDictionary.same_name_different_annotation field1 field2)
            |> List.fold ~init:errors ~f:emit_type_mismatch_error
          in
          errors
        else
          errors
      else
        errors
    in
    let check_init_subclass_call resolution errors =
      let init_subclass_arguments =
        Node.create define ~location
        |> Annotated.Define.create
        |> Annotated.Define.parent_definition ~resolution:global_resolution
        >>| Node.value
        >>| (fun { ClassSummary.bases = { init_subclass_arguments; _ }; _ } ->
              init_subclass_arguments)
        |> Option.value ~default:[]
      in
      let init_subclass_parent =
        let find_init_subclass parent_class =
          GlobalResolution.attribute_from_class_name
            ~resolution:global_resolution
            ~transitive:false
            ~accessed_through_class:true
            ~name:"__init_subclass__"
            ~instantiated:(Type.Primitive parent_class)
            parent_class
          >>= fun attribute ->
          Option.some_if
            (AnnotatedAttribute.defined attribute
            && String.equal (AnnotatedAttribute.parent attribute) parent_class)
            attribute
          >>| AnnotatedAttribute.parent
        in
        parent
        >>| Reference.show
        >>| GlobalResolution.successors ~resolution:global_resolution
        >>= List.find_map ~f:find_init_subclass
      in
      match init_subclass_parent with
      | Some parent ->
          let implicit_call =
            Expression.Call
              {
                callee =
                  {
                    Node.location;
                    value =
                      Name
                        (Name.Attribute
                            {
                              base =
                                Expression.Name (create_name ~location parent)
                                |> Node.create ~location;
                              attribute = "__init_subclass__";
                              special = false;
                            });
                  };
                arguments = init_subclass_arguments;
              }
            |> Node.create ~location
          in
          let { Resolved.errors = init_subclass_errors; _ } =
            forward_expression ~resolution ~at_resolution:None implicit_call
          in
          init_subclass_errors @ errors
      | None -> errors
    in
    let check_behavioral_subtyping resolution errors =
      let is_allowlisted_dunder_method define =
        let allowlist =
          String.Set.of_list
            [
              "__call__";
              "__delattr__";
              "__delitem__";
              "__eq__";
              "__getitem__";
              "__ne__";
              "__setattr__";
              "__setitem__";
              "__sizeof__";
            ]
        in
        String.Set.mem allowlist (Define.unqualified_name define)
      in
      try
        if
          Define.is_constructor define
          || Define.is_overloaded_function define
          || is_allowlisted_dunder_method define
        then
          errors
        else
          let open Annotated in
          begin
            match define with
            | { Ast.Statement.Define.signature = { parent = Some parent; _ }; _ } -> (
                GlobalResolution.overrides
                  (Reference.show parent)
                  ~resolution:global_resolution
                  ~name:(StatementDefine.unqualified_name define)
                >>| fun overridden_attribute ->
                let errors =
                  match AnnotatedAttribute.visibility overridden_attribute with
                  | ReadOnly (Refinable { overridable = false }) ->
                      let parent = overridden_attribute |> Attribute.parent in
                      emit_error
                        ~errors
                        ~location
                        ~kind:(Error.InvalidOverride { parent; decorator = Final })
                  | _ -> errors
                in
                let errors =
                  if
                    not
                      (Bool.equal
                          (Attribute.static overridden_attribute)
                          (StatementDefine.is_static_method define))
                  then
                    let parent = overridden_attribute |> Attribute.parent in
                    let decorator =
                      if Attribute.static overridden_attribute then
                        Error.StaticSuper
                      else
                        Error.StaticOverride
                    in
                    emit_error ~errors ~location ~kind:(Error.InvalidOverride { parent; decorator })
                  else
                    errors
                in
                (* Check strengthening of postcondition. *)
                let overridden_base_attribute_annotation =
                  Annotation.annotation (Attribute.annotation overridden_attribute)
                in
                match overridden_base_attribute_annotation with
                | Type.Parametric
                    {
                      name = "BoundMethod";
                      parameters = [Single (Type.Callable { implementation; _ }); _];
                    }
                | Type.Callable { Type.Callable.implementation; _ } ->
                    let original_implementation =
                      resolve_reference_type ~resolution ~at_resolution:None name
                      |> function
                      | Type.Callable { Type.Callable.implementation = original_implementation; _ }
                      | Type.Parametric
                          {
                            parameters =
                              [
                                Single
                                  (Type.Callable { implementation = original_implementation; _ });
                                _;
                              ];
                            _;
                          } ->
                          original_implementation
                      | annotation -> raise (ClassHierarchy.Untracked (Type.show annotation))
                    in
                    let errors =
                      let expected = Type.Callable.Overload.return_annotation implementation in
                      let actual =
                        Type.Callable.Overload.return_annotation original_implementation
                      in
                      if
                        Type.Variable.all_variables_are_resolved expected
                        && not
                              (GlobalResolution.less_or_equal
                                global_resolution
                                ~left:actual
                                ~right:expected)
                      then
                        emit_error
                          ~errors
                          ~location
                          ~kind:
                            (Error.InconsistentOverride
                                {
                                  overridden_method = StatementDefine.unqualified_name define;
                                  parent = Attribute.parent overridden_attribute |> Reference.create;
                                  override_kind = Method;
                                  override =
                                    Error.WeakenedPostcondition
                                      (Error.create_mismatch
                                        ~resolution:global_resolution
                                        ~actual
                                        ~expected
                                        ~covariant:false);
                                })
                      else
                        errors
                    in
                    (* Check weakening of precondition. *)
                    let overriding_parameters =
                      let parameter_annotations
                          { StatementDefine.signature = { parameters; _ }; _ }
                          ~resolution
                        =
                        let element { Node.value = { Parameter.name; annotation; _ }; _ } =
                          let annotation =
                            annotation
                            >>| (fun annotation ->
                                  GlobalResolution.parse_annotation resolution annotation)
                            |> Option.value ~default:Type.Unknown
                          in
                          name, annotation
                        in
                        List.map parameters ~f:element
                      in
                      parameter_annotations define ~resolution:global_resolution
                      |> List.map ~f:(fun (name, annotation) ->
                              { Type.Callable.Parameter.name; annotation; default = false })
                      |> Type.Callable.Parameter.create
                    in
                    let validate_match ~errors ~overridden_parameter ~expected = function
                      | Some actual -> (
                          let is_compatible =
                            let expected = Type.Variable.mark_all_variables_as_bound expected in
                            GlobalResolution.constraints_solution_exists
                              global_resolution
                              ~left:expected
                              ~right:actual
                          in
                          try
                            if (not (Type.is_top expected)) && not is_compatible then
                              emit_error
                                ~errors
                                ~location
                                ~kind:
                                  (Error.InconsistentOverride
                                      {
                                        overridden_method = StatementDefine.unqualified_name define;
                                        parent =
                                          Attribute.parent overridden_attribute |> Reference.create;
                                        override_kind = Method;
                                        override =
                                          Error.StrengthenedPrecondition
                                            (Error.Found
                                              (Error.create_mismatch
                                                  ~resolution:global_resolution
                                                  ~actual
                                                  ~expected
                                                  ~covariant:false));
                                      })
                            else
                              errors
                          with
                          | ClassHierarchy.Untracked _ ->
                              (* TODO(T27409168): Error here. *)
                              errors)
                      | None ->
                          let has_keyword_and_anonymous_starred_parameters =
                            List.exists overriding_parameters ~f:(function
                                | Keywords _ -> true
                                | _ -> false)
                            && List.exists overriding_parameters ~f:(function
                                    | Variable _ -> true
                                    | _ -> false)
                          in
                          if has_keyword_and_anonymous_starred_parameters then
                            errors
                          else
                            emit_error
                              ~errors
                              ~location
                              ~kind:
                                (Error.InconsistentOverride
                                    {
                                      overridden_method = StatementDefine.unqualified_name define;
                                      override_kind = Method;
                                      parent =
                                        Attribute.parent overridden_attribute |> Reference.create;
                                      override =
                                        Error.StrengthenedPrecondition
                                          (Error.NotFound overridden_parameter);
                                    })
                    in
                    let check_parameter errors = function
                      | `Both (overridden_parameter, overriding_parameter) -> (
                          match
                            ( Type.Callable.RecordParameter.annotation overridden_parameter,
                              Type.Callable.RecordParameter.annotation overriding_parameter )
                          with
                          | Some expected, Some actual ->
                              validate_match ~errors ~overridden_parameter ~expected (Some actual)
                          | None, _
                          | _, None ->
                              (* TODO(T53997072): There is no reasonable way to compare Variable
                                  (Concatenation _). For now, let's just ignore this. *)
                              errors)
                      | `Left overridden_parameter -> (
                          match Type.Callable.RecordParameter.annotation overridden_parameter with
                          | Some expected ->
                              validate_match ~errors ~overridden_parameter ~expected None
                          | None -> errors)
                      | `Right _ -> errors
                    in
                    let overridden_parameters =
                      Type.Callable.Overload.parameters implementation |> Option.value ~default:[]
                    in
                    Type.Callable.Parameter.zip overridden_parameters overriding_parameters
                    |> List.fold ~init:errors ~f:check_parameter
                | _ -> errors)
            | _ -> None
          end
          |> Option.value ~default:errors
      with
      | ClassHierarchy.Untracked _ -> errors
    in
    let check_constructor_return errors =
      if not (Define.is_constructor define) then
        errors
      else
        match return_annotation with
        | Some ({ Node.location; _ } as annotation) -> (
            match define with
            | { Define.signature = { Define.Signature.name; _ }; _ }
              when String.equal (Reference.last name) "__new__" ->
                (* TODO(T45018328): Error here. `__new__` is a special undecorated static method,
                    and we really ought to be checking its return type against typing.Type[Cls]. *)
                errors
            | _ ->
                let annotation = GlobalResolution.parse_annotation global_resolution annotation in
                if Type.is_none annotation then
                  errors
                else
                  emit_error
                    ~errors
                    ~location
                    ~kind:(Error.IncompatibleConstructorAnnotation annotation))
        | _ -> errors
    in
(* 
    let preresolution = resolution in *)
    let resolution, errors =
      let resolution = Resolution.with_parent resolution ~parent in

      let resolution, errors = add_capture_annotations resolution [] in

      (* Log.dump "111 %a" Resolution.pp resolution; *)

      let resolution, errors = check_parameter_annotations resolution errors in

      (* Log.dump "222 %a" Resolution.pp resolution; *)

(*       let resolution = Resolution.meet_refinements preresolution resolution in *)

      
      let errors =
        check_unbound_names errors
        |> check_return_annotation resolution
        |> check_decorators resolution
        |> check_base_annotations resolution
        |> check_init_subclass_call resolution
        |> check_behavioral_subtyping resolution
        |> check_constructor_return
      in
      resolution, errors
    in
    let state =
      let postcondition = Resolution.annotation_store resolution in
      let statement_key = [%hash: int * int] (Cfg.entry_index, 0) in
      let (_ : unit option) =
        Context.resolution_fixpoint >>| LocalAnnotationMap.set ~statement_key ~postcondition
      in
      let (_ : unit option) = Context.error_map >>| LocalErrorMap.set ~statement_key ~errors in
      Value resolution
    in
    state

  let forward_statement_first ~resolution ~at_resolution ~statement =
    let resolved_expression ~resolution expression =
      forward_expression ~resolution ~at_resolution expression
      |> fun { Resolved.resolved; resolved_annotation; resolution = new_resolution; _ } ->
        ( new_resolution,
          resolved_annotation |> Option.value ~default:(Annotation.create_mutable resolved) )
    in

    let update_resolution_of_error ~resolution errors =
      Error.get_expression_type errors
      |> List.fold ~init:resolution ~f:(fun resolution (exp, typ, _, _) -> 
        match Node.value exp with
        | Expression.Name name ->
          (match name_to_reference name with
          | Some reference ->
            let resolved_type = Resolution.resolve_reference resolution reference in
            let new_type =
              (match resolved_type with
              | Type.Union t_list ->
                Type.Union (List.filter t_list ~f:(fun t -> not (Type.equal t typ)))
              | t when Type.equal t typ -> Type.Unknown
              | _ -> resolved_type
              )
            in
            (* Log.dump "Origin : %a" Type.pp typ;
            Log.dump "Update %a : \n%a \n=> \n%a" Reference.pp reference Type.pp resolved_type Type.pp new_type; *)
            Resolution.refine_local resolution ~reference ~annotation:(Annotation.create_mutable new_type)
          | _ -> resolution
          )
        | _ -> resolution
      )
    in

    let _ = update_resolution_of_error in

    let resolve_statement ~resolution statement =
      forward_statement ~resolution ~at_resolution ~statement
      |> fun ((resolution, errors)) ->
      let interesting_errors = Error.filter_interesting_error errors in

      
      match resolution with
      | Value _ when List.length interesting_errors > 0 
        && not ((OurDomain.is_error_mode (OurDomain.load_mode ())) || OurDomain.is_recheck_mode (OurDomain.load_mode ())) (* && false *) -> 
        Resolution.Unreachable
        (* let resolution = update_resolution_of_error ~resolution errors in
        Resolution.Reachable { resolution; errors } *)
      | Unreachable -> Resolution.Unreachable
      | Value resolution -> 
        (* let resolution = update_resolution_of_error ~resolution errors in *)
        Resolution.Reachable { resolution; errors }
    in

    let resolution = 
      Resolution.set_resolve_expression resolution resolved_expression
    in
    let resolution = 
      Resolution.set_resolve_statement resolution resolve_statement
    in

    forward_statement ~resolution ~at_resolution ~statement
    |> fun ((resolution, errors)) ->
    (* Log.dump "WHY??";
    List.iter errors ~f:(fun e -> Log.dump "%a" Error.pp e); *)
    let interesting_errors = Error.filter_interesting_error errors in
    
    (* let { StatementDefine.Signature.name=define_name; _ } = define_signature in
    if String.is_substring (Reference.show define_name) ~substring:"luigi.contrib.redshift"
      then (
      Log.dump "INTERESTING : %a\n%i!!" Statement.pp statement (List.length interesting_errors);
      List.iter interesting_errors ~f:(fun e -> Log.dump "HO : %a" Error.pp e);
      ); *)
    (* if List.length errors > 0 then (
      Log.dump "INTERESTING : %a\n%i!!" Statement.pp statement (List.length interesting_errors);
      List.iter errors ~f:(fun e -> Log.dump "HO : %a" Error.pp e);
    ); *)
    match resolution with
    | Value _ when List.length interesting_errors > 0 
      && not (OurDomain.is_error_mode (OurDomain.load_mode ()) || OurDomain.is_recheck_mode (OurDomain.load_mode ())) (* && false *) -> 
      Unreachable, errors
      (* let resolution = update_resolution_of_error ~resolution errors in
      Value resolution, errors *)
    | Unreachable -> Unreachable, errors
    | Value resolution -> 
      (* let resolution = update_resolution_of_error ~resolution errors in *)
      Value resolution, errors
(*     if List.length errors > 0 && not (OurDomain.is_error_mode (OurDomain.load_mode ()))
    then Unreachable, errors
    else (
      let resolution = update_resolution_of_error ~resolution errors in
      resolution, errors  *)
    

    (* let resolve_statement ~resolution statement =
      forward_statement ~resolution ~at_resolution ~statement
      |> fun ((resolution, errors)) ->
      let errors = Error.filter_interesting_error errors in
      match resolution with
      | Unreachable -> Resolution.Unreachable
      | Value resolution -> Resolution.Reachable { resolution; errors }
    in

    let resolution = 
      Resolution.set_resolve_expression resolution resolved_expression
    in
    let resolution = 
      Resolution.set_resolve_statement resolution resolve_statement
    in

    forward_statement ~resolution ~at_resolution ~statement *)


  let forward ~statement_key:_ ~context:_ state ~statement:_ = state

  let backward ~statement_key:_ state ~statement:_ = state
end
