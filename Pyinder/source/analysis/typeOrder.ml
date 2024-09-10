(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Core
open Ast
open Pyre
open Assumptions

type class_hierarchy = ConstraintsSet.class_hierarchy

type order = ConstraintsSet.order

module type FullOrderTypeWithoutT = sig
  val always_less_or_equal : order -> left:Type.t -> right:Type.t -> bool

  val meet : order -> Type.t -> Type.t -> Type.t

  val join : order -> Type.t -> Type.t -> Type.t
end

module type FullOrderType = sig
  type t = order

  include FullOrderTypeWithoutT
end

module type OrderedConstraintsType = TypeConstraints.OrderedConstraintsType with type order = order

module OrderImplementation = struct
  module Make (OrderedConstraintsSet : ConstraintsSet.OrderedConstraintsSetType) = struct
    type t = order

    let rec always_less_or_equal order ~left ~right =
      let x = 
      OrderedConstraintsSet.add
        ConstraintsSet.empty
        ~new_constraint:
          (LessOrEqual
             {
               left = Type.Variable.mark_all_variables_as_bound left;
               right = Type.Variable.mark_all_variables_as_bound right;
             })
        ~order
      (* This potential is not just potential in this case, since this will always be accurate when
         there are no free type variables, as in this case *)
      in 
      x |> ConstraintsSet.potentially_satisfiable 


    and join_implementations ~parameter_join ~return_join order left right =
      let open Callable in
      let parameters =
        match left.parameters, right.parameters with
        | Undefined, Undefined -> Some Undefined
        | Defined left, Defined right -> (
            try
              let join_parameter sofar left right =
                match sofar with
                | Some sofar ->
                    let joined =
                      if Type.Callable.Parameter.names_compatible left right then
                        match left, right with
                        | Parameter.PositionalOnly left, Parameter.PositionalOnly right
                          when Bool.equal left.default right.default ->
                            Some
                              (Parameter.PositionalOnly
                                 {
                                   left with
                                   annotation =
                                     parameter_join order left.annotation right.annotation;
                                 })
                        | Parameter.PositionalOnly anonymous, Parameter.Named named
                        | Parameter.Named named, Parameter.PositionalOnly anonymous
                          when Bool.equal named.default anonymous.default ->
                            Some
                              (Parameter.PositionalOnly
                                 {
                                   anonymous with
                                   annotation =
                                     parameter_join order named.annotation anonymous.annotation;
                                 })
                        | Parameter.Named left, Parameter.Named right
                          when Bool.equal left.default right.default ->
                            Some
                              (Parameter.Named
                                 {
                                   left with
                                   annotation =
                                     parameter_join order left.annotation right.annotation;
                                 })
                        | Parameter.Variable (Concrete left), Parameter.Variable (Concrete right) ->
                            Some (Parameter.Variable (Concrete (parameter_join order left right)))
                        | Parameter.Keywords left, Parameter.Keywords right ->
                            Some (Parameter.Keywords (parameter_join order left right))
                        | _ -> None
                      else
                        None
                    in
                    joined >>| fun joined -> joined :: sofar
                | None -> None
              in
              List.fold2_exn ~init:(Some []) ~f:join_parameter left right
              >>| List.rev
              >>| fun parameters -> Defined parameters
            with
            | _ -> None)
        | Undefined, Defined right -> Some (Defined right)
        | Defined left, Undefined -> Some (Defined left)
        | _ -> None
      in
      parameters
      >>| fun parameters ->
      { annotation = return_join order left.annotation right.annotation; parameters }


    and join
        ({
           ConstraintsSet.class_hierarchy =
             { least_upper_bound; instantiate_successors_parameters; variables; _ };
           is_protocol;
           assumptions = { protocol_assumptions; _ };
           _;
         } as order)
        left
        right
      =
      let on_any = !OurDomain.on_any in

      (* let origin_left, origin_right = left, right in *)
      let left, right =
        if not on_any
        then (
          (if Type.can_unknown left then Type.Any else left),
          (if Type.can_unknown right then Type.Any else right)
        )
        else left, right
      in
      (* let timer = Timer.start () in *)
      let left, right =
        Type.narrow_union ~join:(join order) ~less_or_equal:(always_less_or_equal order) left,
        Type.narrow_union ~join:(join order) ~less_or_equal:(always_less_or_equal order) right
      in

      (* Log.dump "LEFT %a RIGHT %a" Type.pp left Type.pp right; *)
      (* let tt0 = Timer.stop_in_sec timer in *)

      let union = Type.union_join left right in
      (* let tt1 = Timer.stop_in_sec timer in
      let total_time = Timer.stop_in_sec timer in
      if Float.(>.) total_time 0.01 then (
        Log.dump "JOINDA %.5f %.5f" tt0 tt1;
        Log.dump "LEFT %a RIGHT %a" Type.pp left Type.pp right;
      );   *)
      

      let x =
      if Type.equal left right then
        left
      (*else if
        Type.Variable.contains_escaped_free_variable left
        || Type.Variable.contains_escaped_free_variable right
      then
        union
      *)
      else
        match left, right with
        | Type.Unknown, _
        | _, Type.Unknown ->
          if on_any
          then union
          else Type.Any 
        | Type.Bottom, other
        | other, Type.Bottom ->
            other
        | Type.Top, _
        | _, Type.Top ->
            Type.Top
        | Type.Any, _
        | _, Type.Any ->
            Type.Any
        | Type.OurTypedDictionary { general=left_general; typed_dict=left_typed_dict; }, 
        Type.OurTypedDictionary { general=right_general; typed_dict=right_typed_dict; } ->
          let x = Type.OurTypedDictionary {
            general=join order left_general right_general;
            typed_dict=Type.OurTypedDictionary.join ~join:(join order) left_typed_dict right_typed_dict;
          }
          in
          (*
          Log.dump "Left : %a \n Right : %a \n Result : %a" Type.pp left Type.pp right Type.pp x;
          *)
          x
          (*
          union
          *)
          (*
          (*
          Log.dump "Left : %a \n Right : %a \n Result : %a" Type.pp left Type.pp right Type.pp x;
          *)
          x
          *)

        | Type.ParameterVariadicComponent _, _
        | _, Type.ParameterVariadicComponent _ ->
            union
        | Type.NoneType, _
        | _, Type.NoneType ->
            union
        | Type.Annotated left, _ -> Type.annotated (join order left right)
        | _, Type.Annotated right -> Type.annotated (join order left right)
        | Type.RecursiveType left_recursive_type, Type.RecursiveType right_recursive_type ->
            let new_name = Type.RecursiveType.Namespace.create_fresh_name () in
            (* Based on https://cstheory.stackexchange.com/a/38415. *)
            Type.RecursiveType.create
              ~name:new_name
              ~body:
                (join
                   order
                   (Type.RecursiveType.body_with_replaced_name ~new_name left_recursive_type)
                   (Type.RecursiveType.body_with_replaced_name ~new_name right_recursive_type))
        | Type.RecursiveType _, _
        | _, Type.RecursiveType _ ->
            if always_less_or_equal order ~left ~right then
              right
            else if always_less_or_equal order ~left:right ~right:left then
              left
            else
              Type.union [left; right]
        (* n: A_n = B_n -> Union[A_i] <= Union[B_i]. *)
        
        | Type.Union left, Type.Union right -> 
          Type.Union (left@right)
          |> Type.narrow_union ~join:(join order) ~less_or_equal:(always_less_or_equal order)
        
        
        
        (* | Type.Union _, Type.Union right ->

            List.fold right ~init:left ~f:(fun acc right_t ->
              join order acc right_t
            ) *)
       
        | (Type.Union elements as union), other
        | other, (Type.Union elements as union) ->
          
          (* if List.length elements > 15 then (
            Log.dump "<<< Join Heavy Type : %i >>>" (List.length elements);
            
            let _ = List.fold elements ~init:Type.Bottom ~f:(fun acc t -> 
              Log.dump "[[[ Cand : %b ]]]\n%a\n" (always_less_or_equal order ~left:acc ~right:t) Type.pp t;
              t
            ) in
            Log.dump "[[[ With ]]]\n%a\n" Type.pp other;
            
          );  *)
          
          
            if always_less_or_equal order ~left:other ~right:(Type.filter_unknown union) 
              && not (Type.contains_any other)(*  && not (Type.can_unknown other) && not (Type.can_unknown union) *)
            then (
              union
            )
            else
              let rec flat_join elements new_element =
                match elements with
                | [] -> [new_element]
                | [head] -> (
                    match join order head new_element with
                    | Type.Union _ -> [head; new_element]
                    | joined -> [joined])
                | head :: tail -> (
                    match join order head new_element with
                    | Type.Union _ -> head :: flat_join tail new_element
                    | joined -> joined :: tail)
              in
              let x = Type.union (List.fold ~f:flat_join ~init:[] (other :: elements)) in
              x
        | Type.OurTypedDictionary { general; typed_dict }, other ->

          let _ = general, typed_dict, other in
          let new_general = join order general other in
          if Type.is_dictionary_or_mapping new_general then
            OurTypedDictionary { general=new_general; typed_dict=Type.OurTypedDictionary.add_bottom_in_fields typed_dict; }
          else  
            new_general
        | other, Type.OurTypedDictionary { general; typed_dict } ->
          let _ = general, typed_dict, other in
          let new_general = join order other general in
          if Type.is_dictionary_or_mapping new_general then
            OurTypedDictionary { general=new_general; typed_dict=Type.OurTypedDictionary.add_bottom_in_fields typed_dict; }
          else  
            new_general
        | Type.IntExpression (Data polynomial), other when Type.Polynomial.is_base_case polynomial
          ->
            join order other (Type.polynomial_to_type polynomial)
        | other, Type.IntExpression (Data polynomial) when Type.Polynomial.is_base_case polynomial
          ->
            join order other (Type.polynomial_to_type polynomial)
        | Type.IntExpression _, other
        | other, Type.IntExpression _ ->
            join order other (Type.Primitive "int")
        | _, Type.Variable _
        | Type.Variable _, _ ->
            union
          
        | ( Type.Parametric { name = left_primitive; parameters = [Single left_key; Single left_value] },
            Type.Parametric { name = right_primitive; parameters = [Single right_key; Single right_value] } )
            when 
            (String.equal left_primitive "dict") && 
            (String.equal right_primitive "dict")
            ->
              (* It is not sound... but it is useful *)
            Type.Parametric {
              name = "dict";
              parameters = [
                Single (join order left_key right_key);
                Single (join order left_value right_value);
              ]
            }
            
            (*
        | ( Type.Parametric { name = left_primitive; parameters = [Single left_key; Single left_value] },
            Type.Parametric { name = right_primitive; parameters = [Single right_key; Single right_value] } )
            when 
            (String.equal left_primitive "dict") && 
            (String.equal right_primitive "dict") &&
            (Type.equal left_key right_key)
            ->
            Type.Parametric {
              name = "dict";
              parameters = [
                Single left_key;
                Single (join order left_value right_value);
              ]
            }
            *)
        | Type.Parametric { name="BoundMethod";  parameters=[Single (Callable { Callable.kind = Callable.Named name; implementation=callable_implementation; _ }); Single any_other]},  
          Type.Parametric { name="BoundMethod"; parameters=[Single (Callable { implementation=other_implementation; _ }); Single other]}
            when Reference.equal name (Reference.create "__pyinder_any__") 
              ->
              let { Type.Callable.annotation; parameters; } = callable_implementation in
              if (Type.count_defined_without_default parameters) = (Type.count_defined_without_default other_implementation.parameters)
              then (
                let new_callable = 
                  Type.Callable { 
                    Callable.kind=Callable.Named name; 
                    implementation=
                      { annotation=join order annotation other_implementation.annotation; parameters;};
                    overloads = []
                    }
                in
                let new_other = join order other any_other in

                Type.Parametric { name="BoundMethod"; parameters=[Single new_callable; Single new_other]}

              ) else (
                Type.union [left; right]
              )
        | Type.Parametric { name="BoundMethod"; parameters=[Single (Callable { implementation=other_implementation; _ }); Single other]},
            Type.Parametric { name="BoundMethod";  parameters=[Single (Callable { Callable.kind = Callable.Named name; implementation=callable_implementation; _ }); Single any_other]}
            when Reference.equal name (Reference.create "__pyinder_any__") 
              ->
              let { Type.Callable.annotation; parameters; } = callable_implementation in
              if (Type.count_defined_without_default parameters) = (Type.count_defined_without_default other_implementation.parameters)
              then (
                let new_callable = 
                  Type.Callable { 
                    Callable.kind=Callable.Named name; 
                    implementation=
                      { annotation=join order annotation other_implementation.annotation; parameters;};
                    overloads = []
                    }
                in
                let new_other = join order other any_other in

                Type.Parametric { name="BoundMethod"; parameters=[Single new_callable; Single new_other]}

              ) else (
                Type.union [left; right]
              )
        | ( Type.Parametric { name = left_primitive; _ },
            Type.Parametric { name = right_primitive; _ } )
        | Type.Parametric { name = left_primitive; _ }, Type.Primitive right_primitive
        | Type.Primitive left_primitive, Type.Parametric { name = right_primitive; _ } ->
            if always_less_or_equal order ~left ~right && (not (Type.contains_any left)) then
              right
            else if
              always_less_or_equal order ~left:right ~right:left && (not (Type.contains_any right))
            then
              left
            else
              let target =
                try
                  if
                    always_less_or_equal
                      ~left:(Primitive left_primitive)
                      ~right:(Primitive right_primitive)
                      order
                  then
                    Some right_primitive
                  else if
                    always_less_or_equal
                      ~left:(Primitive right_primitive)
                      ~right:(Primitive left_primitive)
                      order
                  then
                    Some left_primitive
                  else
                    match join order (Primitive left_primitive) (Primitive right_primitive) with
                    | Primitive target -> Some target
                    | _ -> None
                with
                | ClassHierarchy.Untracked _ -> None
              in

              let handle_target target =
                let left_parameters = instantiate_successors_parameters ~source:left ~target in
                let right_parameters = instantiate_successors_parameters ~source:right ~target in
                let variables = variables target in
                let join_parameters_respecting_variance = function
                  | Type.Variable.UnaryPair (unary, left), Type.Variable.UnaryPair (_, right) -> (
                      match left, right, unary with
                      | Type.Bottom, other, _
                      | other, Type.Bottom, _ ->
                          Some other
                      | Type.Top, _, _
                      | _, Type.Top, _ ->
                          Some Type.Top
                      | left, right, { variance = Covariant; _ } -> Some (join order left right)
                      | left, right, { variance = Contravariant; _ } -> (
                          match meet order left right with
                          | Type.Bottom -> None
                          | not_bottom -> Some not_bottom)
                      | left, right, { variance = Invariant; _ } ->
                          if
                            always_less_or_equal order ~left ~right
                            && always_less_or_equal order ~left:right ~right:left
                          then
                            Some left
                          else
                            None)
                  | Type.Variable.TupleVariadicPair _, Type.Variable.TupleVariadicPair _
                  | Type.Variable.ParameterVariadicPair _, Type.Variable.ParameterVariadicPair _ ->
                      (* TODO(T47348395): Implement joining for variadics *)
                      None
                  | _ -> None
                in
                match left_parameters, right_parameters, variables with
                | Some left_parameters, Some right_parameters, Some variables ->
                    let replace_free_unary_variables_with_top =
                      let replace_if_free variable =
                        Option.some_if (Type.Variable.Unary.is_free variable) Type.Top
                      in
                      Type.Variable.GlobalTransforms.Unary.replace_all replace_if_free
                    in
                    Type.Variable.zip_variables_with_two_parameter_lists
                      ~left_parameters
                      ~right_parameters
                      variables
                    >>| List.map ~f:join_parameters_respecting_variance
                    >>= Option.all
                    >>| List.map ~f:replace_free_unary_variables_with_top
                    >>| List.map ~f:(fun single -> Type.Parameter.Single single)
                    >>| fun parameters -> Type.parametric target parameters
                | _ -> None
              in
              target >>= handle_target |> Option.value ~default:union
        | Type.Tuple (Concrete left), Type.Tuple (Concrete right)
          when List.length left = List.length right ->
            List.map2_exn left right ~f:(join order) |> Type.tuple
        | Type.Tuple (Concrete left), Type.Tuple (Concrete right)
          when (List.length left < List.length right) && 
            (List.equal (fun l r -> Type.equal l r) left (List.sub right ~pos:0 ~len:(List.length left)))
          -> 
            Type.Tuple (Concrete right)
        | Type.Tuple (Concrete right), Type.Tuple (Concrete left)
        when (List.length left < List.length right) && 
          (List.equal (fun l r -> Type.equal l r) left (List.sub right ~pos:0 ~len:(List.length left)))
          ->
            Type.Tuple (Concrete right)
        | Type.Tuple (Concatenation left), Type.Tuple (Concatenation right) ->
            let left_unbounded_element =
              Type.OrderedTypes.Concatenation.extract_sole_unbounded_annotation left
              |> Option.value ~default:Type.object_primitive
            in
            let right_unbounded_element =
              Type.OrderedTypes.Concatenation.extract_sole_unbounded_annotation right
              |> Option.value ~default:Type.object_primitive
            in
            Type.Tuple
              (Type.OrderedTypes.create_unbounded_concatenation
                 (join order left_unbounded_element right_unbounded_element))
        | Type.Tuple (Concrete concrete), Type.Tuple (Concatenation concatenation)
        | Type.Tuple (Concatenation concatenation), Type.Tuple (Concrete concrete) -> (
            let unbounded_element =
              Type.OrderedTypes.Concatenation.extract_sole_unbounded_annotation concatenation
              |> Option.value ~default:Type.object_primitive
            in
            match concrete with
            | concrete_head :: tail
              when List.for_all ~f:(fun element -> Type.equal element concrete_head) tail
                   && always_less_or_equal order ~left:concrete_head ~right:unbounded_element ->
                Type.Tuple (Type.OrderedTypes.create_unbounded_concatenation unbounded_element)
            | _ ->
                Type.union
                  [
                    Tuple (Concrete concrete);
                    Type.Tuple (Type.OrderedTypes.create_unbounded_concatenation unbounded_element);
                  ])
        | other, Type.Tuple (Concatenation concatenation)
        | Type.Tuple (Concatenation concatenation), other -> (
            let unbounded_element =
              Type.OrderedTypes.Concatenation.extract_sole_unbounded_annotation concatenation
              |> Option.value ~default:Type.object_primitive
            in
            match other with
            | (Type.Parametric _ as annotation)
            | (Type.Primitive _ as annotation) ->
                join order (Type.parametric "tuple" [Single unbounded_element]) annotation
            | _ -> Type.union_join left right)
        | Type.Tuple (Concrete parameters), (Type.Parametric _ as annotation)
        | (Type.Parametric _ as annotation), Type.Tuple (Concrete parameters) ->
            (* Handle cases like `Tuple[int, int]` <= `Iterator[int]`. *)
            let parameter = List.fold ~init:Type.Bottom ~f:(join order) parameters in
            join order (Type.parametric "tuple" [Single parameter]) annotation
        | Type.Tuple _, _
        | _, Type.Tuple _ ->
            Type.union [left; right]
        | ((Type.Callable { Callable.kind = Callable.Named name; implementation=callable_implementation; _ }),
          Type.Callable { implementation=other_implementation; _ })
          when Reference.equal name (Reference.create "__pyinder_any__") 
          ->
          let { Type.Callable.annotation; parameters; } = callable_implementation in
          if (Type.count_defined_without_default parameters) = (Type.count_defined_without_default other_implementation.parameters)
          then (
          Type.Callable { 
            Callable.kind=Callable.Named name; 
            implementation=
              { annotation=join order annotation other_implementation.annotation; parameters;};
            overloads = []
            }
          ) else (
            Type.union [left; right]
          )

        | (Type.Callable { implementation=other_implementation; _ },
          (Type.Callable { Callable.kind = Callable.Named name; implementation=callable_implementation; _ }))
          when Reference.equal name (Reference.create "__pyinder_any__") 
            ->
            let { Type.Callable.annotation; parameters; } = callable_implementation in
            if (Type.count_defined_without_default parameters) = (Type.count_defined_without_default other_implementation.parameters)
            then (
            Type.Callable { 
              Callable.kind=Callable.Named name; 
              implementation=
                { annotation=join order annotation other_implementation.annotation; parameters;};
              overloads = []
              }
            ) else (
              Type.union [left; right]
            )
        | ( (Type.Callable { Callable.kind = Callable.Named left_name; _ } as callable),
            Type.Callable { Callable.kind = Callable.Named right_name; _ } ) ->
            if Reference.equal left_name right_name then
              callable
            else
              Type.union [left; right]
        | Type.Callable left, Type.Callable right ->
            if List.is_empty left.Callable.overloads && List.is_empty right.Callable.overloads then
              let kind =
                if Type.Callable.equal_kind left.kind right.kind then
                  left.kind
                else
                  Type.Callable.Anonymous
              in
              join_implementations
                ~parameter_join:meet
                ~return_join:join
                order
                left.Callable.implementation
                right.Callable.implementation
              >>| (fun implementation -> Type.Callable { left with Callable.kind; implementation })
              |> Option.value ~default:union
            else (
              union
            )
        | Type.Callable callable, other
        | other, Type.Callable callable -> (
            match
              ConstraintsSet.resolve_callable_protocol ~order ~assumption:(Callable callable) other
            with
            | Some other_callable -> join order other_callable (Type.Callable callable)
            | None -> Type.union [left; right])
        | Type.Literal (String AnyLiteral), Type.Literal (String _)
        | Type.Literal (String _), Type.Literal (String AnyLiteral) ->
            Type.Literal (String AnyLiteral)
        | (Type.Literal _ as literal), other
        | other, (Type.Literal _ as literal) ->
            join order other (Type.weaken_to_arbitrary_literal_if_possible literal)
        | _ when is_protocol right ~protocol_assumptions && always_less_or_equal order ~left ~right
          ->
            right
        | _
          when is_protocol left ~protocol_assumptions
               && always_less_or_equal order ~left:right ~right:left ->
            left
        | Primitive left, Primitive right -> (
            match List.hd (least_upper_bound left right) with
            | Some joined ->
                if Type.Primitive.equal joined left then
                  Type.Primitive left
                else if Type.Primitive.equal joined right then
                  Type.Primitive right
                else
                  union
            | None -> union)
        | TypeOperation _, _
        | _, TypeOperation _ ->
            union
      in

      (* let total_time = Timer.stop_in_sec timer in *)
      (* if Float.(>.) total_time 0.1 then (
        Log.dump "JOIN %.3f %.3f\nLeft : %a =>\n%a\nRight : %a =>\n%a\n" tt0 total_time Type.pp origin_left Type.pp left Type.pp origin_right Type.pp right;
      );  *)

      Type.narrow_union ~join:(join order) ~less_or_equal:(always_less_or_equal order) x



    and meet_callable_implementations
        order
        { Type.Callable.parameters = left_parameters; annotation = left_annotation; _ }
        { Type.Callable.parameters = right_parameters; annotation = right_annotation; _ }
      =
      let open Callable in
      let parameters =
        match left_parameters, right_parameters with
        | Undefined, Undefined -> Some Undefined
        | Defined left, Defined right -> (
            let meet_of_parameters left right =
              if Type.Callable.Parameter.names_compatible left right then
                match left, right with
                | Parameter.PositionalOnly left, Parameter.PositionalOnly right
                  when Bool.equal left.default right.default ->
                    Some
                      (Parameter.PositionalOnly
                         { left with annotation = join order left.annotation right.annotation })
                | Parameter.PositionalOnly anonymous, Parameter.Named named
                | Parameter.Named named, Parameter.PositionalOnly anonymous
                  when Bool.equal named.default anonymous.default ->
                    Some
                      (Parameter.Named
                         {
                           named with
                           annotation = join order named.annotation anonymous.annotation;
                         })
                | Parameter.Named left, Parameter.Named right
                  when Bool.equal left.default right.default ->
                    Some
                      (Parameter.Named
                         { left with annotation = join order left.annotation right.annotation })
                | Parameter.Variable (Concrete left), Parameter.Variable (Concrete right) ->
                    Some (Parameter.Variable (Concrete (join order left right)))
                | Parameter.Keywords left, Parameter.Keywords right ->
                    Some (Parameter.Keywords (join order left right))
                | _ -> None
              else
                None
            in
            let add_meet_of_parameters sofar left right =
              sofar
              >>= fun sofar ->
              meet_of_parameters left right
              >>| fun meet_of_parameters -> meet_of_parameters :: sofar
            in
            match List.fold2 ~init:(Some []) ~f:add_meet_of_parameters left right with
            | Ok parameters -> parameters >>| fun parameters -> Defined (List.rev parameters)
            | Unequal_lengths -> None)
        | Undefined, Defined _
        | Defined _, Undefined ->
            Some Undefined
        | _ -> None
      in
      parameters
      >>| fun parameters -> { annotation = meet order left_annotation right_annotation; parameters }
      

    and meet ({ is_protocol; assumptions = { protocol_assumptions; _ }; _ } as order) left right =
      let left, right =
        if not !OurDomain.on_any
        then (
          (if Type.can_unknown left then Type.Any else left),
          (if Type.can_unknown right then Type.Any else right)
        )
        else left, right
      in

      if Type.equal left right then
        left
      else
        match left, right with
        | Type.Top, other
        | other, Type.Top ->
            other
        | Type.Any, other when not (Type.contains_top other) -> other
        | other, Type.Any when not (Type.contains_top other) -> other
        | Type.Bottom, _
        | _, Type.Bottom ->
            Type.Bottom
        | Type.Unknown, other
        | other, Type.Unknown ->
            if !OurDomain.on_any then
              Type.Unknown
            else
              other
        | Type.ParameterVariadicComponent _, _
        | _, Type.ParameterVariadicComponent _ ->
            Type.Bottom
        | Type.NoneType, _
        | _, Type.NoneType ->
            Type.Bottom
        | Type.Annotated left, _ -> Type.annotated (meet order left right)
        | _, Type.Annotated right -> Type.annotated (meet order left right)
        | (Type.Variable _ as variable), other
        | other, (Type.Variable _ as variable) ->
            if always_less_or_equal order ~left:variable ~right:other then
              variable
            else
              Type.Bottom
        | (Type.Union elements as union), other
        | other, (Type.Union elements as union) ->
            if always_less_or_equal order ~left:other ~right:union then
              other
            else
              List.map elements ~f:(meet order other) |> List.fold ~f:(join order) ~init:Type.Bottom
        | Type.Parametric _, Type.Parametric _
        | Type.Primitive _, Type.Primitive _ ->
            if always_less_or_equal order ~left ~right then
              left
            else if always_less_or_equal order ~left:right ~right:left then
              right
            else
              Type.Bottom
        | Type.Tuple (Concrete left), Type.Tuple (Concrete right)
          when List.length left = List.length right ->
            List.map2_exn left right ~f:(meet order) |> Type.tuple
        | Type.Tuple (Concatenation left), Type.Tuple (Concatenation right) -> (
            match
              ( Type.OrderedTypes.Concatenation.extract_sole_unbounded_annotation left,
                Type.OrderedTypes.Concatenation.extract_sole_unbounded_annotation right )
            with
            | Some left_unbounded_element, Some right_unbounded_element ->
                Type.Tuple
                  (Type.OrderedTypes.create_unbounded_concatenation
                     (meet order left_unbounded_element right_unbounded_element))
            | _ -> Type.Bottom)
        | Type.Tuple (Concrete concrete), Type.Tuple (Concatenation concatenation)
        | Type.Tuple (Concatenation concatenation), Type.Tuple (Concrete concrete) -> (
            match
              ( Type.OrderedTypes.Concatenation.extract_sole_unbounded_annotation concatenation,
                concrete )
            with
            | Some unbounded_element, concrete_head :: tail
              when List.for_all ~f:(fun element -> Type.equal element concrete_head) tail
                   && always_less_or_equal order ~left:concrete_head ~right:unbounded_element ->
                Type.Tuple (Type.OrderedTypes.create_unbounded_concatenation concrete_head)
            | _ -> Type.Bottom)
        | (Type.Tuple _ as tuple), (Type.Parametric _ as parametric)
        | (Type.Parametric _ as parametric), (Type.Tuple _ as tuple) ->
            if always_less_or_equal order ~left:tuple ~right:parametric then
              tuple
            else
              Type.Bottom
        | Type.Tuple _, _
        | _, Type.Tuple _ ->
            Type.Bottom
        | Type.Parametric _, Type.Primitive _
        | Type.Primitive _, Type.Parametric _ ->
            if always_less_or_equal order ~left ~right then
              left
            else if always_less_or_equal order ~left:right ~right:left then
              right
            else
              Type.Bottom
        | Type.RecursiveType _, _
        | _, Type.RecursiveType _ ->
            if always_less_or_equal order ~left ~right then
              left
            else if always_less_or_equal order ~left:right ~right:left then
              right
            else
              Type.Bottom
        | ( (Type.Callable { Callable.kind = Callable.Named left; _ } as callable),
            Type.Callable { Callable.kind = Callable.Named right; _ } )
          when Reference.equal left right ->
            callable
        | ( Type.Callable
              {
                overloads = [];
                kind = left_kind;
                implementation = { annotation = left_annotation; _ } as left_implementation;
              },
            Type.Callable
              {
                overloads = [];
                kind = right_kind;
                implementation = { annotation = right_annotation; _ } as right_implementation;
              } ) ->
            let kind =
              if Type.Callable.equal_kind left_kind right_kind then
                left_kind
              else
                Type.Callable.Anonymous
            in
            meet_callable_implementations order left_implementation right_implementation
            >>| (fun implementation ->
                  Type.Callable { Callable.kind; implementation; overloads = [] })
            |> Option.value
                 ~default:
                   (Type.Callable.create
                      ~annotation:(meet order left_annotation right_annotation)
                      ())
        | Type.Callable _, _
        | _, Type.Callable _ ->
            Bottom
        | (Type.IntExpression _ as int_expression), other
        | other, (Type.IntExpression _ as int_expression)
        | (Type.Literal _ as int_expression), other
        | other, (Type.Literal _ as int_expression) ->
            if always_less_or_equal order ~left:int_expression ~right:other then
              int_expression
            else
              Type.Bottom
        | Type.Primitive _, _ when always_less_or_equal order ~left ~right -> left
        | _, Type.Primitive _ when always_less_or_equal order ~left:right ~right:left -> right
        | _ when is_protocol right ~protocol_assumptions && always_less_or_equal order ~left ~right
          ->
            left
        | _
          when is_protocol left ~protocol_assumptions
               && always_less_or_equal order ~left:right ~right:left ->
            right
        | _ ->
            Log.debug "No lower bound found for %a and %a" Type.pp left Type.pp right;
            Type.Bottom
  end
end

module rec Constraints : OrderedConstraintsType = TypeConstraints.OrderedConstraints (Implementation)

and OrderedConstraintsSet : ConstraintsSet.OrderedConstraintsSetType =
  ConstraintsSet.Make (Constraints)

and Implementation : FullOrderType = OrderImplementation.Make (OrderedConstraintsSet)

let instantiate_protocol_parameters = OrderedConstraintsSet.instantiate_protocol_parameters

module OrderedConstraints = Constraints

module IncludableImplementation : FullOrderTypeWithoutT = Implementation

include IncludableImplementation

let rec is_compatible_with order ~left ~right =
  let fallback () = always_less_or_equal order ~left ~right in
  match left, right with
  (* Unknown *)
  | _, Type.Unknown
  | Type.Unknown, _ ->
    true
  (* Any *)
  | _, Type.Any
  | Type.Any, _ ->
      true
  (* Top *)
  | _, Type.Top -> true
  | Type.Top, _ -> false
  (* None *)
  | Type.NoneType, Type.NoneType -> true
  (* Tuple *)
  | Type.Tuple (Concrete left), Type.Tuple (Concrete right)
    when List.length left = List.length right ->
      List.for_all2_exn left right ~f:(fun left right -> is_compatible_with order ~left ~right)
  | Type.Tuple (Concrete bounded), Type.Tuple (Concatenation concatenation) -> (
      match Type.OrderedTypes.Concatenation.extract_sole_unbounded_annotation concatenation with
      | Some unbounded_element ->
          List.for_all bounded ~f:(fun bounded_type ->
              is_compatible_with order ~left:bounded_type ~right:unbounded_element)
      | None -> fallback ())
  (* Union *)
  | Type.Union left, right ->
      List.fold
        ~init:true
        ~f:(fun current left -> current && is_compatible_with order ~left ~right)
        left
  | left, Type.Union right ->
      List.exists ~f:(fun right -> is_compatible_with order ~left ~right) right
  (* Parametric *)
  | ( Parametric { name = left_name; parameters = left_parameters },
      Parametric { name = right_name; parameters = right_parameters } )
    when Type.Primitive.equal left_name right_name
         && Int.equal (List.length left_parameters) (List.length right_parameters) -> (
      match
        Type.Parameter.all_singles left_parameters, Type.Parameter.all_singles right_parameters
      with
      | Some left_parameters, Some right_parameters ->
          List.for_all2_exn left_parameters right_parameters ~f:(fun left right ->
              is_compatible_with order ~left ~right)
      | _ -> fallback ())
  | Type.OurTypedDictionary { general=left_general; _ }, 
    Type.OurTypedDictionary { general=right_general; _; } ->
      is_compatible_with order ~left:left_general ~right:right_general
  | Type.OurTypedDictionary { general; _ }, _ ->
    is_compatible_with order ~left:general ~right
  | _, Type.OurTypedDictionary { general; _ } ->
    is_compatible_with order ~left ~right:general
      
  | _, _ -> fallback ()


let widen order ~widening_threshold ~previous ~next ~iteration =
  if iteration > widening_threshold then
    Type.Top
  else
    join order previous next
