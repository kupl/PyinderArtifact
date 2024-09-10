
open Core
open Ast
open Ast.Util
open Expression
open Statement

module SkipMap = LocInsensitiveExpMap

module CallInfo = struct
  type t = {
    position: int;
    default: Identifier.Set.t;
    star: bool;
    double_star: bool;
  } [@@deriving sexp, equal, compare]

  let empty = {
    position=0; 
    default=Identifier.Set.empty;
    star=false;
    double_star=false;
  }

  let calculate ~signature target =
    let position_score = 1.0 /. (Float.of_int (Int.abs (target.position - signature.position) + 1)) in
    let default_score = 
      ((Identifier.Set.inter target.default signature.default |> Identifier.Set.length |> Float.of_int) +. 1.0) /. ((Identifier.Set.union target.default signature.default |> Identifier.Set.length |> Float.of_int) +. 1.0)
     (*  (Float.of_int (Identifier.Set.length target.default) +. 1.0) /. (Float.of_int (Identifier.Set.length signature.default) +. 1.0) *)
    in
    let star_score =
      1.0 /. (Float.of_int (Int.abs (Bool.to_int (not (Bool.equal target.star signature.star)) + Bool.to_int (not (Bool.equal target.double_star signature.double_star)) + 1)))
    in

    (* Log.dump "%.3f %.3f %.3f => %.3f" position_score default_score star_score (position_score *. default_score *. star_score); *)

    position_score *. default_score *. star_score

  let of_arguments arguments =
    List.fold arguments ~init:empty ~f:(fun call argument ->
      let _, t = Call.Argument.unpack argument in
      match t with
      | Positional -> { call with position=call.position + 1 }
      | Named name -> { call with default=Identifier.Set.add call.default (Node.value name)  }
      | SingleStar -> { call with star=true }
      | DoubleStar -> { call with double_star=true }
    )

  let of_parameters parameters =
    (* TODO : have to position -1? (because of self) *)
    List.fold parameters ~init:{ empty with position = -1 } ~f:(fun call (param: Parameter.t) ->
      let param = Node.value param in
      if String.is_substring ~substring:"**" param.name
      then { call with double_star=true }
      else if String.is_substring ~substring:"*" param.name
      then { call with star=true }
      else (
        match param.value with
        | Some _ -> { call with default=Identifier.Set.add call.default param.name }
        | _ -> { call with position=call.position + 1 }
      )
    )

  let pp formatter { position; default; star; double_star; } =
    let default_msg =
      Identifier.Set.fold default ~init:"(" ~f:(fun msg ident ->
        msg ^ ident ^ ","  
      )
    in
    Format.fprintf formatter "position : %i \ndefault : %s\nstar: %b\ndouble_star: %b"
      position default_msg star double_star

  let is_corresponding ~signature target =
    (* TODO: do more accurate *)
    if (not signature.star) && (not signature.double_star)
    then (
      (target.position >= signature.position)
      && (target.position + (Identifier.Set.length target.default)) <= (signature.position + (Identifier.Set.length signature.default))
      && (Identifier.Set.is_subset target.default ~of_:signature.default)
    ) else if (signature.star) && (not signature.double_star) then (
      (Identifier.Set.is_subset target.default ~of_:signature.default)
    ) 
    else (
      true
    )

  let is_more_corresponding ~signature target =
    (target.position >= signature.position) &&
    (target.position + (Identifier.Set.length target.default)) <= (signature.position + (Identifier.Set.length signature.default))
      && (Identifier.Set.is_subset target.default ~of_:signature.default)
      && is_corresponding ~signature target

  


end

module CallSet = Set.Make (CallInfo)

module AttributeStorage = struct
  type data_set = {
    attribute_set : Identifier.Set.t;
    call_set : CallSet.t Identifier.Map.t;
  } [@@deriving sexp, equal, compare]
  
  type t = data_set LocInsensitiveExpMap.t
  [@@deriving sexp, equal, compare]

  let empty_data_set = { 
    attribute_set=Identifier.Set.empty;
    call_set=Identifier.Map.empty;
  }

  let empty = LocInsensitiveExpMap.empty

  let map t ~f =
    LocInsensitiveExpMap.map t ~f

  let mapi t ~f =
    LocInsensitiveExpMap.mapi t ~f

  let fold t ~init ~f =
    LocInsensitiveExpMap.fold t ~init ~f

  let filter_keys t ~f =
    LocInsensitiveExpMap.filter_keys t ~f

  let filter_higher_items ?(num_item=3) t =
    LocInsensitiveExpMap.filter t ~f:(fun { attribute_set; call_set; } ->
      (Identifier.Set.length attribute_set) + (Identifier.Map.length call_set) >= num_item
    )

  let get_all_attributes t =
    LocInsensitiveExpMap.fold t ~init:Identifier.Set.empty ~f:(fun ~key:_ ~data:{ attribute_set; _ } acc -> 
      Identifier.Set.union acc attribute_set  
    )

  let get_single_class_param t =
    filter_keys t ~f:(fun { Node.value; _ } ->
      match value with
      | Expression.Name name 
      | Call { callee={ Node.value=Expression.Name name; _ }; _} ->
        (match name_to_reference name with
        | Some reference -> 
          (Reference.equal reference (Reference.create "$parameter$self")) || (Reference.equal reference (Reference.create "$parameter$cls"))
        | _ -> false
        )
      | _ -> false
    )

 let filter_single_class_param ~class_param t =
    filter_keys t ~f:(fun value ->
      not (String.equal (Expression.show value) class_param)
      (* match value with
      | Expression.Name name 
      | Call { callee={ Node.value=Expression.Name name; _ }; _} ->
        (match name_to_reference name with
        | Some reference -> 
          not (String.equal (Reference.show reference) class_param)
        | _ -> true
        )
      | _ -> true *)
    )

  let get_reference_list t =
    LocInsensitiveExpMap.fold t ~init:[] ~f:(fun ~key:{ Node.value; _} ~data:{ attribute_set; _ } acc ->
      match value with
      | Expression.Name name 
      | Call { callee={ Node.value=Expression.Name name; _ }; _} ->
        (match name_to_reference name with
        | Some reference -> 
          Identifier.Set.fold attribute_set ~init:acc ~f:(fun acc attr ->
            (Reference.combine reference (Reference.create attr))::acc  
          )
        | _ -> acc
        )
      | _ -> acc

    )

  let pp_identifier_set formatter ident_set =
    let msg = 
      Identifier.Set.fold ident_set ~init:"(" ~f:(fun msg ident ->
        msg ^ ", " ^ ident
      )
      ^ ")"
    in
    Format.fprintf formatter "%s" msg

  let pp_call_set formatter call_set =
    let msg = 
      Identifier.Map.fold call_set ~init:"(" ~f:(fun ~key:ident ~data:_ msg ->
        msg ^ ", " ^ ident
      )
      ^ ")"
    in
    Format.fprintf formatter "%s" msg

  let pp_data_set formatter data_set =
    Format.fprintf formatter "[[ Attribute ]]\n%a\n[[ Method ]]\n%a\n"
      pp_identifier_set data_set.attribute_set pp_call_set data_set.call_set
  
  let pp formatter t = 
    LocInsensitiveExpMap.iteri t ~f:(fun ~key ~data ->
      Format.fprintf formatter "%s ==> %a \n" (LocInsensitiveExp.show key) pp_data_set data
    )
    

  let add_attribute target attribute storage =
    let data =
      let data_set =
        if LocInsensitiveExpMap.mem storage target
        then (LocInsensitiveExpMap.find_exn storage target)
        else empty_data_set
      in 
      { data_set with attribute_set=Identifier.Set.add data_set.attribute_set attribute }
    in
    LocInsensitiveExpMap.set storage ~key:target ~data
    
  (* let is_inner_method callee =
    String.is_prefix callee ~prefix:"__" && String.is_suffix callee ~suffix:"__" *)

  let add_call target callee arguments storage =
    let call = 
      CallInfo.of_arguments arguments
    in

    let data =
      let data_set =
        if LocInsensitiveExpMap.mem storage target
        then (LocInsensitiveExpMap.find_exn storage target)
        else empty_data_set
      in 
      let call_set =
        Identifier.Map.find data_set.call_set callee
        |> Option.value ~default:CallSet.empty
      in

      let call_set = CallSet.add call_set call in

      { data_set with call_set=Identifier.Map.set ~key:callee ~data:call_set data_set.call_set }
    in
    LocInsensitiveExpMap.set storage ~key:target ~data

  let add_prefix storage ~prefix =
    fold storage ~init:empty ~f:(fun ~key ~data new_storage ->
      match get_identifier_base key with
      | Some _ ->
        let key = add_identifier_base key ~data:prefix in
        LocInsensitiveExpMap.set new_storage ~key:key ~data
      | _ -> failwith (Format.sprintf "Why is in here by add? %s" (Expression.show key))
    )

  let filter_by_prefix storage ~prefix =
    (* ClassInfo 에 넣기 위해 앞의 self prefix를 떼는 작업 *)
    fold storage ~init:empty ~f:(fun ~key ~data new_storage ->
      match Node.value key with
      | Constant _ -> new_storage
      | Call { callee={ Node.value=Expression.Name name; _ }; _ }
      | Name name ->
        (
        match name_to_reference name with
        | Some reference ->
          if (not ((Reference.equal reference prefix))) && (Reference.is_prefix ~prefix reference)
          then (
            let new_reference = Reference.drop_prefix ~prefix reference in
            let new_key = from_reference ~location:key.location new_reference in
            LocInsensitiveExpMap.set new_storage ~key:new_key ~data
          )
          else new_storage
          (*
          let base_reference = Reference.create base in
          Log.dump "BASE : %a" Reference.pp base_reference;
          if (Reference.equal base_reference prefix)
          then 
            (
              let new_base = (Reference.drop_prefix ~prefix base_reference) |> Reference.show in
              let key = change_identifier_base key ~data:new_base in
              LocInsensitiveExpMap.set new_storage ~key:key ~data
            )
          else 
            new_storage
            *)
        | _ -> failwith (Format.sprintf "Why is in here by filter? %s" (Expression.show key))
        )
      | Call _ -> new_storage
      | _ -> new_storage
    )
    
  let filter_class_var storage ~prefix =
    (* self => ( ... ) 은 관심 없기에 self.x 인 것은 다 쳐낸다 *)
    LocInsensitiveExpMap.filter_keys storage ~f:(fun key ->
      match Node.value key with
      | Constant _ -> false
      | Call _ -> false
      | Name name ->
        (
        match name_to_reference name with
        | Some reference ->
          if Reference.is_parameter reference
          then (
            if Reference.is_prefix ~prefix reference
            then true (* false *)
            else true
          )
          else (
            false
          )
          
          (*
          let base_reference = Reference.create base in
          Log.dump "BASE : %a" Reference.pp base_reference;
          if (Reference.equal base_reference prefix)
          then 
            (
              let new_base = (Reference.drop_prefix ~prefix base_reference) |> Reference.show in
              let key = change_identifier_base key ~data:new_base in
              LocInsensitiveExpMap.set new_storage ~key:key ~data
            )
          else 
            new_storage
            *)
        | _ -> failwith (Format.sprintf "Why is in here by filter? %s" (Expression.show key))
        )
      | _ -> false
    )

  let call_set_join left right =
    Identifier.Map.merge left right ~f:(fun ~key:_ data ->
      match data with  
      | `Both (left, right) ->
        Some (CallSet.union left right)
      | `Left data | `Right data -> Some data 
    )

  let data_set_join left right =
    {
      attribute_set = Identifier.Set.union left.attribute_set right.attribute_set;
      call_set = call_set_join left.call_set right.call_set;
    }

  let join left right =
    LocInsensitiveExpMap.merge left right ~f:(fun ~key:_ data ->
      match data with
      | `Both (left, right) ->
        Some (data_set_join left right)
      | `Left data | `Right data -> Some data 
    )

    (*
  let join_without_merge ~origin other =
    LocInsensitiveExpMap.merge origin other ~f:(fun ~key:_ data ->
      match data with
      | `Both (left, right) ->
        Some (Identifier.Set.union left right)
      | `Left data -> Some data 
      | `Right _ -> None
    )
    *)

end

let is_in_skip_set skip_map base attribute =
  match SkipMap.find skip_map base with
  | Some attr_set -> 
    String.Set.mem attr_set attribute
  | _ -> false

let update_skip_map skip_map callee (arguments: Call.Argument.t list) = 
  if String.equal (Expression.show callee) "hasattr" 
  then
    if (List.length arguments) = 2
    then
      let base = List.nth_exn arguments 0 in
      let attrs = List.nth_exn arguments 1 in
      let string_set = Visit.collect_constant_string attrs.value |> String.Set.of_list in
      SkipMap.set skip_map ~key:base.value ~data:string_set
    else
      failwith "Callee Length is not 2"
  else
    skip_map

let rec forward_expression_list (storage, skip_map) ~exp_list =
  List.fold exp_list ~init:(storage, skip_map) ~f:(fun (storage, skip_map) expression -> forward_expression (storage, skip_map) ~expression)

and forward_expression ?(is_assign=false) ~expression:({ Node.value; _ } as expression) (storage, skip_map) =
  let _ = expression in
  let forward_generators (storage, skip_map) ~generators =
    List.fold generators ~init:(storage, skip_map) ~f:(fun (storage, skip_map) { Comprehension.Generator.target; iterator; conditions; _ } -> 
      (storage, skip_map)
      |> forward_expression ~expression:target
      |> forward_expression ~expression:iterator
      |> forward_expression_list ~exp_list:conditions
    )
  in

  let add_attribute ?arguments base attribute name =
    match name_to_reference name with
    | Some reference when (Reference.is_target reference || Reference.is_local reference || Reference.is_parameter reference) (* && not (AttributeStorage.is_inner_method attribute) *) ->
      (* Log.dump "WHAT?? %b %b" is_assign (is_in_skip_set skip_map base attribute); *)
      if (not is_assign) && (is_in_skip_set skip_map base attribute)
      then
        (storage, skip_map) 
      else
        let storage =
          (match arguments with
          | Some arguments -> AttributeStorage.add_call base attribute arguments storage
          | _ -> AttributeStorage.add_attribute base attribute storage
          )
        in

        

        (storage, skip_map)
    | _ -> (storage, skip_map) 
  in

  match value with
  | Expression.Name (Attribute { base; attribute; _ } as name) ->
    add_attribute base attribute name |> forward_expression ~expression:base
  | Name (Identifier _) -> (storage, skip_map)
  | Await expression -> forward_expression (storage, skip_map) ~expression
  | BooleanOperator { left; right; _ }
  | ComparisonOperator { left; right; _ } ->
    (storage, skip_map)
    |> forward_expression ~expression:left
    |> forward_expression ~expression:right
  | Call { callee={ Node.value=Expression.Name (Attribute { base; attribute; _ } as name); _ }; arguments; } ->
    (* Log.dump "??? %a" Expression.pp expression; *)
    add_attribute ~arguments base attribute name 
    |> forward_expression ~expression:base
    |> (fun (storage, skip_map) -> 
      List.fold arguments ~init:(storage, skip_map) ~f:(fun (storage, skip_map) { value; _ } -> forward_expression (storage, skip_map) ~expression:value)
    )
  | Call { callee; arguments; } ->
    (storage, skip_map)
    |> forward_expression ~expression:callee
    |> (fun (storage, skip_map) -> 
        List.fold arguments ~init:(storage, skip_map) ~f:(fun (storage, skip_map) { value; _ } -> forward_expression (storage, skip_map) ~expression:value)
    )
  | Dictionary { entries; keywords; } ->
    List.fold entries ~init:(storage, skip_map) ~f:(fun (storage, skip_map) { key; value; } -> 
      (storage, skip_map)
      |> forward_expression ~expression:key
      |> forward_expression ~expression:value
    )
    |> forward_expression_list ~exp_list:keywords
  | DictionaryComprehension { element={ key; value;}; generators; } ->
    (storage, skip_map)
    |> forward_expression ~expression:key
    |> forward_expression ~expression:value
    |> forward_generators ~generators
  | Generator { element; generators; } 
  | ListComprehension { element; generators; }
  | SetComprehension { element; generators; }
  ->
    (storage, skip_map)
    |> forward_expression ~expression:element
    |> forward_generators ~generators    
  | FormatString substr_list ->
    List.fold substr_list ~init:(storage, skip_map) ~f:(fun (storage, skip_map) substr ->
      match substr with
      | Format expression -> forward_expression (storage, skip_map) ~expression
      | _ -> (storage, skip_map)  
    )
  | Lambda { parameters; body; } ->
    List.fold parameters ~init:(storage, skip_map) ~f:(fun (storage, skip_map) { Node.value; _ } ->
        match value.value with
        | Some expression -> forward_expression (storage, skip_map) ~expression
        | _ -> (storage, skip_map)
      )
    |> forward_expression ~expression:body
  | List exp_list | Set exp_list | Tuple exp_list ->
    (storage, skip_map) |> forward_expression_list ~exp_list
  | Starred t ->
    (match t with
    | Once expression
    | Twice expression ->
      (storage, skip_map) |> forward_expression ~expression
    )
  | Ternary { target; test; alternative; } ->
    (storage, skip_map)
    |> forward_expression ~expression:target
    |> forward_expression ~expression:test
    |> forward_expression ~expression:alternative
  | UnaryOperator { operand; _ } ->
    (storage, skip_map) |> forward_expression ~expression:operand
  | WalrusOperator { target; value; } ->
    (storage, skip_map)
    |> forward_expression ~expression:target
    |> forward_expression ~expression:value
  | Yield expression_opt ->
    (match expression_opt with
    | Some expression -> forward_expression (storage, skip_map) ~expression
    | _ -> (storage, skip_map)
    )
  | YieldFrom expression -> forward_expression (storage, skip_map) ~expression
  | Constant _ -> (storage, skip_map)
  

let rec forward_statement (storage, skip_map) ~statement:({ Node.value; _ } as statement) =
  let _ = statement in
  let forward_statement_list (storage, skip_map) ~stmt_list =
    List.fold stmt_list ~init:(storage, skip_map) ~f:(fun (storage, skip_map) statement -> forward_statement (storage, skip_map) ~statement)
  in

  let rec forward_pattern (storage, skip_map) ~pattern:{Node.value; _} =
    let forward_pattern_list (storage, skip_map) ~patterns =
      List.fold patterns ~init:(storage, skip_map) ~f:(fun (storage, skip_map) pattern -> forward_pattern (storage, skip_map) ~pattern)
    in

    match value with
    | Match.Pattern.MatchAs { pattern=Some pattern; _ } -> forward_pattern (storage, skip_map) ~pattern
    | MatchClass { patterns; keyword_patterns; _ } ->
      (storage, skip_map)
      |> forward_pattern_list ~patterns
      |> forward_pattern_list ~patterns:keyword_patterns
    | MatchMapping { keys; patterns; _ } ->
      (storage, skip_map)
      |> forward_expression_list ~exp_list:keys
      |> forward_pattern_list ~patterns
    | MatchOr patterns | MatchSequence patterns ->
      forward_pattern_list (storage, skip_map) ~patterns
    | MatchValue expression -> forward_expression (storage, skip_map) ~expression
    | _ -> (storage, skip_map) 
  in

  let forward_case storage ~case:{ Match.Case.pattern; guard; body; } =
    storage
    |> forward_pattern ~pattern
    |> (fun storage -> 
        match guard with
        | Some expression -> forward_expression storage ~expression
        | _ -> storage
      )
    |> forward_statement_list ~stmt_list:body
  in

  match value with
  | Statement.Assign { target; value; _ } ->
    (storage, skip_map)
    |> forward_expression ~is_assign:true ~expression:target
    |> forward_expression ~expression:value
  | Assert { test; message; _ } ->
    (storage, skip_map)
    |> forward_expression ~expression:test
    |> 
    (match message with
    | Some expression -> forward_expression ~is_assign:false ~expression
    | _ -> (fun (storage, skip_map) -> (storage, skip_map))
    )
  | Class { body; _ } ->  
    (storage, skip_map) |> forward_statement_list ~stmt_list:body
  | Delete exp_list -> forward_expression_list (storage, skip_map) ~exp_list
  | Expression expression -> forward_expression (storage, skip_map) ~expression
  | For { iterator; body; orelse; _ } ->
    (storage, skip_map)
    |> forward_expression ~expression:iterator
    |> forward_statement_list ~stmt_list:body
    |> forward_statement_list ~stmt_list:orelse
  | If { test=({ Node.value = Call { callee; arguments; }; _ } as test); body; orelse; } 
    when String.equal (Expression.show callee) "hasattr"     
    ->
      let storage, skip_map = forward_expression (storage, skip_map) ~expression:test in
      let updated_skip_map = update_skip_map skip_map callee arguments in
      let storage, _ = forward_statement_list (storage, updated_skip_map) ~stmt_list:body in
      let storage, _ = forward_statement_list (storage, updated_skip_map) ~stmt_list:orelse in
      (storage, skip_map)
  | If { test; body; orelse; } ->
    (storage, skip_map) |> forward_expression ~expression:test 
    |> forward_statement_list ~stmt_list:body
    |> forward_statement_list ~stmt_list:orelse
  | Match { subject; cases; } -> 
    (storage, skip_map) 
    |> forward_expression ~expression:subject
    |> (fun storage -> List.fold cases ~init:storage ~f:(fun storage case -> forward_case storage ~case))
  | Return { expression; _ } ->
    (match expression with
    | Some expression -> forward_expression (storage, skip_map) ~expression
    | None -> (storage, skip_map)
    )
  | Try { body; orelse; finally; _ } ->
    (storage, skip_map)
    |> forward_statement_list ~stmt_list:body
    |> forward_statement_list ~stmt_list:orelse
    |> forward_statement_list ~stmt_list:finally
  | With { items; body; _ } ->
    List.fold items ~init:(storage, skip_map) ~f:(fun (storage, skip_map) (expression, expression_opt) ->
      (storage, skip_map)
      |> forward_expression ~expression
      |> (fun (storage, skip_map) ->
          match expression_opt with
          | Some expression -> forward_expression (storage, skip_map) ~expression
          | None -> (storage, skip_map)
        )  
    )
    |> forward_statement_list ~stmt_list:body
  | While { test; body; orelse; } ->
    (storage, skip_map)
    |> forward_expression ~expression:test
    |> forward_statement_list ~stmt_list:body
    |> forward_statement_list ~stmt_list:orelse
  | Define { body; _ } ->
    (storage, skip_map) |> forward_statement_list ~stmt_list:body
  | Global _
  | Import _
  | Raise _ 
  | Nonlocal _
  | Break | Continue | Pass
    -> (storage, skip_map)