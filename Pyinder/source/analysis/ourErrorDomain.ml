open Ast
open Core
open Pyre
module Error = AnalysisError
module OurErrorListReadOnly = OurErrorDomainReadOnly.OurErrorListReadOnly
module LocationMap = Map.Make (Location.WithModule)


module RefTyp = struct
  type t = Reference.t * Type.t [@@deriving sexp, equal, compare]
end

module RefTypSet = Set.Make (RefTyp)

let catch_type_join ~type_join t1 t2 =
  (try
    type_join t1 t2
  with
  | _ -> Type.Unknown
  )

module Cause = struct
  type cause =
    | Binary of cause * cause
    | RefSet of (Reference.Set.t * Type.t * Type.t)
    | Exp of (Expression.t * Type.t * Type.t)
    | Keyword of Reference.t
    | Missing of Reference.t
    | TooMany of Reference.t
    | Return of cause
    [@@deriving sexp, compare]


  let pp_ref_set format reference_set = 
    Reference.Set.iter reference_set ~f:(fun r -> Format.fprintf format "%a, " Reference.pp r)

  let rec pp_cause ppf = function
    | Binary (left, right) -> Format.fprintf ppf "Binary (%a, %a)" pp_cause left pp_cause right
    | RefSet (reference_set, typ, origin_typ) -> Format.fprintf ppf "RefSet (%a, %a <= %a)" pp_ref_set reference_set Type.pp typ Type.pp origin_typ
    | Exp (expression, typ, origin_typ) -> Format.fprintf ppf "Exp (%a, %a <= %a)" Expression.pp expression Type.pp typ Type.pp origin_typ
    | Keyword reference -> Format.fprintf ppf "Keyword %a" Reference.pp reference
    | Missing reference -> Format.fprintf ppf "Missing %a" Reference.pp reference
    | TooMany reference -> Format.fprintf ppf "TooMany %a" Reference.pp reference
    | Return cause -> Format.fprintf ppf "Return (%a)" pp_cause cause

  type t = {
    cause : cause;
    context : AstContext.t;
  } [@@deriving sexp, compare, show]

  let create ~cause ~context = { cause; context }

  let get_reference_set t =
    let rec get_reference_set t =
      match t with
      | Binary (left, right) -> Reference.Set.union (get_reference_set left) (get_reference_set right)
      | RefSet (reference_set, _, _) -> reference_set
      | Exp ({ Node.value=expression; _ }, _, _) -> Expression.get_reference_set expression
      | Keyword reference -> Reference.Set.singleton reference
      | Missing reference -> Reference.Set.singleton reference
      | TooMany reference -> Reference.Set.singleton reference
      | Return cause -> get_reference_set cause
    in
    get_reference_set t.cause

  let calc_metric left right =
    let _ = pp in
    (* Reference.Set.iter left_reference_set ~f:(fun r -> Log.dump "%a" Reference.pp r);
    Log.dump "T : %a" Type.pp left_type;
    Reference.Set.iter right_reference_set ~f:(fun r -> Log.dump "%a" Reference.pp r);
    Log.dump "T : %a" Type.pp right_type; *)
    let rec calc_cause_score ?(direct=false) left right =
      match left, right with
      | Binary (Exp e, RefSet r), _ -> calc_cause_score (Binary (RefSet r, Exp e)) right
      | _, Binary (Exp e, RefSet r) -> calc_cause_score left (Binary (RefSet r, Exp e))
      | RefSet _, Binary _ -> calc_cause_score right left
      | Binary (RefSet lr, Exp le), Binary (RefSet rr, Exp re) ->
        let refset = calc_cause_score (RefSet lr) (RefSet rr) in
        let exp = calc_cause_score (Exp le) (Exp re) in

        (* Log.dump "??? : %f * %f" refset exp; *)

        (1.0 +. exp) *. refset /. 2.0
      | Binary (RefSet l, Exp _), RefSet (r, _, origin_typ) -> 
        (* Log.dump "[OK] : %a\nVS\n%a\n[END]" pp_cause left pp_cause right; *)
        calc_cause_score (RefSet l) (RefSet (r, origin_typ, origin_typ))
      | Binary (RefSet ll, RefSet lr), RefSet (r, _, origin_typ) -> 
        (* Log.dump "[OK] : %a\nVS\n%a\n[END]" pp_cause left pp_cause right; *)
        let s1 = calc_cause_score (RefSet ll) (RefSet (r, origin_typ, origin_typ)) in
        let s2 = calc_cause_score (RefSet lr) (RefSet (r, origin_typ, origin_typ)) in
        Option.value_exn (List.max_elt ~compare:Float.compare [s1; s2;])
      | Binary (RefSet lr1, RefSet lr2), Binary (RefSet rr1, RefSet rr2) ->
        (* let timer = Timer.start () in *)
        let s1 = calc_cause_score (RefSet lr1) (RefSet rr1) in
        let s2 = calc_cause_score (RefSet lr1) (RefSet rr2) in
        let s3 = calc_cause_score (RefSet lr2) (RefSet rr1) in
        let s4 = calc_cause_score (RefSet lr2) (RefSet rr2) in
        (* let time = Timer.stop_in_sec timer in *)
        (* Log.dump "TIME : %f" time; *)
        (* Log.dump "HMM : %f %f %f %f" s1 s2 s3 s4; *)
        Option.value_exn (List.max_elt ~compare:Float.compare [s1; s2; s3; s4])
      | Binary (RefSet only, Exp _), Binary (RefSet other1, RefSet other2)
      | Binary (RefSet other1, RefSet other2), Binary (RefSet only, Exp _) ->
        let s1 = calc_cause_score (RefSet only) (RefSet other1) in
        let s2 = calc_cause_score (RefSet only) (RefSet other2) in
        Option.value_exn (List.max_elt ~compare:Float.compare [s1; s2])
      | RefSet (left_reference_set, left_type, left_total), RefSet (right_reference_set, right_type, right_total) ->
        let ref_score =
          (Reference.Set.length (Reference.Set.inter left_reference_set right_reference_set)) //
          (Reference.Set.length (Reference.Set.union left_reference_set right_reference_set))
        in

        let _ = left_total, right_total in

        (* let ref_score = Float.min 1.0 (ref_score +. 0.5) in *)
        let ref_score = Float.sqrt ref_score in

        let s1 = Type.calc_type left_type right_type in
        (* let s2 = Type.calc_type left_total right_total in
        let s3 = Type.calc_type left_total right_type in
        let s4 = Type.calc_type left_type right_total in
        let type_score = Option.value_exn (List.max_elt ~compare:Float.compare [s1; s2; s3; s4]) in *)
        let type_score = s1 in

        (* Reference.Set.iter left_reference_set ~f:(fun t -> Log.dump ">> %a" Reference.pp t);
        Log.dump "VS";
        Reference.Set.iter right_reference_set ~f:(fun t -> Log.dump ">> %a" Reference.pp t);
        Log.dump "%f * %f" ref_score type_score; *)
        ref_score *. type_score
      | Exp ({ Node.value=left_expression; _ }, left_type, _), Exp ({ Node.value=right_expression; _ }, right_type, _) (* Baseline *) ->
        (* let timer = Timer.start () in *)

        let exp_score = 
          (match left_expression, right_expression with
          | Call { callee=left_callee; _ }, Call { callee=right_callee; _ } 
            when String.equal (Expression.show left_callee) "sorted" && String.equal (Expression.show right_callee) "sorted"
            ->
            Expression.calc_similarity left_expression right_expression
          | Call { callee; _ }, _ when String.equal (Expression.show callee) "sorted" -> 0.0
          | _, Call { callee; _ } when String.equal (Expression.show callee) "sorted" -> 0.0
          | _ -> 
            if (not direct) || Expression.check_attribute left_expression right_expression 
            then 
              Expression.calc_similarity left_expression right_expression
            else 0.0 
          )
        
        in
        (* let exp_time = Timer.stop_in_sec timer in *)
        let type_score =
          Type.calc_type left_type right_type
        in
        (* let type_time = Timer.stop_in_sec timer in
        Log.dump "EXP : (%f, %f)" exp_time type_time; *)

        (* Log.dump "EXP ??? : %f * %f" exp_score type_score; *)
        
        exp_score *. type_score
      | Keyword left, Keyword right -> if Reference.equal left right then 1.0 else 0.0
      | Missing left, Missing right -> if Reference.equal left right then 1.0 else 0.0
      | TooMany left, TooMany right -> if Reference.equal left right then 1.0 else 0.0
      | Return left, Return right -> calc_cause_score left right
      | _ -> 
        (* Log.dump "[OK] : %a\nVS\n%a\n[END]" pp_cause left pp_cause right; *)
        0.0
    in

    let cause_score = calc_cause_score ~direct:true left right in


    (* Log.dump "CAUSE : %f" cause_score; *)

    1.0 -. cause_score

    let rec get_cause_type ~type_join = function
      | Binary (cause1, cause2) -> 
        let t1 = get_cause_type ~type_join cause1 in
        let t2 = get_cause_type ~type_join cause2 in
        catch_type_join ~type_join t1 t2
      | RefSet (_, c, _) -> c
      | Exp (_, c, _) -> c
      | Return cause -> get_cause_type ~type_join cause
      | _ -> Type.Unknown 
end

module CauseMap = Map.Make (Cause)
module ErrorMap = Map.Make (Error)
module ErrorSet = Set.Make (Error)


module OurCauseMap = struct
  type cause_with_ignore = {
    cause : Cause.t;
    ignore : bool;
  } [@@deriving compare, sexp]

  type t = cause_with_ignore ErrorMap.t [@@deriving compare]

  module ErrorCause = struct
    type t = Error.t * cause_with_ignore [@@deriving compare, sexp]
  end
  module ErrorCauseSet = Set.Make (ErrorCause)

  let empty = ErrorMap.empty

  (* let length t = ReferenceSetMap.length t *)

  let set ~key ~data t = ErrorMap.set ~key ~data t

  (* let find ~key t = ErrorMap.find t key *)

  let fold = ErrorMap.fold

  module RefSetSet = Set.Make (Reference.Set)

  (* let filter_singleton t = 
    (* let errors = ReferenceSetMap.data t in
    List.iter errors ~f:(fun errors -> 
      Log.dump "?? : %i" (List.length errors);
      List.iter errors ~f:(fun error -> Log.dump "E : %a" Error.pp error)
    ); *)
    
    ErrorMap.filter t ~f:(fun data -> List.length data <= 1) *)

  let get_common_reference cluster =
    let total_reference, remain = ErrorCauseSet.fold cluster ~init:(RefSetSet.empty, Reference.Set.empty) ~f:(
      fun (acc, remain) (_, data) -> 
        let cause_set = Cause.get_reference_set data.cause in
        if RefSetSet.mem acc cause_set then acc, (Reference.Set.union remain cause_set)
        else RefSetSet.add acc (Cause.get_reference_set data.cause), remain
    ) 
    in
    
    (* Log.dump "TOTaL";
    RefSetSet.iter total_reference ~f:(fun r -> 
      Log.dump "SETSET";
      Reference.Set.iter r ~f:(fun t -> Log.dump "%a" Reference.pp t)); *)
    
    let rec common_reference candidate result =
      if RefSetSet.is_empty candidate
      then result
      else (
        let current = RefSetSet.min_elt_exn candidate in
        let rest = RefSetSet.remove candidate current in
        let result = RefSetSet.fold rest ~init:result ~f:(fun result r -> 
          Reference.Set.union result (Reference.Set.inter current r)) in
        common_reference rest result
      )
    in
    Reference.Set.union remain (common_reference total_reference Reference.Set.empty)

  let get_reference_to_type ~type_join reference_set cluster =
    ErrorCauseSet.fold cluster ~init:Reference.Map.empty ~f:(
      fun acc (_, data) -> 
        let cause_set = Cause.get_reference_set data.cause |> Reference.Set.filter ~f:(fun r -> Reference.Set.mem reference_set r) in
        let cause_type = Cause.get_cause_type ~type_join data.cause.cause in
        Reference.Set.fold cause_set ~init:acc ~f:(
          fun acc r -> 
            let data = Reference.Map.find acc r |> Option.value ~default:Type.Unknown in
            Reference.Map.set acc ~key:r ~data:(catch_type_join ~type_join data cause_type)
        )
    ) 
    

  let function_to_reference ~cluster ~type_join func_to_ref =
    let common = get_common_reference cluster in
    let ref_to_type = get_reference_to_type ~type_join common cluster in
    let func_to_ref =
    ErrorCauseSet.fold cluster ~init:func_to_ref ~f:(fun acc (key, _) ->
      let error_function = 
        (key.signature |> Node.value).name
      in
      let data_func = Reference.Map.find acc error_function |> Option.value ~default:Reference.Map.empty in
      let data =
        Reference.Map.fold ref_to_type ~init:data_func ~f:(fun ~key ~data acc_ref ->
          let type_data = Reference.Map.find acc_ref key |> Option.value ~default:Type.Unknown in
          Reference.Map.set acc_ref ~key ~data:(catch_type_join ~type_join type_data data)
        )
      in
      (* let data_ref = Reference.Map.find acc_ref common |> Option.value ~default:Type.Unknown in
      Reference.Map.set acc ~key:error_function ~data:(Reference.Set.union data common),
      Reference.Map. *)
      Reference.Map.set acc ~key:error_function ~data
    )
    in
    func_to_ref


  let dbscan ~epsilon ~type_join ~min_pts (t: t) =
    let _ = epsilon in
    let rec find_cluster ~(errors: t) check_points cluster_points =
      if ErrorCauseSet.is_empty check_points
      then cluster_points
      else
        let new_check_points = 
          ErrorCauseSet.fold check_points ~init:ErrorCauseSet.empty ~f:(fun new_check_points (check_point, _) ->
            let inner_points = 
              ErrorMap.fold errors ~init:[] ~f:(fun ~key ~data:({ cause={Cause.cause; context;}; ignore; } as error_data) acc -> 

                if ErrorCauseSet.mem cluster_points (key, error_data) || ErrorCauseSet.mem new_check_points (key, error_data) then acc else (

                  let { cause={Cause.cause=check_cause; context=check_context;}; ignore=check_ignore; } = (ErrorMap.find_exn errors check_point) in
                  
                  let _ = ignore, check_ignore in

                  (* Log.dump "%b vs %b" ignore check_ignore; *)

                  if AstContext.compare context check_context = 0
                  then (
                    (* Log.dump "Same Context"; *)
                    if (ignore || check_ignore) then (
                      let cause_distance = (Cause.calc_metric cause check_cause ) in
                      if Float.(<.) cause_distance 0.5 then (
                        (key, error_data)::acc
                      )
                      else acc
                    )
                    else (
                      match key, check_point with
                      | { kind=Error.UnexpectedKeyword _; _ }, { kind=Error.UnexpectedKeyword _; _ }
                      | { kind=Error.TooManyArguments _; _ }, { kind=Error.TooManyArguments _; _ }
                      | { kind=Error.MissingArgument _; _ }, { kind=Error.MissingArgument _; _ } -> (
                        (* let cause_distance = (Cause.calc_metric cause check_cause ) in *)
                        let cause_distance = 1.0 in
                        if Float.(<.) cause_distance 1.1 then (
                          (key, error_data)::acc
                        )
                        else acc
                      )
                      | _ -> acc
                    )
                  )
                  else (

                    (* Log.dump "HERE"; *)
                    (match key, check_point with
                      | { kind=Error.UnexpectedKeyword _; _ }, { kind=Error.UnexpectedKeyword _; _ }
                      | { kind=Error.TooManyArguments _; _ }, { kind=Error.TooManyArguments _; _ }
                      | { kind=Error.MissingArgument _; _ }, { kind=Error.MissingArgument _; _ } -> (
                        let cause_distance = (Cause.calc_metric cause check_cause ) in
                        if Float.(<.) cause_distance 0.5 then (
                          (key, error_data)::acc
                        )
                        else acc
                      )
                      | { kind=Error.UnexpectedKeyword _; _ }, _ | _, { kind=Error.UnexpectedKeyword _; _ }
                      | { kind=Error.TooManyArguments _; _ }, _ | _, { kind=Error.TooManyArguments _; _ }
                      | { kind=Error.MissingArgument _; _ }, _ | _, { kind=Error.MissingArgument _; _ } -> acc
                      | _ ->
                        let cause_distance = (Cause.calc_metric cause check_cause ) in
                        (* let context_distance = (AstContext.calc_metric context check_context) in *)

                        (* if Float.(<=.) cause_distance 0.25 && Float.(<=.) context_distance 0.75
                        then (
                          Log.dump "[FIRST]\n\n%a\n\n[SECOND]\n\n%a\n\n" Error.pp key Error.pp check_point;
                          Log.dump "Distance : %.3f, %.3f\n\n" cause_distance context_distance;
                        ); *)
                        if Float.(<.) cause_distance 0.5 (* && Float.(<.) context_distance 1.1 *)
                        then (
                          (* if ignore then  (
                            Log.dump "Connect! %b => %a" ignore Error.pp key;
                          ); *)
                          (* Log.dump "[FIRST]\n\n%a\n\n[SECOND]\n\n%a\n\n" Error.pp key Error.pp check_point;
                          Log.dump "Distance : %.3f, %.3f\n\n" cause_distance context_distance; *)
                          (key, error_data)::acc
                        )
                        else if (ignore || check_ignore) && Float.(<.) cause_distance 0.5 then (
                          (* Log.dump "[FIRST]\n\n%a\n\n[SECOND]\n\n%a\n\n" Error.pp key Error.pp check_point;
                          Log.dump "Distance : %.3f, %.3f\n\n" cause_distance context_distance; *)
                          acc
                        )
                        else (
                          (* Log.dump "[FIRST]\n\n%a\n\n[SECOND]\n\n%a\n\n" Error.pp key Error.pp check_point;
                          Log.dump "Distance : %.3f, %.3f\n\n" cause_distance context_distance; *)
                          acc
                        )
                      )
                  )
                )
              )
            in

            (* Log.dump "%i" (List.length inner_points); *)

            if List.length inner_points >= min_pts
            then (
              List.fold inner_points ~init:new_check_points ~f:(fun new_check_points point ->
                (* ErrorSet.add new_check_points point *)   
                  if ErrorCauseSet.mem cluster_points point 
                  then new_check_points
                  else ErrorCauseSet.add new_check_points point
              )
            ) else 
              new_check_points
          )
        in

        find_cluster ~errors new_check_points (ErrorCauseSet.union cluster_points new_check_points)
    in

    let rec get_noise_point t noise_map cluster_map common_reference =
      match ErrorMap.nth t 0 with
      | None -> noise_map, cluster_map, common_reference
      | Some (key, data) ->

        (* let timer = Timer.start () in
        Log.dump "FIND IN %i" (ErrorMap.length t); *)

        let new_cluster = find_cluster ~errors:t (ErrorCauseSet.singleton (key, data)) (ErrorCauseSet.singleton (key, data)) in

        (* let find_time = Timer.stop_in_sec timer in
        if (ErrorCauseSet.length new_cluster) > 1 then
          Log.dump "FIND : %f (%i)" find_time (ErrorCauseSet.length new_cluster); *)

        (* if ErrorSet.length new_cluster = 1 then (
          Log.dump "\n[[ SINGLE ]]";
          (* Log.dump ">> %a" Error.pp key; *)
          ErrorSet.iter new_cluster ~f:(fun error -> Log.dump ">> %a" Error.pp error);
        );
 *)
        (* let is_local_error =
          (match key.kind with
          | Error.UnsupportedOperandWithReference (BinaryWithReference { left_reference; right_reference; _ }) ->
            let left_reference = Reference.create (Expression.show left_reference) in
            let right_reference = Reference.create (Expression.show right_reference) in
            (Reference.is_local left_reference && not (Reference.is_parameter left_reference)) || (Reference.is_local right_reference && not (Reference.is_parameter right_reference))
          | Error.UnsupportedOperandWithReference (UnaryWithReference { reference; _ }) ->
            let reference = Reference.create (Expression.show reference) in
            Reference.is_local reference && not (Reference.is_parameter reference)
          | Error.IncompatibleParameterTypeWithReference { reference; _ } ->
            let reference = Reference.create (Expression.show reference) in
            Reference.is_local reference && not (Reference.is_parameter reference)
          | Error.UndefinedAttributeWithReference { reference; _ } ->
            let reference = Reference.create (Expression.show reference) in
            Reference.is_local reference && not (Reference.is_parameter reference)
          | Error.UnexpectedKeyword _
          | Error.TooManyArguments _
          | Error.MissingArgument _ -> true
          | _ -> false
          )
        in *)


        (* if ErrorCauseSet.length new_cluster >= 4 then (
          (* Log.dump "\n[[ CLUSTER ]] : %i" (ErrorCauseSet.length new_cluster); *)
          (* Log.dump "LOCAL %b" is_local_error; *)
          (* Log.dump "(%b) >> %a" data.ignore Error.pp key; *)
          ErrorCauseSet.iter new_cluster ~f:(fun (error, cause) -> Log.dump "Error >> %a\nCause >> %a" Error.pp error Cause.pp cause.cause);
        ); *)


        let next_t = ErrorMap.filteri t ~f:(fun ~key ~data -> not (ErrorCauseSet.mem new_cluster (key, data))) in

        (* Log.dump "LENGTH %i" (ErrorMap.length next_t); *)
        if ErrorCauseSet.length new_cluster < 4
        then (
          get_noise_point next_t (ErrorCauseSet.fold ~init:noise_map ~f:(fun noise_map (key, data) -> ErrorMap.set ~key ~data noise_map) new_cluster) cluster_map common_reference
        )
        else (
          (* ErrorCauseSet.iter new_cluster ~f:(fun (error, cause) -> 
            Log.dump "Error >> %a\nCause >> %a" Error.pp error Cause.pp cause.cause
          ); *)

          get_noise_point next_t noise_map (ErrorCauseSet.fold ~init:cluster_map ~f:(fun cluster_map (key, data) -> ErrorMap.set ~key ~data cluster_map) new_cluster)
          (function_to_reference ~type_join ~cluster:new_cluster common_reference)
        )
    in

    get_noise_point t empty empty Reference.Map.empty
end

module OurErrorList = struct
  type errors = Error.t list [@@deriving sexp, compare]

  type error_with_ignore = {
    error : Error.t;
    ignore : bool
  } [@@deriving sexp, compare]

  type t = error_with_ignore LocationMap.t [@@deriving sexp, compare]

  let empty = LocationMap.empty

  let equal t1 t2 = compare t1 t2 = 0 

  let set ~key ~data t = LocationMap.set ~key ~data t

  let get ~key t = LocationMap.find t key

  let add ~join ~(errors : Error.t list) ~(ignore_lines: Ignore.t list) t =
    let errors = 
      Error.filter_type_error errors 
      |> List.filter ~f:(fun e -> not (Error.due_to_analysis_limitations e))
    in
    List.fold errors ~init:t ~f:(fun t error -> 
      let error_line = Location.WithModule.line error.location in
      LocationMap.update t error.location ~f:(fun v ->
        match v with
        | Some { error=origin_error; ignore=origin_ignore; } -> 
          let error = Error.join_without_resolution ~type_join:join origin_error error in
          let ignore = origin_ignore in
          { error; ignore }
          (* if String.equal (Reference.show origin_error.signature.value.name) "test.ParserBase._should_parse_dates"
          then 
          Log.dump "HMM : %a" Error.pp error; *)
        | _ -> 
          let ignore = 
            List.exists ignore_lines ~f:(fun { Ignore.location=ignore_location; _ } -> 
              let ignore_line = Location.line ignore_location in
    
              ignore_line = error_line
            )
          in
          { error; ignore }   
      )
    )
  let num t =
    LocationMap.length t

  let cause_map_to_t (cause_map: OurCauseMap.t) =
    OurCauseMap.fold cause_map ~init:empty ~f:(fun ~key:({ Error.location; _ } as error) ~data:{ ignore; _ } acc ->
        set ~key:location ~data:{ error; ignore; } acc  
    )

  let get_cause ~global_resolution (t: t) our_model =
    let _ = global_resolution in
    let cause_map, loc_map =
      LocationMap.fold t ~init:(OurCauseMap.empty, LocationMap.empty) ~f:(
        fun ~key ~data:({ error=({ Error.signature={ Node.value={ name; parent; _ }; _ }; context; _ } as error); ignore }) (acc, locmap) ->
        
        let flag =
          (match error.kind with
          | Error.IncompatibleParameterTypeWithReference { mismatch={ actual; _ }; callee; _ } 
            when String.equal (Option.value ~default:Reference.empty callee |> Reference.show) "sum"
            -> 
            if (String.is_prefix (Type.show actual) ~prefix:"List[int]")
              || (String.is_prefix (Type.show actual) ~prefix:"List[Unknown]")
              || (String.is_prefix (Type.show actual) ~prefix:"List[bool]")
              || (String.is_prefix (Type.show actual) ~prefix:"typing.List[int]")
              || (String.is_prefix (Type.show actual) ~prefix:"map[")
              || (String.is_prefix (Type.show actual) ~prefix:"dict_keys[")
              || (String.is_prefix (Type.show actual) ~prefix:"dict_values[")
              || (String.is_prefix (Type.show actual) ~prefix:"dict_items[")
            then true 
            else false
          | Error.IncompatibleParameterTypeWithReference { mismatch={ actual; _ }; callee; _ } 
            when String.equal (Option.value ~default:Reference.empty callee |> Reference.show) "list.__getitem__"
            -> 
            if (String.is_prefix (Type.show actual) ~prefix:"Union[int, slice]")
            then true 
            else false
          | Error.IncompatibleParameterTypeWithReference { mismatch={ actual; _ }; callee; _ } 
            when String.equal (Option.value ~default:Reference.empty callee |> Reference.show) "list.append"
            -> 
            if (String.is_prefix (Type.show actual) ~prefix:"List[")
            then true 
            else false
          | Error.IncompatibleParameterTypeWithReference { mismatch={ actual; _ }; callee; _ } ->
            let callee = Option.value ~default:Reference.empty callee in
            let _ = callee in

            if Type.is_generator actual 
              || (String.is_prefix (Type.show actual) ~prefix:"map[")
              || (String.is_prefix (Type.show actual) ~prefix:"dict_keys[")
              || (String.is_prefix (Type.show actual) ~prefix:"dict_values[")
              || (String.is_prefix (Type.show actual) ~prefix:"dict_items[")
            then true 
            else false
          | _ -> false
          )
        in

        if flag (* && false *) (* Baseline *) then acc, locmap else (
        
          (* Log.dump "??? %a" Error.pp error; *)
          let _ = error in
          (* let module_reference = key.module_reference in *)
          let location = Location.strip_module key in
          let unique_analysis = OurDomain.OurSummary.get_unique_analysis our_model name in
          let error_expression_list = Error.get_expression_type [error] in

          match error_expression_list with
          | [] -> 
            (match error.kind with
            | UnexpectedKeyword { callee; _ } 
            | TooManyArguments { callee; _ } 
            | MissingArgument { callee; _ } -> (
              match callee with
              | Some callee when String.equal (Reference.show callee) "object.__init__" (* && false *) (* Baseline *)->
                acc, locmap
              | Some callee -> (
                match error.kind with
                | UnexpectedKeyword _ -> 
                  OurCauseMap.set acc ~key:error ~data:{ OurCauseMap.cause=(Cause.create ~context ~cause:(Cause.Keyword callee)); ignore; }
                | TooManyArguments _ -> 
                  OurCauseMap.set acc ~key:error ~data:{ OurCauseMap.cause=(Cause.create ~context ~cause:(Cause.TooMany callee)); ignore; }
                | MissingArgument _ ->
                  OurCauseMap.set acc ~key:error ~data:{ OurCauseMap.cause=(Cause.create ~context ~cause:(Cause.Missing callee)); ignore; }
                | _ -> acc
              ), locmap
              | _ -> acc, LocationMap.set ~key ~data:{ error; ignore; } locmap
            )
            | _ -> acc, LocationMap.set ~key ~data:{ error; ignore; } locmap
            )
          | _ -> 
            let new_acc = 
              List.map error_expression_list ~f:(fun (error_expression, typ, origin_typ, cause) -> 
                let _ = cause in
                match error_expression |> Expression.get_first_name >>= Expression.name_to_reference with
                | Some error_reference -> (
                  match UniqueAnalysis.UniqueStruct.find_pre_statements_of_location unique_analysis location with
                    | Some (state, loc) ->
                      let error_reference =
                        if String.equal cause "zip" then (
                          Reference.combine error_reference (Reference.create "_zip")
                        ) else (
                          error_reference
                        )
                      in
                      let _ = state, loc in
                      let var_set = UniqueAnalysis.UniqueState.get_all_relative_variables ~reference:error_reference state in

                      (* let param_to_varset =
                        let param_varset = OurDomain.OurSummary.get_param_varset our_model name in
                        let parameters = Reference.Set.filter var_set ~f:(fun v -> Reference.is_parameter v) in
                        Reference.Set.fold parameters ~init:Reference.Set.empty ~f:(fun acc v ->

                          (* Log.dump "FIND %a" Reference.pp v;
                          Identifier.Map.iteri param_varset ~f:(fun ~key:param_varset ~data:varset ->
                            Log.dump "KEY %a" Identifier.pp param_varset;
                            Reference.Set.iter varset ~f:(fun v -> Log.dump "VAR %a" Reference.pp v);
                          ); *)

                          let varset = Identifier.Map.find param_varset (Reference.show v) |> Option.value ~default:Reference.Set.empty in
                          Reference.Set.union acc varset
                        )
                      in

                      let _ = param_to_varset in *)

                      let suspicious_params =
                        let param_varset = OurDomain.OurSummary.get_param_varset our_model name in
                        let parameters = Reference.Set.filter var_set ~f:(fun v -> 
                          Reference.is_parameter v && (
                            let var_set = Identifier.Map.find param_varset (Reference.show v) |> Option.value ~default:Reference.Set.empty in
                            (* let var_set =
                              Reference.Set.filter var_set ~f:(fun v -> 
                                (v
                                |> GlobalResolution.resolve_exports global_resolution
                                >>= UnannotatedGlobalEnvironment.ResolvedReference.as_module_toplevel_reference
                                >>= fun a -> Some a)
                                |> Option.is_none
                              )
                            in *)
                            Reference.Set.exists var_set ~f:(fun v -> Reference.is_cls v 
                              || Reference.is_self v 
                              || Reference.is_attribute v
                            )
                          )
                        ) 
                        in
                        parameters
                      in

                      (* let var_set = Reference.Set.union var_set param_to_varset in *)
                      (* Log.dump "[ STATE ] %a \n %a" UniqueAnalysis.UniqueState.pp state Location.pp loc; *)
                      (* Log.dump "ERROR : %a" Reference.pp error_reference;
                      Log.dump "HMM? %a ====> %a" Error.pp error UniqueAnalysis.UniqueState.pp state; *)
                      (* Reference.Set.iter var_set ~f:(fun v -> Log.dump "%a" Reference.pp v); *)

                      (* let var_set =
                        Reference.Set.filter var_set ~f:(fun v -> 
                          (v
                          |> GlobalResolution.resolve_exports global_resolution
                          >>= UnannotatedGlobalEnvironment.ResolvedReference.as_module_toplevel_reference
                          >>= fun a -> Some a)
                          |> Option.is_none
                        )
                      in *)

                      let cause_var =
                        if Reference.is_local error_reference then (
                          None
                        ) else (
                          let error_reference = 
                            if Reference.is_local error_reference then Reference.delocalize_only_name error_reference else error_reference
                          in

                          if (not (Reference.is_self error_reference)) && (String.equal cause "__getitem__" || String.equal cause "__setitem__")
                          then (
                            let error_reference = Reference.create ((Reference.show error_reference) ^ ".__index__") in
                            error_reference
                          )
                          else error_reference
                        ) |> Option.some
                      in

                      let var_set =
                        Reference.Set.map var_set ~f:(fun v -> 
                          if Reference.is_local v then Reference.delocalize_only_name v else v
                        )
                      in

                      (* Log.dump "HMM...";
                      Reference.Set.iter var_set ~f:(fun v -> Log.dump "%a" Reference.pp v); *)

                      let var_set =
                        Reference.Set.filter var_set ~f:(fun v -> Reference.is_cls v 
                          || Reference.is_self v 
                          || Reference.is_attribute v
                        )
                        |> Reference.Set.union suspicious_params
                      in

                      let var_set =
                        match cause_var with
                        | Some cause_var ->
                          if Reference.is_parameter cause_var && (not (Reference.is_cls cause_var || Reference.is_self cause_var)) then (
                            if (Reference.Set.exists suspicious_params ~f:(fun v -> Reference.is_contain ~base:cause_var ~target:v)) then (
                              Reference.Set.add var_set cause_var
                            ) else (
                              var_set
                            )
                          ) else (
                            Reference.Set.add var_set cause_var
                          )
                        | _ -> var_set
                      in

                      (* Log.dump "Before";
                      Reference.Set.iter var_set ~f:(fun v -> Log.dump "%a" Reference.pp v); *)

                      let var_set =
                        Reference.Set.filter var_set ~f:(fun v ->
                          let rest = Reference.Set.remove var_set v in
                          not (Reference.Set.exists rest ~f:(fun r -> Reference.is_contain ~base:r ~target:v))
                        )
                      in

                      
                      let var_set =
                        (match parent with
                        | Some class_name -> 
                          OurDomain.OurSummary.filter_seen_var ~class_name ~func_name:name ~var_set our_model
                        | _ -> var_set
                        )
                        |> Reference.Set.filter ~f:(fun v -> 
                          not (String.equal "len" (Reference.show v))
                        )
                      in

                      (* Log.dump "After";
                      Reference.Set.iter var_set ~f:(fun v -> Log.dump "%a" Reference.pp v); *)

                      Cause.RefSet (var_set, typ, origin_typ)
                    | None -> Cause.Exp (error_expression, typ, origin_typ)
                )
                | _ -> (* Expression 비교 *) 
                  Cause.Exp (error_expression, typ, origin_typ)
              )
              |> (function 
                | left::[right] ->
                  (match error.kind with
                  | Error.IncompatibleReturnTypeWithExpression _ ->
                    OurCauseMap.set acc ~key:error ~data:{ OurCauseMap.cause=(Cause.create ~context ~cause:((Cause.Binary (left, right)))); ignore; }
                  | _ ->
                    OurCauseMap.set acc ~key:error ~data:{ OurCauseMap.cause=(Cause.create ~context ~cause:(Cause.Binary (left, right))); ignore; }
                  )
                  
                | [cause] ->
                  (match error.kind with
                  | Error.IncompatibleReturnTypeWithExpression _ ->
                    OurCauseMap.set acc ~key:error ~data:{ OurCauseMap.cause=(Cause.create ~context ~cause:(cause)); ignore; }
                  | _ ->
                    OurCauseMap.set acc ~key:error ~data:{ OurCauseMap.cause=(Cause.create ~cause ~context); ignore; }
                  )
                | _ -> acc
              )
                (* let data = OurCauseMap.find ~key:(error_reference_set, typ) acc |> Option.value ~default:[] in *)
                
              
            in
            new_acc, locmap
          )
      )
    in
    cause_map, loc_map

  let inter_error (t1: t) (t2: t) =
    LocationMap.merge t1 t2 ~f:(fun ~key:_ data ->
      match data with
      | `Left _ | `Right _ -> None
      | `Both (a, b) -> if Error.compare_only_location a.error b.error = 0 then Some a else None
    )

  let merge_error (t1: t) (t2: t) =
    LocationMap.merge t1 t2 ~f:(fun ~key:_ data ->
      match data with
      | `Left v | `Right v -> Some v
      | `Both (a, _) -> Some a
    )
  
  let cause_analysis ~global_resolution (t: t) our_model =
    let timer = Timer.start () in
    let cause_map, loc_map = get_cause ~global_resolution t our_model in
    let get_cause_time = Timer.stop_in_sec timer in
    let type_join = GlobalResolution.join global_resolution in
    let noise_map, cluster_map, function_to_reference = OurCauseMap.dbscan ~type_join ~epsilon:0.5 ~min_pts:1 cause_map in
    let get_map_time = Timer.stop_in_sec timer in
    (* Log.dump "END MAP"; *)
    let noise_map =
      noise_map
      |> cause_map_to_t
      |> LocationMap.merge loc_map ~f:(fun ~key:_ data ->
        match data with
        | `Left v | `Right v -> Some v
        | `Both (a, b) -> if Error.compare a.error b.error = 0 then Some a else None
      )
    in

    let cluster_map =
      cluster_map
      |> cause_map_to_t
      |> LocationMap.merge loc_map ~f:(fun ~key:_ data ->
        match data with
        | `Left v | `Right v -> Some v
        | `Both (a, b) -> if Error.compare a.error b.error = 0 then Some a else None
      )
    in
    let remove_time = Timer.stop_in_sec timer in

    Log.dump "%f %f %f" get_cause_time get_map_time remove_time;

    (* let other_x =
      cause_map
      |> cause_map_to_t
      |> LocationMap.merge loc_map ~f:(fun ~key:_ data ->
        match data with
        | `Left v | `Right v -> Some v
        | `Both (a, b) -> if Error.compare a b = 0 then Some a else None
      )
    in *)

    (* Log.dump "%i => %i" (LocationMap.length t) (LocationMap.length noise_map); *)

    noise_map, cluster_map, function_to_reference

    (* LocationMap.fold t ~init:0 ~f:(fun ~key:_ ~data acc ->
      List.length data + acc  
    ) *)

  (* let get_repeated_errors t key_list =
    let reference_type_map =
    ReferenceMap.filter_keys t ~f:(fun key -> List.exists key_list ~f:(Reference.equal key))
    |> ReferenceMap.map ~f:(fun errors ->
      let reference_type_list = 
        Error.get_reference_type errors 
      in

      let empty_set = RefTypSet.empty in
      List.fold reference_type_list ~init:empty_set ~f:(fun acc (r, t) -> RefTypSet.add acc (r, t))
    )
    in

    (* Log.dump "Map : %i" (ReferenceMap.length reference_type_map); *)

    let total_set = ReferenceMap.fold reference_type_map ~init:RefTypSet.empty ~f:(fun ~key:_ ~data acc ->
      RefTypSet.union acc data  
    )
    in

    (* Log.dump "Set : %i" (RefTypSet.length total_set); *)

    let remain_reftyp_set = 
      RefTypSet.filter total_set ~f:(fun (reference, typ) -> 
        let count = 
          ReferenceMap.fold reference_type_map ~init:0 ~f:(fun ~key:_ ~data:reference_type_set count ->
            if RefTypSet.mem reference_type_set (reference, typ) then count+1 else count
          )
        in

        let ref_count =
          List.fold key_list ~init:0 ~f:(fun count key ->
            let attribute_storage = OurDomain.OurSummary.get_usage_attributes_from_func !OurDomain.our_model key in
            let reference_list = AttributeAnalysis.AttributeStorage.get_reference_list attribute_storage in
            if List.exists reference_list ~f:(Reference.equal reference) then count+1 else count
          )
        in

        (* Log.dump "(%a, %a) => %i / %i" Reference.pp reference Type.pp typ count ref_count; *)
        
        (ref_count < 2 && not (Reference.is_parameter reference)) 
        || not (ref_count = 0 || Float.(>=) (Int.(//) count ref_count) 0.5)
      )
    in

    (* Log.dump "START";
    RefTypSet.iter remain_reftyp_set ~f:(fun (r, t) -> Log.dump "(%a, %a)" Reference.pp r Type.pp t);
 *)
    let x= 
    ReferenceMap.mapi t ~f:(fun ~key ~data:errors ->
      let flag = List.exists key_list ~f:(Reference.equal key) in 
      if flag then
        let exist = RefTypSet.mem remain_reftyp_set in
        let after = Error.filter_typical_errors ~exist errors in

        (* List.iter after ~f:(fun e -> Log.dump "ERROR: %a" Error.pp e); *)

        after
      else
        errors
    )
      in
    (* Log.dump "END"; *)
    x *)

  (*
  let equal left right =
    ReferenceMap.equal (fun l_value r_value -> [%compare.equal: Error.t list] l_value r_value) -> left right 
    *)
end

type errors = Error.t list [@@deriving sexp]

let read_only (our_error_list: OurErrorList.t) =
  let reference_map =
    LocationMap.fold our_error_list ~init:Reference.Map.empty ~f:(fun ~key:_ ~data:{ error=data; _ } ref_map -> 
      let signature = Node.value data.signature in
      let key = signature.name in
      let error_list = Reference.Map.find ref_map key |> Option.value ~default:[] in
      
      Reference.Map.set ref_map ~key ~data:(data::error_list)
    )
  in
  Reference.Map.fold reference_map ~init:OurErrorListReadOnly.empty ~f:(fun ~key ~data read_only -> 
    OurErrorListReadOnly.set ~key ~data:(sexp_of_errors data) read_only
  )

let get_errors ~key t = 
  OurErrorDomainReadOnly.ReferenceMap.find t key
  |> (function
  | Some errors -> errors_of_sexp errors
  | _ -> []
  )

let our_errors = ref OurErrorList.empty