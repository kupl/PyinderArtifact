(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Analysis
open Interprocedural
open OurDomain

module TypeSummarize = OurSummary
module ReverseCallGraph = OurCallGraph.OurCallGraph
module Signature = Ast.Statement.Define.Signature

(*
let errors = ref []
let ast_environment = ref None
*)

module Summarize = struct
  type t = {
    type_summary : TypeSummarize.t;
    call_graph : ReverseCallGraph.t;
    errors : AnalysisError.t list
  }

  (*
  let remove_empty_list_of_list l =
    List.rev (List.fold l ~init:[] ~f:(fun sofar e -> if List.is_empty e then sofar else e::sofar))

  let is_inner_method target =
    match target with
    | Target.Method { method_name; _ } ->
      String.is_prefix method_name ~prefix:"_"
    | _ -> false

  let is_init_method target =
    match target with
    | Target.Method { method_name; _ } ->
      String.equal method_name "__init__"
    | _ -> false

  let reference_to_target name =
    Target.create_method name

  let target_to_reference target =
    let name = 
      match target with
      | Target.Function { name; _ } -> name
      | Method { class_name; method_name; _ } | Override { class_name; method_name; _ } -> class_name ^ "." ^ method_name
      | Object s -> s
    in
    Reference.create name


  let find_usedef_table_of_location usedef_tables cfg location =
    UsedefStruct.find_usedef_table_of_location usedef_tables cfg location |> Option.value ~default:UsedefState.bottom

    (*
  let find_error_reference (kind: AnalysisError.kind) =
    match kind with
    | UndefinedAttributeWithReference { reference; attribute; origin; } ->
      let _ = attribute, origin in
      let dropped_reference = Reference.drop_suffix ~suffix:(Reference.create attribute) reference in
      dropped_reference
    | IncompatibleParameterTypeWithReference { reference; _ } ->
      reference
    | _ -> 
      Log.dump "???";
      Reference.empty
    *)

  let rec analyze_scenario ?(check_defined=false) type_summary call_graph callee_name error_reference prev_callee =
    match List.find prev_callee ~f:(fun n -> Reference.equal n callee_name) with
    | Some _ -> []
    | None ->
      let callee_define = reference_to_target callee_name in
      if is_inner_method callee_define && (not (is_init_method callee_define))
      then (* inner method *)
        let caller_defines = ReverseCallGraph.find call_graph callee_define |> Option.value ~default:[] in

        (*List.iter filtered_caller_defines ~f:(fun target -> Log.dump "caller > %a" Target.pp target);*)

        let candidate_scenarios = List.map caller_defines ~f:(fun caller -> 
          let caller_reference = target_to_reference caller in
          let usedef_tables = TypeSummarize.get_usedef_tables type_summary caller_reference |> Option.value ~default:UsedefStruct.empty in
          let cfg = TypeSummarize.get_cfg type_summary caller_reference |> Option.value ~default:Cfg.empty in
          let locations  = ReverseCallGraph.find_callee_locations call_graph caller callee_define in
          (*Log.dump "Locations of %a" Target.pp callee_define;*)
          let candidate_scenarios_of_caller = List.fold locations ~init:[] ~f:(fun sofar callee_location -> 
            if List.is_empty sofar 
            then
              let usedef_table = find_usedef_table_of_location usedef_tables cfg callee_location in
              (*
              Log.dump "Callee Location > %a %a" Reference.pp caller_reference Location.pp callee_location;
              Log.dump "%a" UsedefState.pp usedef_table;
              *)
              (
              if check_defined && (not (is_inner_method callee_define && (not (is_init_method callee_define))))
              then
                if (not (Reference.is_empty error_reference)) && UsedefState.is_defined usedef_table error_reference 
                then
                  (* 아마 kind도 바뀌어야 할 것 *)
                  let candidate_scenarios = (analyze_scenario type_summary call_graph caller_reference error_reference (callee_name::prev_callee)) in
                  List.map candidate_scenarios ~f:(fun candidate -> if List.is_empty candidate then candidate else callee_name::candidate)
                  |> remove_empty_list_of_list
                else 
                  []
              else  
                if (not (Reference.is_empty error_reference)) && UsedefState.is_undefined usedef_table error_reference 
                then
                  (* 아마 kind도 바뀌어야 할 것 *)
                  let candidate_scenarios = (analyze_scenario type_summary call_graph caller_reference error_reference (callee_name::prev_callee)) in
                  List.map candidate_scenarios ~f:(fun candidate -> if List.is_empty candidate then candidate else callee_name::candidate)
                  |> remove_empty_list_of_list
                else 
                  []
                )
            else
              sofar
          )
          in
          if List.is_empty candidate_scenarios_of_caller then [] else (List.nth_exn candidate_scenarios_of_caller 0)
        ) in

        (*
        List.iter candidate_scenarios ~f:(fun cand ->
          Log.dump "%s" (List.fold cand ~init:"" ~f:(fun sofar ref -> sofar ^ ", " ^ Reference.show ref))
        );

        if List.is_empty candidate_scenarios then Log.dump "Empty List";
        *)
        candidate_scenarios
      else (* public method *)
          [[callee_name]]
    
    
    (*
    if is_inner_method callee_define
    then (* inner method *)
      let caller_defines = ReverseCallGraph.find call_graph callee_define |> Option.value ~default:[] in

      (*List.iter filtered_caller_defines ~f:(fun target -> Log.dump "caller > %a" Target.pp target);*)

      let candidate_scenarios = List.map caller_defines ~f:(fun caller -> 
        let caller_reference = target_to_reference caller in
        let usedef_tables = TypeSummarize.get_usedef_tables type_summary caller_reference |> Option.value ~default:UsedefStruct.empty in
        let cfg = TypeSummarize.get_cfg type_summary caller_reference |> Option.value ~default:Cfg.empty in
        let locations  = ReverseCallGraph.find_callee_locations call_graph caller callee_define in
        (*Log.dump "Locations of %a" Target.pp callee_define;*)
        let candidate_scenarios_of_caller = List.fold locations ~init:[] ~f:(fun sofar callee_location -> 
          if List.is_empty sofar 
          then
            let usedef_table = find_usedef_table_of_location usedef_tables cfg callee_location in
            
            let error_reference = find_error_reference kind in
            (*
            Log.dump "Callee Location > %a %a" Reference.pp caller_reference Location.pp callee_location;
            Log.dump "%a" UsedefState.pp usedef_table;
            *)
            (if (not (Reference.is_empty error_reference)) && UsedefState.is_undefined usedef_table error_reference 
            then
              let location = Location.with_module ~module_reference:caller_reference callee_location in
              let signature = Signature.set_name signature caller_reference in 
              let signature = Node.create_with_default_location signature in
              (* 아마 kind도 바뀌어야 할 것 *)
              let candidate_scenarios = (analyze_error type_summary call_graph { AnalysisError.location; kind; signature; cause; }) in
              List.map candidate_scenarios ~f:(fun candidate -> if List.is_empty candidate then candidate else name::candidate)
              |> remove_empty_list_of_list
            else 
              []
            )
          else
            sofar
        )
        in
        if List.is_empty candidate_scenarios_of_caller then [] else (List.nth_exn candidate_scenarios_of_caller 0)
      ) in

      (*
      List.iter candidate_scenarios ~f:(fun cand ->
        Log.dump "%s" (List.fold cand ~init:"" ~f:(fun sofar ref -> sofar ^ ", " ^ Reference.show ref))
      );

      if List.is_empty candidate_scenarios then Log.dump "Empty List";
      *)
      candidate_scenarios
      (*
      match kind with
      | UndefinedAttribute { attribute; origin; } ->
        let _ = attribute, origin in

        ()
      | _ -> ()
      *)
    else (* public method *)
      [[name]]
    *)
    

  let find_origin_function_set { TypeSummarize.class_summary; _ } class_name reference typ =
    let function_set = ClassSummary.find_map_function_of_types class_summary class_name reference typ in
    function_set


  let analyze { type_summary; call_graph; errors;} =
    let _ = type_summary, call_graph, errors in
    let candidates_scenarios = List.fold errors ~init:[] ~f:(fun sofar error -> 
      let { AnalysisError.signature; cause; _ } = error in
      match cause with
      | Some (error_reference, error_type) ->
        (*Log.dump "Suspicious Variable >>> %a : %a" Reference.pp error_reference Type.pp error_type;*)
        let { Signature.name; _ } = Node.value signature in
        let candidate_scenarios = 
          analyze_scenario type_summary call_graph name error_reference [] |> remove_empty_list_of_list 
          |> List.map ~f:List.rev  
        in

        (* find origin of cause *)
        
        let func_arg_types = TypeSummarize.get_func_arg_types type_summary name in 
        let prev_list = (
        if not (Reference.is_parameter error_reference) then []
        else
          let parameter_name = Option.value_exn (Reference.head error_reference) ~message:"This is not Parameter" in 
          let parameter_type = ArgTypes.get_type func_arg_types (Reference.show parameter_name) in

          (* primitives로 다 이끌어내지는 거 맞는지 확인해야함 *)
          let primitives = Type.primitives parameter_type in
          let prev_list = List.map primitives ~f:(fun primitive ->
            let class_name = Type.class_name primitive in
            let function_set = find_origin_function_set type_summary class_name error_reference error_type in
            FunctionSet.fold ~f:(fun sofar prev_func_name -> 
              let prev_func_paths = 
                analyze_scenario ~check_defined:true type_summary call_graph prev_func_name error_reference [] |> remove_empty_list_of_list |> List.map ~f:List.rev 
              in
              (*
              List.iter prev_func_paths ~f:(fun cand ->
                if List.is_empty cand 
                then Log.dump "No Scenario"
                else
                  Log.dump ">>> Cause : %s" (List.fold cand ~init:"" ~f:(fun sofar ref -> sofar ^ Reference.show ref ^ " => "))
              );
              *)

              prev_func_paths@sofar
            ) function_set ~init:[]
          )
          in

          prev_list
        )
        in
    


        (*
        List.iter candidate_scenarios ~f:(fun cand ->
          if List.is_empty cand 
          then Log.dump "No Scenario"
          else
            Log.dump ">>> Final : %s" (List.fold cand ~init:"" ~f:(fun sofar ref -> sofar ^ Reference.show ref ^ " => "))
        );
        *)
        (prev_list, candidate_scenarios)::sofar

      | None -> ([], [])::sofar
    )
    in
    candidates_scenarios |> List.rev


  let create () = {
    type_summary = !OurTypeSet.our_model;
    call_graph = !OurCallGraph.our_callgraph;
    errors = !errors
  }

  let pp formatter { type_summary; call_graph; _ } =
    Format.fprintf formatter "%a\n\n%a" TypeSummarize.pp type_summary ReverseCallGraph.pp call_graph; 
    *)
end
(*
let rec show_candidate_scenario candidate_scenario =
  match candidate_scenario with
  | [] -> ""
  | hd::[] -> Reference.show hd
  | hd::tl -> Reference.show hd ^ " => " ^ (show_candidate_scenario tl)

let show_candidate_scenarios candidate_scenarios =
  List.foldi candidate_scenarios ~init:"" ~f:(fun i sofar candidate_scenario -> 
    sofar ^ "   *** Scenario " ^ string_of_int i ^ " ***\n" ^ (show_candidate_scenario candidate_scenario) ^ "\n"
  )

let show_prev_list prev_list =
  List.foldi prev_list ~init:"" ~f:(fun i sofar prev -> 
    if List.is_empty prev then sofar
    else
    sofar ^
    "   *** Cause " ^ string_of_int i ^ " ***\n" ^
    (
      List.fold prev ~init:"" ~f:(fun sofar p ->
        sofar ^ show_candidate_scenario p ^ "\n"
      )
    )
  ) 

let show_candidate_scenarios (prev_list, candidate_scenarios) =
  show_prev_list prev_list ^
  "\n" ^
  show_candidate_scenarios candidate_scenarios
  *)
