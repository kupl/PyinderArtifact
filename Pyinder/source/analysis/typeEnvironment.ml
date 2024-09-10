(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Pyre
open Ast
open Core
module PreviousEnvironment = AnnotatedGlobalEnvironment
module Error = AnalysisError

module CheckResultValue = struct
  type t = TypeCheck.CheckResult.t option [@@deriving equal]

  let prefix = Prefix.make ()

  let description = "CheckResult"
end





let produce_check_results global_environment define_info ~dependency =
  let timer = Timer.start () in
  let define_name = define_info in 
  (* let _ = our_model in  *)
  (* Log.dump "Start %a" Reference.pp define_name; *)
  (* let define_name, entry_arg_types = OurDomain.ArgTypesKey.from_key define_info in
  let _ = entry_arg_types in *)
  let type_check_controls, call_graph_builder, dependency =
    let controls = AnnotatedGlobalEnvironment.ReadOnly.controls global_environment in
    let configuration = EnvironmentControls.configuration controls in
    OurDomain.set_data_path configuration;
    OurDomain.our_model :=  EnvironmentControls.our_summary controls;
    let type_check_controls = EnvironmentControls.type_check_controls controls in
    let call_graph_builder =
      if EnvironmentControls.populate_call_graph controls then
        (module Callgraph.DefaultBuilder : Callgraph.Builder)
      else
        (module Callgraph.NullBuilder : Callgraph.Builder)
    in
    let dependency =
      if EnvironmentControls.track_dependencies controls then
        dependency
      else
        None
    in
    type_check_controls, call_graph_builder, dependency
  in


  
  let mode = OurDomain.load_mode () in

  if String.equal mode "recheck" then (
    OurDomain.OurSummary.set_skip_reference_map ~define_name !OurDomain.our_model;
  );

  (* Reference.Set.iter !OurDomain.skip_reference_set ~f:(fun ref -> Log.dump "SKIP %a" Reference.pp ref); *)

  let init_time = Timer.stop_in_sec timer in

  let x = 
    if String.equal mode "preprocess" then (
      TypeCheckPre.check_define_by_name
      ~global_environment
      ~dependency
      define_name
    ) (* else if String.equal mode "filter" then (
      TypeCheckPost.check_define_by_name
      ~global_environment
      ~dependency
      define_name
    ) *)
    else
      TypeCheck.check_define_by_name
      ~type_check_controls
      ~call_graph_builder
      ~global_environment
      ~dependency
      ~entry_arg_types:OurDomain.ArgTypes.empty
      define_name
  in

  let analysis_time = Timer.stop_in_sec timer in

  let _ = init_time, analysis_time in 

  (* if Float.(>.) analysis_time 0.5 then (
    Log.dump ">>> %a (%.3f => %.3f)" Reference.pp define_name init_time analysis_time;
    (* Log.dump "START \n%a\nEnd" OurDomain.OurSummary.pp !Context.our_summary; *)
  ); *)

  (* Log.dump "End %a" Reference.pp define_name; *)
  (*
  let mode = OurDomain.load_mode () in
  let x = 
  if OurDomain.is_search_mode mode then
    TypeCheck.search_define_by_name
      ~type_check_controls
      ~call_graph_builder
      ~global_environment
      ~dependency
      define_name
  else if OurDomain.is_inference_mode mode then (
    (if OurDomain.is_func_model_exist () then () else (
    OurDomain.save_summary OurDomain.OurSummary.empty define_name));
    (*OurTypeSet.load_global_summary_cache ();*)
    let x = TypeCheck.check_define_by_name
      ~type_check_controls
      ~call_graph_builder
      ~global_environment
      ~dependency
      define_name
    in
    (*OurTypeSet.save_summary !OurTypeSet.our_model define_name;*)
    x
  )
  else
    (
    TypeCheck.check_define_by_name_origin
          ~type_check_controls
          ~call_graph_builder
          ~global_environment
          ~dependency
          define_name
    )
  in
  *)

  x

(* module CheckResultsTable = Environment.EnvironmentTable.WithCache (struct
  module PreviousEnvironment = AnnotatedGlobalEnvironment
  module Key = SharedMemoryKeys.ReferenceArgTypesKey
  module Value = CheckResultValue

  type trigger = OurDomain.ArgTypesKey.t
  [@@deriving sexp, compare]

  module TriggerSet = Set.Make (OurDomain.ArgTypesKey)

  let convert_trigger = Fn.id

  let key_to_trigger = Fn.id

  let show_key = OurDomain.ArgTypesKey.show

  let overlay_owns_key module_tracker_overlay key =
    let reference, _ = key in
    ModuleTracker.Overlay.owns_reference module_tracker_overlay reference

  let lazy_incremental = false

  let produce_value = produce_check_results

  let filter_upstream_dependency = function
    | SharedMemoryKeys.OurTypeCheckDefine name -> Some name
    | _ -> None


  let trigger_to_dependency name = SharedMemoryKeys.OurTypeCheckDefine name

  let equal_value = CheckResultValue.equal
end) *)

module CheckResultsTable = Environment.EnvironmentTable.WithCache (struct
  module PreviousEnvironment = AnnotatedGlobalEnvironment
  module Key = SharedMemoryKeys.ReferenceKey
  module Value = CheckResultValue

  type trigger = Reference.t [@@deriving sexp, compare]

  module TriggerSet = Reference.Set

  let convert_trigger = Fn.id

  let key_to_trigger = Fn.id

  let show_key = Reference.show

  let overlay_owns_key module_tracker_overlay =
    ModuleTracker.Overlay.owns_reference module_tracker_overlay

  let lazy_incremental = false

  let produce_value environment trigger = 
      produce_check_results environment trigger

  let filter_upstream_dependency = function
    | SharedMemoryKeys.TypeCheckDefine name -> Some name
    | _ -> None


  let trigger_to_dependency name = SharedMemoryKeys.TypeCheckDefine name

  let equal_value = CheckResultValue.equal
end)

include CheckResultsTable

let global_environment = CheckResultsTable.Unsafe.upstream

let module_tracker type_environment =
  ast_environment type_environment |> AstEnvironment.module_tracker


let populate_for_definitions ~scheduler environment defines =
  let timer = Timer.start () in
  let read_only = read_only environment in
  let number_of_defines = List.length defines in
  Log.info "Checking %d functions..." number_of_defines;
  let map _ names =
    let analyze_define number_defines name =
      (*
      let t = ReadOnly.get read_only name in
      (match t with
      | Some t ->
        let errors = TypeCheck.CheckResult.errors t in
        List.iter (Option.value errors ~default:[]) ~f:(fun e -> Log.dump "In HERE! : %a" Error.pp e)
      | _ -> ());
      *)
      
      let () = ReadOnly.add read_only name |> ignore in
      number_defines + 1
    in
    let x = List.fold names ~init:0 ~f:analyze_define in
    x
  in

  let reduce left right =
    let number_defines = left + right in
    Log.log ~section:`Progress "Processed %d of %d functions" number_defines number_of_defines;
    number_defines
  in

  let minimum_chunk_size =
    Int.max 10 (number_of_defines / 12 / 50)
  in

  let preferred_chunk_size =
    Int.max 100 (number_of_defines / 12)
  in

  let _ =
    SharedMemoryKeys.DependencyKey.Registry.collected_map_reduce
      scheduler
      ~policy:
        (Scheduler.Policy.fixed_chunk_size
           ~minimum_chunk_size
           ~minimum_chunks_per_worker:2
           ~preferred_chunk_size
           ())
      ~initial:0
      ~map
      ~reduce
      ~inputs:defines
      ()
  in

  (* let _ =
    SharedMemoryKeys.DependencyKey.Registry.collected_map_reduce
      scheduler
      ~policy:
        (Scheduler.Policy.fixed_chunk_size
           ~minimum_chunk_size:10
           ~minimum_chunks_per_worker:2
           ~preferred_chunk_size:100
           ())
      ~initial:0
      ~map
      ~reduce
      ~inputs:defines
      ()
  in *)

  Statistics.performance ~name:"check_TypeCheck" ~phase_name:"Type check" ~timer ()


let populate_for_modules ~scheduler ?type_join ?(skip_set=Reference.Set.empty) environment qualifiers =

  let timer = Timer.start () in

  Profiling.track_shared_memory_usage ~name:"Before legacy type check" ();
  let our_model = !OurDomain.our_model in
  let all_defines = !OurDomain.all_defines in

  let all_defines =
    if List.is_empty all_defines then (
      let all_defines = 
        let unannotated_global_environment =
          global_environment environment
          |> AnnotatedGlobalEnvironment.read_only
          |> AnnotatedGlobalEnvironment.ReadOnly.unannotated_global_environment
        in

        let map _ qualifiers =
          List.concat_map qualifiers ~f:(fun qualifier ->
              UnannotatedGlobalEnvironment.ReadOnly.get_define_names
                unannotated_global_environment
                qualifier)
        in
        Scheduler.map_reduce
          scheduler
          ~policy:
            (Scheduler.Policy.fixed_chunk_count
              ~minimum_chunks_per_worker:1
              ~minimum_chunk_size:100
              ~preferred_chunks_per_worker:5
              ())
          ~initial:[]
          ~map
          ~reduce:List.append
          ~inputs:qualifiers
          ()
        
      in
      OurDomain.all_defines := all_defines;
      all_defines
    )
    else
      all_defines
  in

  let time = Timer.stop_in_sec timer in
  Log.dump "Found %d functions in %f seconds" (List.length all_defines) time;
  (* List.iter qualifiers ~f:(fun q -> Log.dump "Qual : %a" Reference.pp q); *)
  

  let mode = OurDomain.load_mode () in
  if !OurDomain.is_first || String.equal mode "error" || String.equal mode "filter" || String.equal mode "recheck" || (String.equal mode "last_inference") then
    List.iter all_defines ~f:(fun define -> 
     OurDomain.OurSummary.change_analysis_of_func our_model define
     );

    (* List.iter all_defines ~f:(fun t -> Log.dump "GO %a" Reference.pp t); *)

  let filter_test_defines =
    if String.equal mode "check_preprocess" || String.equal mode "preprocess" || (String.equal mode "inference" && !OurDomain.is_first) then
    (
      List.filter all_defines ~f:(fun name ->
        let flag =
        (* (not (String.is_substring ~substring:"sympy." (Reference.show name))) &&
        (not (String.is_substring ~substring:"Lib." (Reference.show name))) && *)
        (* (not (Reference.is_test name)) && *)
        (not (Reference.is_just_check name))
        in

        (* Log.dump "%a ==> %b" Reference.pp name flag; *)

        flag
      )
    )
      
    else
      List.filter all_defines ~f:(fun name ->
        let _ = name in
        let flag = 
        (not (Reference.is_test name)) &&
        (not (Reference.is_just_check name))
        in

        (* Log.dump "%a ==> %b" Reference.pp name flag; *)

        flag
      )
      
  in

  (* Log.dump "OKOK %i => %i" (List.length all_defines) (List.length filter_test_defines); *)

  let filter_test_defines =
    List.filter filter_test_defines ~f:(fun name ->
      not ((String.is_substring ~substring:"sympy." (Reference.show name)) && (
        (String.is_substring ~substring:"miscellaneous" (Reference.show name)) ||
        (String.is_substring ~substring:"benchmarks" (Reference.show name)) ||
        (String.is_substring ~substring:"rubi" (Reference.show name)) ||
        (String.is_substring ~substring:"hyperexpand" (Reference.show name))
      ))
    )
  in

  let filter_test_defines =
    List.filter filter_test_defines ~f:(fun name ->
      not ((String.is_substring ~substring:"Lib." (Reference.show name)) && (
        (String.is_substring ~substring:"etree" (Reference.show name)) ||
        (Reference.is_test name)
      ))
    )
  in
  (* List.iter filter_test_defines ~f:(fun t -> Log.dump "GO %a" Reference.pp t); *)

  let filtered_defines =
    List.filter filter_test_defines ~f:(fun name ->
      not (Reference.Set.exists skip_set ~f:(Reference.equal name))
    )
    (* |> List.fold ~init:[] ~f:(fun acc define -> 
      let arg_types = OurDomain.OurSummary.get_analysis_arg_types !OurDomain.our_model define in
      let arg_types =
        if !OurDomain.is_first then [ OurDomain.ArgTypes.empty; ] else arg_types
      in
      List.map arg_types ~f:(fun arg_type -> OurDomain.ArgTypesKey.to_key define arg_type) @ acc
    ) *)
  in

  let filtered_defines =
    if String.equal mode "recheck" then (
      let recheck_info = OurDomain.OurSummary.get_recheck_info our_model in
      List.filter filtered_defines ~f:(fun name ->
        Reference.Map.mem recheck_info name
      )
    ) else (
      filtered_defines
    )
  in

  (* Log.dump "OKOK %i => %i" (List.length all_defines) (List.length filtered_defines); *)

  (*
  if List.length filtered_defines < 20 then
    List.iter filtered_defines ~f:(fun r -> Log.dump "Analysis: %a" Reference.pp r);
  *)
  (* let prev_temp_class_var_type = OurDomain.OurSummary.get_temp_class_var_type our_model in *)

  populate_for_definitions ~scheduler environment filtered_defines;

  let time = Timer.stop_in_sec timer in
  Log.dump "Type checking took %f seconds" time;

  OurDomain.OurSummary.set_all_join_temp_class_var_type_to_empty our_model;
  let _ = type_join in
  
  let prev_model = !OurDomain.our_model in
  let _ = prev_model in

  
  (* if (!OurDomain.is_first) && not (String.equal mode "preprocess") then (
    (* Log.dump "INIT"; *)
    OurDomain.our_model := OurDomain.OurSummary.set_all_class_var_type_to_empty our_model;
    (* Log.dump "%a" OurDomain.OurSummary.pp !OurDomain.our_model;
    Log.dump "%a" OurDomain.OurSummary.pp prev_model *)
    ()
  )
  else
    (); *)

  
  (* Log.dump "FINISH!!"; *)
  (* if (String.equal mode "error") then (
    (* Analysis.OurDomain.OurSummary.update_unseen_temp_class_var_type_to_unknown !Analysis.OurDomain.our_model; *)
    OurDomain.OurSummary.update_unseen_temp_class_var_type_to_var !OurDomain.our_model;
  ); *)
  
  if String.equal mode "preprocess" then (
    (* Log.dump "%a" OurDomain.OurSummary.pp !OurDomain.our_model; *)
    List.iter all_defines ~f:(fun define -> OurDomain.OurSummary.change_analysis_of_func our_model define)
  ) 
  else (
    List.iter filtered_defines ~f:(fun define -> OurDomain.OurSummary.change_analysis_to_false_of_func our_model define);

  );

  

  let read_only = read_only environment in
  (
  match type_join with
  | Some type_join ->
    

    let updated_vars, our_errors =
      List.fold filtered_defines ~init:(Reference.Map.empty, !OurErrorDomain.our_errors) ~f:(fun (updated_vars, our_errors) define ->
        let timer = Timer.start () in
        let _ = timer in
        let result = ReadOnly.get read_only define in
        (* let define, _ =  OurDomain.ArgTypesKey.from_key arg_types_key in *)
        let updated_vars, our_errors = 
        (match result with
        | Some t when String.equal mode "check_preprocess" ->
          let cur_summary = OurDomain.OurSummary.t_of_sexp (TypeCheck.CheckResult.our_summary t) in
          let our_model = !OurDomain.our_model in
          OurDomain.OurSummary.update_check_preprocess ~define ~type_join ~prev:cur_summary our_model;

          updated_vars, our_errors
        | Some t when String.equal mode "preprocess" ->
          let cur_summary = OurDomain.OurSummary.t_of_sexp (TypeCheck.CheckResult.our_summary t) in
          let expression_map = OurDomain.OurSummary.get_preprocess cur_summary define in
          let unique_analysis = OurDomain.OurSummary.get_unique_analysis cur_summary define in
          OurDomain.ExpressionMap.iteri expression_map ~f:(fun ~key ~data -> 
            OurDomain.OurSummary.set_preprocess our_model define key data
          );
          let our_model = !OurDomain.our_model in
          (* OurDomain.OurSummary.set_usage_attributes our_model define AttributeAnalysis.AttributeStorage.empty; *)
          OurDomain.OurSummary.set_unique_analysis our_model define unique_analysis;
          updated_vars, our_errors
        | Some t when String.equal mode "error" || String.equal mode "recheck" ->
          let errors = TypeCheck.CheckResult.errors t |> Option.value ~default:[] in
          let global_environment =
            global_environment environment
            |> AnnotatedGlobalEnvironment.read_only
          in
          let unannotated_global_environment =
            global_environment
            |> AnnotatedGlobalEnvironment.ReadOnly.unannotated_global_environment
          in

          let global_resolution = GlobalResolution.create global_environment in

          let ast_environment = UnannotatedGlobalEnvironment.ReadOnly.ast_environment unannotated_global_environment in
          let ignore_lines =
            let function_definition = 
              GlobalResolution.function_definition global_resolution define
            in

            (match function_definition with
            | Some { FunctionDefinition.qualifier; _ } ->
              AstEnvironment.ReadOnly.get_raw_source ast_environment qualifier
              |> (function
              | Some (Result.Ok source) -> 
                Source.ignore_lines source
              | _ -> []
              )
            | _ -> []
            )

            
          in
          let our_errors = OurErrorDomain.OurErrorList.add ~join:type_join ~errors ~ignore_lines our_errors in
          Reference.Map.empty, our_errors

        | Some t -> 
          let cur_summary = OurDomain.OurSummary.t_of_sexp (TypeCheck.CheckResult.our_summary t) in

          let class_vars = OurDomain.OurSummary.get_class_vars cur_summary in

          

            (* if String.equal (Reference.show define) "homeassistant.helpers.entity_component.EntityComponent.async_add_entity"
              then (
                Log.dump "OK! \n %a" OurDomain.OurSummary.pp cur_summary;
               (*  List.iter errors ~f:(fun e -> Log.dump "[[ TEST ]]] \n%a" Error.pp e) *)
              );

            if String.equal (Reference.show define) "salt.state.State.call"
              then (
                Log.dump "OK! \n %a" OurDomain.OurSummary.pp cur_summary;
                (*  List.iter errors ~f:(fun e -> Log.dump "[[ TEST ]]] \n%a" Error.pp e) *)
              ); *)
          
          
            (* OurDomain.OurSummary.set_callers our_model define (OurDomain.OurSummary.get_callers cur_summary define);

            OurDomain.OurSummary.set_usage_attributes our_model define (OurDomain.OurSummary.get_usage_attributes_from_func cur_summary define); *)
            (* if String.is_substring (Reference.show define) ~substring:"sklearn.model_selection._split.check_cv"
              then (
                (* Log.dump "OK! \n %a" OurDomain.OurSummary.pp our_model; *)
                OurDomain.debug := true
               (*  List.iter errors ~f:(fun e -> Log.dump "[[ TEST ]]] \n%a" Error.pp e) *)
              ); *)

          let our_model = !OurDomain.our_model in
          OurDomain.OurSummary.update ~type_join ~prev:cur_summary our_model;

          (* if String.is_substring (Reference.show define) ~substring:"sklearn.model_selection._split.check_cv"
            then (
              (* Log.dump "OK! \n %a" OurDomain.OurSummary.pp cur_model; *)
              Log.dump "OK! \n %a" OurDomain.OurSummary.pp our_model;
              OurDomain.debug := false
             (*  List.iter errors ~f:(fun e -> Log.dump "[[ TEST ]]] \n%a" Error.pp e) *)
            ); *)

          let updated_vars = Reference.Map.merge updated_vars class_vars ~f:(fun ~key:_ data -> 
            match data with
            | `Both (a, b) -> Some (Reference.Set.union a b)
            | `Left a | `Right a -> Some a
          )
          in
          (* Log.dump ">>> %a" OurDomain.OurSummary.pp cur_summary; *)
           (* if String.is_substring (Reference.show define) ~substring:"salt.states.smartos._parse_vmconfig"
            then (
              Log.dump ">>> %a" OurDomain.OurSummary.pp cur_summary;
            ); *)
            
          (* if String.is_substring (Reference.show define) ~substring:"entity_component.EntityComponent"
            then (
              Log.dump ">>> %a" OurDomain.OurSummary.pp cur_summary;
            ); *)

            (* if String.is_substring (Reference.show define) ~substring:"ZabbixMultipleHostTriggerCountSensor.__init__"
              then (
                Log.dump "%a >>> %a" Reference.pp define OurDomain.OurSummary.pp cur_summary;
                List.iter errors ~f:(fun e -> Log.dump "Error : %a" Error.pp e);
              ); *)

            (* if String.is_substring (Reference.show define) ~substring:"_write_col_header"
              then (
                Log.dump ">>> %a" OurDomain.OurSummary.pp cur_summary;
                List.iter errors ~f:(fun e -> Log.dump "Error : %a" Error.pp e);
              ); *)

            (* if String.is_substring (Reference.show define) ~substring:"pandas.core.indexes.multi.MultiIndex.format"
              then (
                Log.dump ">>> %a" OurDomain.OurSummary.pp cur_summary;
              ); *)

            (* if String.is_substring (Reference.show define) ~substring:"get_level_lengths"
              then (
                Log.dump ">>> %a" OurDomain.OurSummary.pp cur_summary;
              ); *)

          (* if String.equal (Reference.show define) "pandas.util._decorators.make_signature"
          then (
            Log.dump ">>> %a" OurDomain.OurSummary.pp cur_summary;
            List.iter errors ~f:(fun e -> Log.dump "Error : %a" Error.pp e);
          );

          if String.equal (Reference.show define) "pandas.compat.signature"
            then (
              Log.dump ">>> %a" OurDomain.OurSummary.pp cur_summary;
              List.iter errors ~f:(fun e -> Log.dump "Error : %a" Error.pp e);
          ); *)

          (* let total_time = Timer.stop_in_sec timer in *)
          (* if Float.(>.) total_time 0.1 then (
            (* Log.dump "Start\n%a\nEnd" OurDomain.OurSummary.pp cur_summary; *)
            Log.dump "OKOK %a %.3f" Reference.pp define total_time;
          );   *)
          
          updated_vars, our_errors
        | _ -> updated_vars, our_errors
        )
        in
        
        updated_vars, our_errors
      )
    in

    (* Reference.Map.iteri updated_vars ~f:(fun ~key ~data:_ -> Log.dump "UPDATE %a" Reference.pp key);
    Log.dump ">>> %a" OurDomain.OurSummary.pp !OurDomain.our_model; *)

    (* Log.dump "%a" OurDomain.OurSummary.pp !OurDomain.our_model; *)
    let _ = updated_vars in

    if (String.equal mode "inference") || (String.equal mode "last_inference") then (
      OurDomain.OurSummary.update_unseen_temp_class_var_type ~type_join ~updated_vars !OurDomain.our_model;
    );
    if not (String.equal mode "preprocess") then (
      OurDomain.OurSummary.set_all_temp_class_var_type_from_join !OurDomain.our_model;
    );


    (* For Baseline => update all *)
    if !OurDomain.baseline || true then (
      OurDomain.OurSummary.update_unseen_temp_class_var_type ~type_join ~updated_vars:Reference.Map.empty !OurDomain.our_model;
    );

    
    
    let _ = OurDomain.OurSummary.update_default_value in
    (* if (!OurDomain.is_first) && not (String.equal mode "preprocess") then  (
      
      OurDomain.OurSummary.update_default_value ~prev:prev_model !OurDomain.our_model;
      (* Log.dump "%a" OurDomain.OurSummary.pp !OurDomain.our_model; *)
    ); *)

    
    (* OurDomain.our_model := our_summary; *)
    if String.equal mode "error" then
      OurErrorDomain.our_errors := our_errors;
    ()
  | _ -> Log.dump "No Join"
  )
  ;
  (* let functions_list = OurDomain.OurSummary.get_functions_of_class our_model in
  OurErrorDomain.our_errors := List.fold functions_list ~init:!OurErrorDomain.our_errors ~f:(fun our_errors functions -> OurErrorDomain.OurErrorList.get_repeated_errors our_errors functions);
 *)
  Statistics.event
    ~section:`Memory
    ~name:"shared memory size post-typecheck"
    ~integers:["size", Memory.heap_size ()]
    ();
  Profiling.track_shared_memory_usage ~name:"After legacy type check" ()




let populate_for_project_modules ~scheduler ?type_join ?(skip_set=Reference.Set.empty) environment =
  let project_qualifiers =
    module_tracker environment
    |> ModuleTracker.read_only
    |> ModuleTracker.ReadOnly.project_qualifiers
  in
  populate_for_modules ~scheduler ?type_join ~skip_set environment project_qualifiers;
  



module ReadOnly = struct
  include CheckResultsTable.ReadOnly

  let global_environment = CheckResultsTable.Testing.ReadOnly.upstream

  let global_resolution environment = global_environment environment |> GlobalResolution.create

  let ast_environment environment =
    unannotated_global_environment environment
    |> UnannotatedGlobalEnvironment.ReadOnly.ast_environment


  let module_tracker environment =
    ast_environment environment |> AstEnvironment.ReadOnly.module_tracker

    (*
  let get_our_summary environment ?dependency reference =
    let x = get ?dependency environment reference in
    match x with
    | Some x ->
      TypeCheck.CheckResult.our_summary x
    | _ -> OurDomain.OurSummary.empty
    *)

  let get_errors environment ?dependency reference =
    (* let reference = OurDomain.ArgTypesKey.to_key reference OurDomain.ArgTypes.empty in *)
    let x = get ?dependency environment reference in
    x >>= TypeCheck.CheckResult.errors
    |> Option.value ~default:[]


  let get_local_annotations environment ?dependency reference =
    (* let reference = OurDomain.ArgTypesKey.to_key reference OurDomain.ArgTypes.empty in *)
    let x = get ?dependency environment reference in 
    x >>= TypeCheck.CheckResult.local_annotations


  let get_or_recompute_local_annotations environment name =
    let x= get_local_annotations environment name in
    let name = OurDomain.ArgTypesKey.to_key name OurDomain.ArgTypes.empty in
    match x with
    | Some _ as local_annotations -> local_annotations
    | None ->
        (* Local annotations not preserved in shared memory in a standard pyre server (they can be,
           via TypeEnvironment.LocalAnnotations, but to save memory we only populate this for pysa
           runs, not the normal server used by LSP). This behavior is controlled by the
           `store_type_check_resolution` flag. *)
        let global_environment = global_environment environment in
        TypeCheck.compute_local_annotations ~global_environment name
end

(* All SharedMemory tables are populated and stored in separate, imperative steps that must be run
   before loading / after storing. These functions only handle serializing and deserializing the
   non-SharedMemory data *)

let store environment =
  CheckResultsTable.store environment;
  SharedMemoryKeys.DependencyKey.Registry.store ()


let load configuration =
  (* Loading the dependency keys needs to happen exactly once in the environment stack; we do it
     here, at the very top. *)
  SharedMemoryKeys.DependencyKey.Registry.load ();
  CheckResultsTable.load configuration


module TypeEnvironmentReadOnly = ReadOnly
