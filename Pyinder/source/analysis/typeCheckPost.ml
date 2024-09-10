open Core
open Pyre
open Ast
open Ast.Util
open Expression
open Statement

module OurSummaryResolution = OurTypeSet.OurSummaryResolution
module OurSummary = OurDomain.OurSummary
module StatementDefine = Define
module Error = AnalysisError
module CheckResult = TypeCheck.CheckResult
module DummyContext = TypeCheck.DummyContext

let preprocess ~our_model ~global_resolution define =
  let { Node.value = { Define.signature = { Define.Signature.name; Define.Signature.parent; parameters; _ }; _ }; _ } =
    define
  in

  (* let timer = Timer.start () in *)
  
  let final_model = !OurDomain.our_model in

  (* Log.dump ">>> %a" OurDomain.OurSummary.pp final_model; *)
  
  if !OurDomain.on_attribute then (

    let func_attrs = 
      
      let parameter_usage_attributes =
        OurDomain.OurSummary.get_usage_attributes_from_func final_model name
      in

      

      let successors = GlobalResolution.successors ~resolution:global_resolution in

      let parent_usage_attributes = AttributeAnalysis.AttributeStorage.empty in

      (match parent, List.nth parameters 0 with
      | Some class_name, Some { Node.value={ Parameter.name=class_param; _ }; _ } ->
        let rec get_parent_usage_attributes class_name parent_usage_attributes =
          (* 부모 클래스 계속 순회하면서 attributes 업데이트 *)
          let parent_usage_attributes =
            OurDomain.OurSummary.get_usage_attributes_from_class final_model class_name
            |> AttributeAnalysis.AttributeStorage.join parent_usage_attributes
          in
          let class_summary = GlobalResolution.class_summary global_resolution (Type.Primitive (Reference.show class_name)) in
          (match class_summary with
          | Some { Node.value = class_summary; _ } ->
            List.fold ~init:parent_usage_attributes (ClassSummary.base_classes class_summary) 
              ~f:(fun parent_usage_attributes { Node.value = parent_class_exp; _ }  ->
                match parent_class_exp with
                | Name name ->
                  let class_name = name_to_reference name |> Option.value ~default:Reference.empty in
                  get_parent_usage_attributes class_name parent_usage_attributes
                | _ -> parent_usage_attributes
              )
          | _ -> parent_usage_attributes
          )
        in

        let parent_usage_attributes =
          get_parent_usage_attributes class_name parent_usage_attributes
          |> AttributeAnalysis.AttributeStorage.add_prefix ~prefix:(Reference.create class_param)
        in

        let total_usage_attributes = 
          AttributeAnalysis.AttributeStorage.join parameter_usage_attributes parent_usage_attributes 
          |>  AttributeAnalysis.AttributeStorage.filter_single_class_param ~class_param
          |> AttributeAnalysis.AttributeStorage.filter_higher_items
        in

        (* Log.dump "Name : %a ===> \n %a" Reference.pp name AttributeAnalysis.AttributeStorage.pp total_usage_attributes; *)

        
        (* if String.is_substring (Reference.show name) ~substring:"homeassistant.helpers.entity_component.EntityComponent.async_add_entity" then
          Log.dump "Name : %a ===> \n %a" Reference.pp name AttributeAnalysis.AttributeStorage.pp total_usage_attributes; *)

        (* let info_time = Timer.stop_in_sec timer in *)

        let x =
        OurTypeSet.OurSummaryResolution.find_class_of_attributes ~successors final_model name total_usage_attributes
        in

        (* let infer_time = Timer.stop_in_sec timer in *)

        (* if Float.(>.) infer_time 0.1 then
          Log.dump "Infer time : %.3f" info_time infer_time; *)

        x
      | _ -> OurTypeSet.OurSummaryResolution.find_class_of_attributes ~successors final_model name parameter_usage_attributes
      )
    in  

    

    (* if String.is_substring (Reference.show name) ~substring:"homeassistant.helpers.entity_component.EntityComponent.async_add_entity" then
      (
        LocInsensitiveExpMap.iteri func_attrs ~f:(fun ~key ~data -> 
          let duck_type = 
            List.map data ~f:(fun d -> Type.Primitive (Reference.show d))
            |> Type.union
          in
          Log.dump "Expression %a ==> %a" Expression.pp key Type.pp duck_type;  
        )
      ); *)

    (* if (LocInsensitiveExpMap.length func_attrs) > 0 then
      Log.dump "ATTR NUM >>> %i" (LocInsensitiveExpMap.length func_attrs); *)

    LocInsensitiveExpMap.iteri func_attrs ~f:(fun ~key:({ Node.value; _ } as expression) ~data ->
      match value with
      | Expression.Name _ ->
        let duck_type = 
          List.map data ~f:(fun d -> Type.Primitive (Reference.show d))
          |> Type.union
        in
        (* Log.dump "Name : %a ===> %a (%a)" Expression.pp_expression value Type.pp duck_type Reference.pp name; *)
        (* if String.is_substring (Reference.show name) ~substring:"capabilities.AlexaCapability" then
          Log.dump "RESULT Name : %a ===> %a (%a)" Expression.pp_expression value Type.pp duck_type Reference.pp name;

        if String.is_substring (Reference.show name) ~substring:"EntityComponent" then
          Log.dump "RESULT Name : %a ===> %a (%a)" Expression.pp_expression value Type.pp duck_type Reference.pp name;
          *)

          (* if String.is_substring (Reference.show name) ~substring:"modules.state.show_states" then
          Log.dump "RESULT Name : %a ===> %a (%a)" Expression.pp_expression value Type.pp duck_type Reference.pp name; *)
          (* Log.dump "RESULT Name : %a ===> %a (%a)" Expression.pp_expression value Type.pp duck_type Reference.pp name; *)

        OurDomain.OurSummary.set_preprocess our_model name expression duck_type
      | _ -> ()
    );
  );
  let { Node.value = { Define.signature = { Define.Signature.name; _ }; _ } as define; _ } = define in

  let cfg = Cfg.create define in
  let fixpoint = UniqueAnalysis.UniqueStruct.forward ~cfg ~initial:UniqueAnalysis.UniqueState.bottom in

  OurDomain.OurSummary.set_unique_analysis our_model name fixpoint;

  our_model

let check_define
    ~our_model
    ~global_resolution
    define_node
  =
  let our_summary = preprocess ~our_model ~global_resolution define_node in
  let errors = None in
  let local_annotations = None in
  (our_summary, errors, local_annotations)

let check_function_definition
    ~global_resolution
    ~name

    { FunctionDefinition.body; siblings; _ }
  =
  let timer = Timer.start () in
  let our_model = OurDomain.OurSummary.empty () in
  let check_define = check_define ~our_model ~global_resolution in
  let sibling_bodies = List.map siblings ~f:(fun { FunctionDefinition.Sibling.body; _ } -> body) in
  let sibling_results = List.map sibling_bodies ~f:(fun define_node -> let x = check_define define_node in x) in
  let result =
    let aggregate_errors results =
      List.map results ~f:(fun (_, errors, _) -> errors)
      |> List.fold ~init:(Some []) ~f:(Option.map2 ~f:List.append)
    in
    let aggregate_our_summary results =
      List.map results ~f:(fun (our_summary, _, _) -> our_summary)
      |> List.iter ~f:(fun our_summary ->
          OurDomain.OurSummary.join ~type_join:(GlobalResolution.join global_resolution) our_summary our_model
        )
    in

    

    match body with
    | None -> aggregate_our_summary sibling_results;
      
      { CheckResult.our_summary = OurDomain.OurSummary.sexp_of_t our_model; errors = aggregate_errors sibling_results; local_annotations = None; }
    | Some define_node ->
      
        let ((our_summary, _, local_annotations) as body_result) = check_define define_node in
        { CheckResult.our_summary = OurDomain.OurSummary.sexp_of_t our_summary; errors = aggregate_errors (body_result :: sibling_results); local_annotations; }
  in

  let number_of_lines =
    let bodies =
      match body with
      | None -> sibling_bodies
      | Some body -> body :: sibling_bodies
    in
    List.fold bodies ~init:0 ~f:(fun sofar body -> sofar + Node.number_of_lines body)
  in
  Statistics.performance
    ~flush:false
    ~randomly_log_every:1000
    ~section:`Check
    ~name:"SingleDefineTypeCheck"
    ~timer
    ~normals:["name", Reference.show name; "request kind", "SingleDefineTypeCheck"]
    ~integers:["number of lines", number_of_lines]
    ();
  result
(*
let check_define_by_name_origin
    ~type_check_controls
    ~call_graph_builder
    ~global_environment
    ~dependency
    name
  =
  let global_resolution = GlobalResolution.create global_environment ?dependency in
  (* TODO(T65923817): Eliminate the need of creating a dummy context here *)
  let resolution = resolution global_resolution (module DummyContext) in
  GlobalResolution.function_definition global_resolution name
  >>| check_function_definition_origin ~type_check_controls ~call_graph_builder ~resolution ~name
*)
let check_define_by_name
    ~global_environment
    ~dependency
    name
  =
  (*Log.dump ">>> %a" Reference.pp name;*)
  let global_resolution = GlobalResolution.create global_environment ?dependency in
  (* TODO(T65923817): Eliminate the need of creating a dummy context here *)
  GlobalResolution.function_definition global_resolution name
  >>| check_function_definition ~global_resolution ~name
