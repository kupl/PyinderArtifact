(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Core
open Ast
open Pyre

module Stmt = Statement.Statement
module Class = Statement.Class
module Define = Statement.Define


module type PossibleState = sig
  type t [@@deriving show]

  (*
  val top_to_bottom : t -> t
  
  val set_possibleconditions : t -> t -> t

  val update_possible : t -> t -> Reference.t -> t
  *)
  val is_reachable : t -> bool

  val get_resolution : t -> Resolution.t option

  val bottom : t

  val less_or_equal : left:t -> right:t -> bool

  val join : t -> t -> t

  val widen : previous:t -> next:t -> iteration:int -> t

  (*
  val join_possible : t -> t -> t

  val widen_possible : previous:t -> next:t -> iteration:int -> t
  *)

  val forward : statement_key:int -> context:AstContext.t -> t -> statement:Statement.t -> t

  val backward : statement_key:int -> t -> statement:Statement.t -> t
end

module type PossibleFixpoint = sig
  type state

  type t = {
    preconditions: state Int.Table.t;
    postconditions: state Int.Table.t;
  }
  [@@deriving show]

  val entry : t -> state option

  val normal_exit : t -> state option

  val exit : t -> state option

  val post_info : t -> (Resolution.t option * Resolution.t option) Int.Map.t

  (*
  val exit_possible : t -> state option
  *)
  val forward : cfg:Cfg.t -> initial:state -> Reference.t -> t

  val backward : cfg:Cfg.t -> initial:state -> t

  val equal : f:(state -> state -> bool) -> t -> t -> bool
end

module Make (State : PossibleState) = struct
  type state = State.t


  type t = {
    preconditions: State.t Int.Table.t;
    postconditions: State.t Int.Table.t;
    (*possibleconditions : State.t Int.Table.t;*)
  }

  let equal ~f left right =
    Core.Hashtbl.equal f left.preconditions right.preconditions
    && Core.Hashtbl.equal f left.postconditions right.postconditions


  let pp format { preconditions; postconditions; _ } =
    let print_state ~name ~key ~data =
      Format.fprintf format "%s %d -> %a\n" name key State.pp data
    in
    Hashtbl.iteri preconditions ~f:(print_state ~name:"Precondition");
    Hashtbl.iteri postconditions ~f:(print_state ~name:"Postcondition");
    ()
    (*
    Hashtbl.iteri possibleconditions ~f:(print_state ~name:"Possiblecondition");
    let _ = possibleconditions in ()
    *)


  let show fixpoint = Format.asprintf "%a" pp fixpoint

  let entry { preconditions; _ } = Hashtbl.find preconditions Cfg.entry_index

  let normal_exit { postconditions; _ } = Hashtbl.find postconditions Cfg.normal_index

  let exit { postconditions; _ } = Hashtbl.find postconditions Cfg.exit_index

  let post_info { preconditions; postconditions; } =
    Hashtbl.fold preconditions ~init:Int.Map.empty ~f:(fun ~key ~data:precondition acc ->
      match State.get_resolution precondition with
      | Some precondition ->
        let postcondition = Hashtbl.find_exn postconditions key in
        (match State.get_resolution postcondition with
        | Some postcondition -> 
          Int.Map.set acc ~key ~data:(Some precondition, Some postcondition)
        | _ -> Int.Map.set acc ~key ~data:(Some precondition, None) (* (Refinement.Store.empty, Refinement.Store.empty) *)
        )
      | _ -> Int.Map.set acc ~key ~data:(None, None) (* (Refinement.Store.empty, Refinement.Store.empty) *)
    )
      (* match State.get_resolution postcondition with
      | Some postcondition ->
        let precondition = Hashtbl.find_exn preconditions key in
        (match State.get_resolution precondition with
        | Some precondition -> 
          Int.Map.set acc ~key ~data:(Some (precondition, postcondition))
        | _ -> Int.Map.set acc ~key ~data:None (* (Refinement.Store.empty, Refinement.Store.empty) *)
        )
      | _ -> Int.Map.set acc ~key ~data:None (* (Refinement.Store.empty, Refinement.Store.empty) *) *)
    
    (*
  let exit_possible { possibleconditions; _ } = Hashtbl.find possibleconditions Cfg.exit_index
    *)
  let our_compute_fixpoint cfg func_name ~initial_index ~initial ~predecessors ~successors ~transition =
    (*
     * This is the implementation of a monotonically increasing chaotic fixpoint
     * iteration sequence with widening over a control-flow graph (CFG) using the
     * recursive iteration strategy induced by a weak topological ordering of the
     * nodes in the control-flow graph. The recursive iteration strategy is
     * described in Bourdoncle's paper on weak topological orderings:
     *
     *   F. Bourdoncle. Efficient chaotic iteration strategies with widenings.
     *   In Formal Methods in Programming and Their Applications, pp 128-141.
     *)
    let _ = func_name in
    let components = WeakTopologicalOrder.create ~cfg ~entry_index:initial_index ~successors in

    let preconditions = Int.Table.create () in
    let postconditions = Int.Table.create () in
    (*
    let possibleconditions = Int.Table.create () in
    *)
    let context_initial = AstContext.define func_name in
    let contexts = Int.Table.create () in

    let class_hierachy = Hashtbl.create (module Reference) in
    let _ = class_hierachy in

    let join_with_predecessors_postconditions node state =
      
      if Int.equal (Cfg.Node.id node) initial_index then
        State.join state initial
      else
        predecessors node
        |> Set.fold ~init:state ~f:(fun sofar predecessor_index ->
               Hashtbl.find postconditions predecessor_index
               |> Option.value ~default:State.bottom
               (*|> State.top_to_bottom*)
               |> State.join sofar)
    in

    let propagate_context node state =
      successors node
      |> Set.iter ~f:(fun successor_index ->
          if Hashtbl.mem contexts successor_index
          then ()
          else Hashtbl.set contexts ~key:successor_index ~data:state 
        )
    in

    (*
    let join_with_predcessors_possibleconditions node state =
      if Int.equal (Cfg.Node.id node) initial_index then
        State.join state initial
      else
        predecessors node
        |> Set.fold ~init:state ~f:(fun sofar predecessor_index ->
              (*Log.dump "Join %i" predecessor_index;*)
              Hashtbl.find possibleconditions predecessor_index
              |> Option.value ~default:State.bottom
              |> State.join_possible sofar)
    in
    *)

    let analyze_node node =
      let node_id = Cfg.Node.id node in
      
      let timer = Timer.start () in
      let precondition =
        Hashtbl.find preconditions node_id
        |> Option.value ~default:State.bottom
        |> join_with_predecessors_postconditions node
      in

      let context = 
        if Int.equal (Cfg.Node.id node) initial_index
        then context_initial
        else Hashtbl.find_exn contexts node_id
      in

      (* let join_time = Timer.stop_in_sec timer in

      if Float.(>) join_time 0.5 then
        Log.dump "%.3f %a" join_time State.pp precondition; *)

      
      (*
      let prepossible = 
        Hashtbl.find preconditions node_id
        |> Option.value ~default:State.bottom
        |> join_with_predcessors_possibleconditions node
      in
      *)
     (*  if String.is_substring (Reference.show func_name) ~substring:"State.call"
        then (

        Log.dump "%s" (Format.asprintf "[ Node ]\n%a\n" Cfg.Node.pp node);
        
        Log.dump "%s" (Format.asprintf "[ Node Precondition ]\n%a\n" State.pp precondition);
        ); *)
     
      (*
      if Int.equal 3 (Cfg.Node.id node)
      then
        Log.dump "%s" (Format.asprintf "[ Node Precondition ]\n%a\n" State.pp precondition);
      *)
      (* let timer = Timer.start () in *)

      (* if String.is_substring (Reference.show func_name) ~substring:"test.ParserBase._should_parse_dates"
        then (
          Log.dump "START %a %i" Reference.pp func_name (Cfg.Node.id node);
          Log.dump "%a" Cfg.Node.pp node;
        ); *)

        (* Log.dump "%s" (Format.asprintf "[ Node ]\n%a\n" Cfg.Node.pp node);
        Log.dump "HMM %a" AstContext.pp context; *)

      AstContext.context := context;

      Hashtbl.set preconditions ~key:node_id ~data:precondition;
      let postcondition = transition ~context node_id precondition (Cfg.Node.statements node) in

      let context = AstContext.set_context context node in
      AstContext.context := AstContext.set_context context node;

      let trans_time = Timer.stop_in_sec timer in
      let _ = trans_time in

      (* if Float.(>) trans_time 1.0
        then (
          Log.dump "END %i" (Cfg.Node.id node);
          Log.dump "%a" Cfg.Node.pp node;
          Log.dump "%s" (Format.asprintf "[ Node Precondition ]\n%a\n" State.pp precondition);
          Log.dump "%s" (Format.asprintf "[ Node Postcondition ]\n%a\n" State.pp postcondition);
        ); *)

      (* if (* Float.(>) trans_time 2.0 && *) String.is_substring (Reference.show func_name) ~substring:"salt.client.LocalClient.pub"
        then (
          Log.dump "END %i" (Cfg.Node.id node);
          (* Log.dump "%a" Cfg.Node.pp node; *)
        ); *)
        (* if String.is_substring (Reference.show func_name) ~substring:"pandas.io.formats.html.HTMLFormatter._write_col_header" && (Int.equal (Cfg.Node.id node) 15)
          then (
        Log.dump "%s" (Format.asprintf "[ Node ]\n%a\n" Cfg.Node.pp node);
        Log.dump "%s" (Format.asprintf "[ Node Precondition ]\n%a\n" State.pp precondition);
        Log.dump "%s" (Format.asprintf "[ Node Postcondition ]\n%a\n" State.pp postcondition);
          ); *)

          (* Log.dump "%a" Cfg.Node.pp node;
          Log.dump "%s" (Format.asprintf "[ Node Precondition ]\n%a\n" State.pp precondition);
          Log.dump "%s" (Format.asprintf "[ Node Postcondition ]\n%a\n" State.pp postcondition); *)
      (*
      if Int.equal 3 (Cfg.Node.id node)
        then
      Log.dump "%s" (Format.asprintf "[ Node Postcondition ]\n%a\n" State.pp postcondition);
      *)
      (* if String.is_substring (Reference.show func_name) ~substring:"pandas.io.formats.html.HTMLFormatter._write_col_header"
        then (
      Log.dump "%s" (Format.asprintf "[ Node Postcondition ]\n%a\n" State.pp postcondition);
        ); *)
     
      Hashtbl.set postconditions ~key:node_id ~data:postcondition;
      
      propagate_context node context;
      (*
      (*Log.dump "%s" (Format.asprintf "[ Node Pre Possiblecondition ]\n%a\n" State.pp prepossible);*)
      let possiblecondition = State.set_possibleconditions precondition postcondition in
      (*Log.dump "%s" (Format.asprintf "[ Node Possiblecondition ]\n%a\n" State.pp possiblecondition);*)

      

      let possiblecondition = State.update_possible prepossible possiblecondition func_name in
      (*Log.dump "%s" (Format.asprintf "[ Node Update Possiblecondition ]\n%a\n" State.pp possiblecondition);*)
      Hashtbl.set possibleconditions ~key:node_id ~data:possiblecondition
      *)

    in
    let rec analyze_component = function
      | { WeakTopologicalOrder.Component.kind = Node node; _ } -> 
        analyze_node node
      | { kind = Cycle { head; components }; _ } ->
          (* Loop에 해당하는 거 같음 *)
          let head_id = Cfg.Node.id head in
          let rec iterate local_iteration =
            analyze_node head;
            List.iter ~f:analyze_component components;
            let current_head_precondition = Hashtbl.find_exn preconditions head_id in
            let new_head_precondition =
              join_with_predecessors_postconditions head current_head_precondition
            in
            let converged =
              State.less_or_equal ~left:new_head_precondition ~right:current_head_precondition
            in
            (*
            Log.dump
              "\n%a\n  { <= (result %b) (iteration = %d) }\n\n%a"
              State.pp
              new_head_precondition
              converged
              local_iteration
              State.pp
              current_head_precondition;
            *)
            (*
            Log.log
              ~section:`Fixpoint
              "\n%a\n  { <= (result %b) (iteration = %d) }\n\n%a"
              State.pp
              new_head_precondition
              converged
              local_iteration
              State.pp
              current_head_precondition;
              *)
            if not converged then (
              let precondition =
                State.widen
                  ~previous:current_head_precondition
                  ~next:new_head_precondition
                  ~iteration:local_iteration
              in
              Hashtbl.set preconditions ~key:head_id ~data:precondition;
              iterate (local_iteration + 1))
            else
              (* At this point, we know we have a local fixpoint.
               * Since operators are monotonic, `new_head_precondition` is also
               * a post fixpoint. This is basically the argument for performing
               * decreasing iteration sequence with a narrowing operator.
               * Therefore, `new_head_precondition` might be more precise,
               * let's use it at the result.
               *)
              Hashtbl.set preconditions ~key:head_id ~data:new_head_precondition
          in
          iterate 0
    in
    List.iter ~f:analyze_component components;

    (*
    Hashtbl.iteri class_hierachy ~f:(fun ~key:ref ~data:define_list -> 
      Format.printf "[Reference] \n %a \n" Reference.pp ref;
      Hashtbl.iteri define_list ~f:(fun ~key:define ~data:summary ->
        Format.printf "\n %a \n" Define.pp define;
        Format.printf "\n %a \n" Summary.pp summary;
      );
    );
    *)
    

    { preconditions; postconditions; }

  let compute_fixpoint cfg ~initial_index ~initial ~predecessors ~successors ~transition =
    (*
     * This is the implementation of a monotonically increasing chaotic fixpoint
     * iteration sequence with widening over a control-flow graph (CFG) using the
     * recursive iteration strategy induced by a weak topological ordering of the
     * nodes in the control-flow graph. The recursive iteration strategy is
     * described in Bourdoncle's paper on weak topological orderings:
     *
     *   F. Bourdoncle. Efficient chaotic iteration strategies with widenings.
     *   In Formal Methods in Programming and Their Applications, pp 128-141.
     *)
    let components = WeakTopologicalOrder.create ~cfg ~entry_index:initial_index ~successors in

    let preconditions = Int.Table.create () in
    let postconditions = Int.Table.create () in
    (*
    let possibleconditions = Int.Table.create () in
    *)
    let join_with_predecessors_postconditions node state =
      if Int.equal (Cfg.Node.id node) initial_index then
        State.join state initial
      else
        predecessors node
        |> Set.fold ~init:state ~f:(fun sofar predecessor_index ->
               Hashtbl.find postconditions predecessor_index
               |> Option.value ~default:State.bottom
               |> State.join sofar)
    in
    let analyze_node node =
      let node_id = Cfg.Node.id node in
      let precondition =
        Hashtbl.find preconditions node_id
        |> Option.value ~default:State.bottom
        |> join_with_predecessors_postconditions node
      in
      Hashtbl.set preconditions ~key:node_id ~data:precondition;
      let postcondition = transition node_id precondition (Cfg.Node.statements node) in
      Hashtbl.set postconditions ~key:node_id ~data:postcondition
    in
    let rec analyze_component = function
      | { WeakTopologicalOrder.Component.kind = Node node; _ } -> 
        analyze_node node
      | { kind = Cycle { head; components }; _ } ->
          let head_id = Cfg.Node.id head in
          let rec iterate local_iteration =
            analyze_node head;
            List.iter ~f:analyze_component components;
            let current_head_precondition = Hashtbl.find_exn preconditions head_id in
            let new_head_precondition =
              join_with_predecessors_postconditions head current_head_precondition
            in
            let converged =
              State.less_or_equal ~left:new_head_precondition ~right:current_head_precondition
            in
            Log.log
              ~section:`Fixpoint
              "\n%a\n  { <= (result %b) (iteration = %d) }\n\n%a"
              State.pp
              new_head_precondition
              converged
              local_iteration
              State.pp
              current_head_precondition;
            if not converged then (
              let precondition =
                State.widen
                  ~previous:current_head_precondition
                  ~next:new_head_precondition
                  ~iteration:local_iteration
              in
              Hashtbl.set preconditions ~key:head_id ~data:precondition;
              iterate (local_iteration + 1))
            else
              (* At this point, we know we have a local fixpoint.
               * Since operators are monotonic, `new_head_precondition` is also
               * a post fixpoint. This is basically the argument for performing
               * decreasing iteration sequence with a narrowing operator.
               * Therefore, `new_head_precondition` might be more precise,
               * let's use it at the result.
               *)
              Hashtbl.set preconditions ~key:head_id ~data:new_head_precondition
          in
          iterate 0
    in
    List.iter ~f:analyze_component components;
    { preconditions; postconditions; }


  let forward ~cfg ~initial func_name =
    let transition ~context node_id init statements =
      let forward statement_index before statement =
        let statement_key = [%hash: int * int] (node_id, statement_index) in
        let after = State.forward ~statement_key ~context before ~statement in
        (*
        Format.printf "\n\n  {  %a  } \n\n"
        Statement.pp
        statement
        ;
        *)
        (*Log.log
          ~section:`Fixpoint
          "\n%a\n  {  %a  }\n\n%a"
          State.pp
          before
          Statement.pp
          statement
          State.pp
          after;*)
        after
      in
      List.foldi ~f:forward ~init statements
    in
    our_compute_fixpoint
      cfg
      func_name
      ~initial_index:Cfg.entry_index
      ~initial
      ~predecessors:Cfg.Node.predecessors
      ~successors:Cfg.Node.successors
      ~transition
    (*
  let our_forward ~cfg ~initial =
    let transition node_id init statements =
      let forward statement_index before ({value; _} as statement : Statement.statement Node.t) =
        let _ = 
          match value with
          | Statement.Statement.Class {body; _ } -> 
            Some body
          | _ -> None
        in
        let statement_key = [%hash: int * int] (node_id, statement_index) in
        let after = State.forward ~statement_key before ~statement in
        Log.log
          ~section:`Fixpoint
          "\n%a\n  {  %a  }\n\n%a"
          State.pp
          before
          Statement.pp
          statement
          State.pp
          after;
        after
      in
      List.foldi ~f:forward ~init statements
    in
    compute_fixpoint
      cfg
      ~initial_index:Cfg.entry_index
      ~initial
      ~predecessors:Cfg.Node.predecessors
      ~successors:Cfg.Node.successors
      ~transition
      *)
  


  let backward ~cfg ~initial =
    let transition node_id init statements =
      let statement_index = ref (List.length statements) in
      let backward statement =
        statement_index := !statement_index - 1;
        let statement_key = [%hash: int * int] (node_id, !statement_index) in
        State.backward ~statement_key ~statement
      in
      List.fold_right ~f:backward ~init statements
    in
    compute_fixpoint
      cfg
      ~initial_index:Cfg.exit_index
      ~initial
      ~predecessors:Cfg.Node.successors
      ~successors:Cfg.Node.predecessors
      ~transition



end
