open Core
open Ast
open Expression
open Statement

module type UniqueState = sig
  type t [@@deriving show, sexp]

  val bottom : t

  val less_or_equal : left:t -> right:t -> bool

  val equal : t -> t -> bool

  val join : t -> t -> t

  val widen : previous:t -> next:t -> iteration:int -> t

  val forward : statement_key:int -> t -> statement:Statement.t -> t

  val backward : statement_key:int -> t -> statement:Statement.t -> t
end


module UniqueState = struct
  module VarSet = struct 
    
    type t = Reference.Set.t [@@deriving sexp, equal, compare]

    let show t =
      (Reference.Set.fold t ~init:"(" ~f:(fun acc reference -> acc ^ (Reference.show reference) ^ ", "))
        ^ ")"
    let pp format t =
      let msg =
        show t
      in
      Format.fprintf format "%s" msg

    
    let empty = Reference.Set.empty
    let singleton name = Reference.Set.singleton name

    let add t data = Reference.Set.add t data

    let mem t data = Reference.Set.mem t data
    let union left right = Reference.Set.union left right

    (* let inter left right = Reference.Set.inter left right *)
    let fold ~init ~f t = Reference.Set.fold t ~init ~f

    let filter_map t ~f = Reference.Set.filter_map t ~f
  end

  type condtion_var_set =
    | True of VarSet.t
    | False of VarSet.t
  [@@deriving sexp, equal]

  type t = { 
    relation_var_map : VarSet.t Reference.Map.t;
    conditions : condtion_var_set Int.Map.t
  } [@@deriving sexp, equal]

  let pp_relation_var_map format relation_var_map = 
    Reference.Map.iteri ~f:(fun ~key ~data -> 
      Format.fprintf format "%a -> %a\n" Reference.pp key VarSet.pp data
    ) relation_var_map

  let pp_condition_var_set format condition_var_set =
    Format.fprintf format "%s"
    (match condition_var_set with
    | True v -> "True of " ^ (VarSet.show v)
    | False v -> "False of " ^ (VarSet.show v)
    )

  let pp_conditions format conditions = 
    Int.Map.iteri ~f:(fun ~key:_ ~data -> 
      Format.fprintf format "%a\n" pp_condition_var_set data
    ) conditions

  let pp format t = 
  Format.fprintf format "[ Variable Relation ] => \n";
  Format.fprintf format "%a\n" pp_relation_var_map t.relation_var_map;
  Format.fprintf format "\n";
  Format.fprintf format "[ Conditions ] => \n";
  Format.fprintf format "%a\n" pp_conditions t.conditions;
  Format.fprintf format "\n"

  let show _ = "Not Implemented"


  let create = { 
    relation_var_map = Reference.Map.empty; 
    conditions = Int.Map.empty;
  }
  let bottom = create

  let less_or_equal ~left:_ ~right:_ = true

  let get_all_relative_variables ~reference { relation_var_map; _ } =
    let rec get_relative_variables ~check_set reference =
      if VarSet.mem check_set reference then VarSet.empty
      else
        let var_set = Reference.Map.find relation_var_map reference |> Option.value ~default:VarSet.empty in
        let init_set = VarSet.add check_set reference in
        VarSet.fold var_set ~init:init_set ~f:(fun var_set new_reference -> 
          VarSet.union var_set (get_relative_variables ~check_set:var_set new_reference)
        )
    in

    get_relative_variables ~check_set:VarSet.empty reference

  let join_relation_var_map left right = 
    Reference.Map.merge left right ~f:(fun ~key:_ data ->
      match data with
      | `Both (a, b) -> Some (Reference.Set.union a b )
      | `Left v | `Right v -> Some v
    )
  
  let join_conditions left right =
    Int.Map.merge left right ~f:(fun ~key:_ data ->
      match data with
      | `Both (True a, True b) -> Some (True (Reference.Set.union a b))
      | `Both (False a, False b) -> Some (False (Reference.Set.union a b))
      | `Both _ -> None
      | `Left v | `Right v -> Some v
    )

  let join left right =
    {
      relation_var_map = join_relation_var_map left.relation_var_map right.relation_var_map;
      conditions = join_conditions left.conditions right.conditions;
    }

  let widen ~previous:_ ~next ~iteration:_ = next

  let abstract_variable reference = 
    if Reference.is_self reference || Reference.is_cls reference
    then
      let names = Reference.as_list reference in
      if List.length names >= 2
      then Some (Reference.create_from_list [List.nth_exn names 0; List.nth_exn names 1])
      else None
    else if Reference.is_parameter reference || Reference.is_local reference then
      Reference.head reference
    else
      Some reference

  let map_abstract_variable var_set =
    VarSet.filter_map var_set ~f:abstract_variable

  let add_assign ~target_variables ~value_variables ({relation_var_map; _ } as t) =
    let relation_var_map =
      VarSet.fold target_variables ~init:relation_var_map ~f:(fun map target ->
        let value_variables = (Reference.Map.find map target |> Option.value ~default:VarSet.empty) |> VarSet.union value_variables in
        Reference.Map.set ~key:target ~data:value_variables map
      ) 
    in

    { t with relation_var_map; }

  let add_condition ~line ~test_variables ~true_branch ({ conditions; _ } as t) =
    let conditions =
      if true_branch then
        Int.Map.set conditions ~key:line ~data:(True test_variables)
      else 
        Int.Map.set conditions ~key:line ~data:(False test_variables)
    in
    { t with conditions }

  
  let rec forward_expression (exp: Expression.t) =
    let forward_list expression_list f =
      List.fold ~init:VarSet.empty ~f:(fun accum e ->
        VarSet.union accum (f e)
      ) expression_list
    in
    let forward_generator (generator: Comprehension.Generator.t) =
      VarSet.union (forward_expression generator.target) (forward_expression generator.iterator)
      |> VarSet.union (forward_list generator.conditions forward_expression)
    in
    let forward_parameter (param: Parameter.t) =
      let param = Node.value param in
      VarSet.union 
        (Option.value_map param.value ~default:VarSet.empty ~f:forward_expression)
        (Option.value_map param.annotation ~default:VarSet.empty ~f:forward_expression)
    in
    let forward_expression_comprehension (comprehension: Expression.t Comprehension.t) =
      VarSet.union (forward_expression comprehension.element) (forward_list comprehension.generators forward_generator)
    in
    match Node.value exp with
    | Name n -> 
      (match name_to_reference n with
      | Some name -> VarSet.singleton name
      | None -> VarSet.empty
      )
    | Await e -> forward_expression e
    | BooleanOperator e -> VarSet.union (forward_expression e.left) (forward_expression e.right)
    | Call e -> 
      let f accum (a: Call.Argument.t) =
        VarSet.union accum (forward_expression a.value)
      in
      VarSet.union (forward_expression e.callee) (List.fold ~init:VarSet.empty ~f e.arguments)
    | ComparisonOperator e -> VarSet.union (forward_expression e.left) (forward_expression e.right)
    | Dictionary e -> 
      let f accum (a: Dictionary.Entry.t) =
        VarSet.union accum (VarSet.union (forward_expression a.key) (forward_expression a.value))
      in
      VarSet.union (List.fold ~init:VarSet.empty ~f e.entries) (forward_list e.keywords forward_expression)
    | Generator e -> forward_expression_comprehension e
    | FormatString e -> forward_list e (fun e ->
        match e with
        | Format e -> forward_expression e
        | _ -> VarSet.empty
      )
    | Lambda e -> VarSet.union (forward_list e.parameters forward_parameter) (forward_expression e.body)
    | List e -> forward_list e forward_expression
    | ListComprehension e -> forward_expression_comprehension e
    | Set e -> forward_list e forward_expression
    | SetComprehension e -> forward_expression_comprehension e
    | Starred e ->
        (match e with
        | Once e | Twice e -> forward_expression e
        )
    | Ternary e -> VarSet.union (forward_expression e.target) (forward_expression e.test) |> VarSet.union (forward_expression e.alternative)
    | Tuple e -> forward_list e forward_expression
    | UnaryOperator e -> forward_expression e.operand
    | WalrusOperator e -> VarSet.union (forward_expression e.target) (forward_expression e.value)
    | Yield (Some e) -> forward_expression e
    | YieldFrom e -> forward_expression e
    | _ -> VarSet.empty


  let forward_assignment ~target ~value state =
    let target_variables = forward_expression target |> map_abstract_variable in
    let value_variables = forward_expression value |> map_abstract_variable in
    add_assign ~target_variables ~value_variables state

  let forward_assert test =
    let test_variables = forward_expression test in
    test_variables

  let forward_statement ~(statement: Statement.t) state =
    let { Node.value; location; } = statement in 
    match value with
    | Assign { Assign.target; value; _} ->
      forward_assignment ~target ~value state
    | Assert { Assert.test; origin = If { true_branch; }; _ } 
    | Assert { Assert.test; origin = While { true_branch; }; _ }
    ->
      let line = Location.line location in 
      let test_variables = forward_assert test in
      add_condition ~line ~test_variables ~true_branch state
    (* | Define { signature={ parameters; _ }; _ } ->
       *)
    (* | For { target; iterator; _ } ->
      forward_assignment ~target ~value:iterator state *)
    | _ -> state

  let forward ~statement_key:_ state ~statement =
    forward_statement ~statement state

  let backward ~statement_key:_ state ~statement:_ =
    state

end

module type UniqueFixpoint = sig
  type state

  type t = {
    pre_variables: state Int.Table.t;
    post_variables: state Int.Table.t;
    pre_statements: state Location.Table.t;
  } [@@deriving show, sexp, equal]

  val join : t -> t -> t
  val entry : t -> state option

  val normal_exit : t -> state option

  val exit : t -> state option

  val empty : t

  val find : t -> int -> state option

  val find_pre_statements_of_location : t -> Location.t -> (state * Location.t) option

  val forward : cfg:Cfg.t -> initial:state -> t

  val backward : cfg:Cfg.t -> initial:state -> t

  (*
  val equal : f:(state -> state -> bool) -> t -> t -> bool
*)
end

module Make (State : UniqueState) = struct
  type state = State.t


  type t = {
    pre_variables: State.t Int.Table.t;
    post_variables: State.t Int.Table.t;
    pre_statements: State.t Location.Table.t;
  } [@@deriving sexp, equal]

  (*
  let equal ~f left right =
    Core.Hashtbl.equal f left.usedef_tables right.usedef_tables
  *)

  let pp format { pre_variables; post_variables; _ } =
    let print_state ~name ~key ~data =
      Format.fprintf format "%s %d -> \n%a\n" name key State.pp data
    in
    Hashtbl.iteri pre_variables ~f:(print_state ~name:"Before");
    Hashtbl.iteri post_variables ~f:(print_state ~name:"After")

  let show fixpoint = Format.asprintf "%a" pp fixpoint

  let find { pre_variables; _ } node_id = Hashtbl.find pre_variables node_id
  let entry { pre_variables; _ } = Hashtbl.find pre_variables Cfg.entry_index

  let normal_exit { post_variables; _ } = Hashtbl.find post_variables Cfg.normal_index

  let exit { post_variables; _ } = Hashtbl.find post_variables Cfg.exit_index

  let empty = { 
    pre_variables=Int.Table.create ();
    post_variables=Int.Table.create (); 
    pre_statements=Location.Table.create ();
  }

  let join_state left right =
    Int.Table.merge left right ~f:(fun ~key:_ data ->
      match data with
      | `Both (a, b) -> Some (State.join a b )
      | `Left v | `Right v -> Some v
    )

  let join left right = 
    {
      pre_variables = join_state left.pre_variables right.pre_variables;
      post_variables = join_state left.post_variables right.post_variables;
      pre_statements = left.pre_statements;
    }

  (* let get_usedef_tables { usedef_tables; _ } = usedef_tables *)

  let find_pre_statements_of_location { pre_statements; _ } location =
    Location.Table.fold pre_statements ~init:None ~f:(fun ~key ~data find ->
      match find with
      | Some _ -> find
      | None -> 
        let start_contains = Location.contains_eq ~location:key (Location.start location) in
        let stop_contains = Location.contains_eq ~location:key (Location.stop location) in
        (if start_contains && stop_contains then Some (data, key) else find)
    )

  let our_compute_fixpoint cfg ~initial_index ~initial ~predecessors ~successors ~transition =
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

    let pre_variables = Int.Table.create () in
    let post_variables=Int.Table.create () in
    let pre_statements = Location.Table.create () in

    let join_with_predecessors_usedef_tables node state =
      
      if Int.equal (Cfg.Node.id node) initial_index then
        State.join state initial
      else
        predecessors node
        |> Set.fold ~init:state ~f:(fun sofar predecessor_index ->
               Hashtbl.find post_variables predecessor_index
               |> Option.value ~default:State.bottom
               |> State.join sofar)
    in

    let analyze_node node =
      let node_id = Cfg.Node.id node in
      let pre = 
        Hashtbl.find pre_variables node_id
        |> Option.value ~default:State.bottom
        |> join_with_predecessors_usedef_tables node
      in
      let post = transition ~pre_statements node_id pre (Cfg.Node.statements node) in
      (*Format.printf "[[[ USEDEF TABLE: Node %d ]]] \n\n%a\n\n" node_id State.pp usedef_table;*)
      Hashtbl.set pre_variables ~key:node_id ~data:pre;
      Hashtbl.set post_variables ~key:node_id ~data:post;

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
            let current_head_precondition = Hashtbl.find_exn pre_variables head_id in
            let new_head_precondition =
              join_with_predecessors_usedef_tables head current_head_precondition
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
              Hashtbl.set pre_variables ~key:head_id ~data:precondition;
              iterate (local_iteration + 1))
            else
              (* At this point, we know we have a local fixpoint.
               * Since operators are monotonic, `new_head_precondition` is also
               * a post fixpoint. This is basically the argument for performing
               * decreasing iteration sequence with a narrowing operator.
               * Therefore, `new_head_precondition` might be more precise,
               * let's use it at the result.
               *)
              Hashtbl.set pre_variables ~key:head_id ~data:new_head_precondition
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
    

    { pre_variables; post_variables; pre_statements; }

  let forward ~cfg ~initial =
    let transition ~pre_statements node_id init statements =
      let forward statement_index before ({ Node.location; _ } as statement) =
        let statement_key = [%hash: int * int] (node_id, statement_index) in
        Hashtbl.set pre_statements ~key:location ~data:before;
        let after = State.forward ~statement_key before ~statement in
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
    let transition ~pre_statements node_id init statements =
      let _ = pre_statements in
      let statement_index = ref (List.length statements) in
      let backward statement =
        statement_index := !statement_index - 1;
        let statement_key = [%hash: int * int] (node_id, !statement_index) in
        State.backward ~statement_key ~statement
      in
      List.fold_right ~f:backward ~init statements
    in
    our_compute_fixpoint
      cfg
      ~initial_index:Cfg.exit_index
      ~initial
      ~predecessors:Cfg.Node.successors
      ~successors:Cfg.Node.predecessors
      ~transition

end


module UniqueStruct = Make (UniqueState)