open Ast

type kind =
  | If of Expression.t
  | While of Expression.t
  | Try
  | With
  | For
[@@deriving compare, sexp, show, hash]

module T = struct
  type t =
    | Empty 
    | Define of Reference.t
    | Context of kind * t
  [@@deriving compare, sexp, show, hash]

  let empty = Empty

  let define func_name = Define func_name

  let remove t =
    match t with
    | Context (_, t) -> t
    | _ -> t

  let set_context t node =
    match Cfg.Node.kind node with
    | Cfg.Node.If { test; _ } -> Context (If test, t)
    | Cfg.Node.While { test; _ } -> Context (While test, t)
    | Cfg.Node.Try _ -> Context (Try, t)
    | Cfg.Node.With _ -> Context (With, t)
    | Cfg.Node.For _ -> Context (For, t)
    | Cfg.Node.Join -> remove t
    | _ -> t

  let to_list t =
    let rec aux t acc =
      match t with
      | Context (kind, t) -> aux t (kind :: acc)
      | _ -> acc
    in
    aux t []

  
    


end

include T

let calc_test_sim left right =
  let left_list = to_list left in
  let right_list = to_list right in
  let left_test = List.filter_map (function If t | While t -> Some t | _ -> None ) left_list in
  let right_test = List.filter_map (function If t | While t -> Some t | _ -> None) right_list in

  let left_exp_map = List.fold_right (fun t acc -> 
      Expression.BoolExpressionCounter.count_expression_num ~state:acc t
    )
    left_test Expression.BoolExpressionCounter.empty
  in

  let right_exp_map = List.fold_right (fun t acc -> 
      Expression.BoolExpressionCounter.count_expression_num ~state:acc t
    )
    right_test Expression.BoolExpressionCounter.empty
  in

  let exp_map_calc = Expression.BoolExpressionCounter.calc_similarity left_exp_map right_exp_map in

  exp_map_calc

let calc_kind_sim left right =
  let left_list = to_list left in
  let right_list = to_list right in
  
  let left_try_num = List.length (List.filter (fun x -> x = Try) left_list) in
  let right_try_num = List.length (List.filter (fun x -> x = Try) right_list) in
  let try_sim = float_of_int ((min left_try_num right_try_num) + 1) /. float_of_int (left_try_num + right_try_num + 1) in

  let left_with_num = List.length (List.filter (fun x -> x = With) left_list) in
  let right_with_num = List.length (List.filter (fun x -> x = With) right_list) in
  let with_sim = float_of_int ((min left_with_num right_with_num) + 1) /. float_of_int (left_with_num + right_with_num + 1) in

  let left_for_num = List.length (List.filter (fun x -> x = For) left_list) in
  let right_for_num = List.length (List.filter (fun x -> x = For) right_list) in
  let for_sim = float_of_int ((min left_for_num right_for_num) + 1) /. float_of_int (left_for_num + right_for_num + 1) in

  let sim = (try_sim +. with_sim +. for_sim) /. 3. in

  sim

let calc_metric left right =
  let test_sim = calc_test_sim left right in
  let kind_sim = calc_kind_sim left right in
  let _ = kind_sim in
  1.0 -. test_sim

let context = ref empty


(* let gumtree ~source ~target =
  let source_list = to_list source in
  let target_list = to_list target in *)
  
  