open Core
open Expression

module LocInsensitiveExp = struct
  type t = Expression.t [@@deriving compare, sexp, show]

  let rec to_default_location ~expression:({ Node.value; _ } as t) =
    let value =
      match value with
      | Expression.Name (Identifier _ ) | Constant _ -> value
      | Name (Attribute ({ base; _ } as attr)) ->
        Name (Attribute { attr with base = to_default_location ~expression:base})
      | Call { Call.callee; arguments } ->
        let callee = to_default_location ~expression:callee in
        let visit_argument ({ Call.Argument.value; _ } as t) =
          { t with value = to_default_location ~expression:value }
        in
        let arguments = List.map arguments ~f:visit_argument in
        Call { callee; arguments }
      | List elements -> List (List.map elements ~f:(fun expression -> to_default_location ~expression))
      | Tuple elements -> Tuple (List.map elements ~f:(fun expression -> to_default_location ~expression))
      | _ -> failwith (Format.sprintf "Why is in here by default location? %s" (Expression.show t))
    in

    Node.create_with_default_location value
  (*
  let to_expression t = Node.create_with_default_location t

  let of_expression { Node.value; _ } = value
  *)
end

module LocInsensitiveExpMap = struct 
  include Map.Make(LocInsensitiveExp)
  [@@deriving show]
  let set t ~key ~data = set t ~key:(LocInsensitiveExp.to_default_location ~expression:key) ~data

  let mem t data = mem t (LocInsensitiveExp.to_default_location ~expression:data)

  let find t data = find t (LocInsensitiveExp.to_default_location ~expression:data)

  let find_exn t data = find_exn t (LocInsensitiveExp.to_default_location ~expression:data)
end

(*
module LocInsensitiveExp = struct
  include Expression
  let compare left right = location_insensitive_compare left right
end

module LocInsensitiveExpMap = struct
  include Map.Make(LocInsensitiveExp)

  let set t ~key:{ Node.value; _ } ~data = set t ~key:(Node.create_with_default_location value) ~data
end
*)