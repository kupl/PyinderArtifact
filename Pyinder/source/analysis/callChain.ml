open Core
open Ast

module T = struct
  type t = Reference.t Location.Map.t [@@deriving compare, sexp, equal]

  let empty = Location.Map.empty

  let length = Location.Map.length

  let join left right = 
    Location.Map.merge left right ~f:(fun ~key:_ -> function
      | `Left callee | `Right callee -> Some callee
      | `Both (c, _) -> Some c
    )

  let set_callee ~location ~callee t =
    Location.Map.set t ~key:location ~data:callee

  let get_callee ~location t =
    Location.Map.find t location

  let get_callee_chain t =
    Location.Map.to_alist ~key_order:`Increasing t
    |> List.map ~f:(fun (_, callee) -> callee)
end

include T