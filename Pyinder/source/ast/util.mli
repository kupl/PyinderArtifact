open Core
open Expression

module LocInsensitiveExp : sig
    type t = Expression.t [@@deriving compare, show]

    val to_default_location : expression:t -> t
end

module LocInsensitiveExpMap : sig 
    include Map.S with type Key.t = LocInsensitiveExp.t
    [@@deriving show]

    val set : 'a t -> key:Expression.t -> data:'a -> 'a t

    val length : 'a t -> int
end

(*
module LocInsensitiveExp : sig
    include module type of struct
        include Expression
    end
end

module LocInsensitiveExpMap : Map.S with type Key.t = LocInsensitiveExp.t
*)