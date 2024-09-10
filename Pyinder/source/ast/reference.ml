(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Core
open Pyre
open Sexplib.Conv

module T = struct
  type t = Identifier.t list [@@deriving compare, sexp, equal, hash, to_yojson, show]
end

include T

let local_qualifier_pattern = Str.regexp "^\\$local_\\([a-zA-Z-_0-9\\?]+\\)\\$"

let create ?prefix name =
  let name =
    if String.equal name "" then
      []
    else if String.equal name "..." then
      [name]
    else
      String.split ~on:'.' name
  in
  match prefix with
  | None
  | Some [""] ->
      name
  | Some prefix -> prefix @ name


let pp format reference = reference |> String.concat ~sep:"." |> Format.fprintf format "%s"

let show reference = Format.asprintf "%a" pp reference

module Map = Map.Make (T)
module SerializableMap = Data_structures.SerializableMap.Make (T)
module Set = Set.Make (T)
include Hashable.Make (T)



let empty = []

let create_from_list names = names

let as_list reference = reference

let combine prefix suffix =
  match prefix with
  | [""] -> suffix
  | _ -> prefix @ suffix


let delocalize reference =
  match reference with
  | head :: tail when String.is_prefix ~prefix:"$local_$" head -> [Identifier.sanitized head] @ tail
  | head :: tail when String.is_prefix ~prefix:"$local_" head ->
      let qualifier =
        if Str.string_match local_qualifier_pattern head 0 then
          Str.matched_group 1 head |> String.substr_replace_all ~pattern:"?" ~with_:"." |> create
        else (
          Log.debug "Unable to extract qualifier from %s" head;
          [])
      in
      qualifier @ [Identifier.sanitized head] @ tail
  | _ -> reference

let delocalize_only_name reference =
  match reference with
  | head :: tail when String.is_prefix ~prefix:"$local_$" head -> [Identifier.sanitized head] @ tail
  | head :: tail when String.is_prefix ~prefix:"$local_" head ->
      [Identifier.sanitized head] @ tail
  | _ -> reference

let is_target reference =
  match reference with
  | head :: _ when String.is_prefix ~prefix:"$target" head -> true
  | _ -> false
  
let is_local reference =
  match reference with
  | head :: _ when String.is_prefix ~prefix:"$local_" head -> true
  | _ -> false

let is_parameter reference =
  match reference with
  | head :: _ when String.is_prefix ~prefix:"$parameter$" head -> true
  | _ -> false

let is_self reference =
  match reference with
  | head :: _ when String.is_prefix ~prefix:"$parameter$self" head -> true
  | _ -> false

let is_cls reference =
  match reference with
  | head :: _ when String.is_prefix ~prefix:"$parameter$cls" head -> true
  | _ -> false

let is_attribute reference =
  let delocalized = delocalize_only_name reference in
  String.is_substring (show delocalized) ~substring:"."

let is_test name =
  (
  String.is_substring (show name) ~substring:"test_"
  || String.is_substring (show name) ~substring:"test."
  || String.is_substring (show name) ~substring:"tests."
  || String.is_substring (show name) ~substring:"_test"
  )

let is_assert name =
  (
  String.is_substring (show name) ~substring:".assert_"
  || String.is_substring (show name) ~substring:"._assert_"
  )

let is_is name =
  (
  String.is_substring (show name) ~substring:".is_"
  || String.is_substring (show name) ~substring:"._is_"
  )

let is_just_check name =
  is_assert name (* || is_is name *)



let sanitized reference = List.map ~f:Identifier.sanitized reference

let sanitize_qualified reference =
  List.rev reference
  |> (function
       | head :: tail -> sanitized [head] @ tail
       | reference -> reference)
  |> List.rev


let equal = [%compare.equal: t]

let equal_sanitized left right = equal (sanitized left) (sanitized right)

let pp_sanitized format reference =
  sanitized reference |> String.concat ~sep:"." |> Format.fprintf format "%s"


let show_sanitized reference = Format.asprintf "%a" pp_sanitized reference

let single = function
  | [single] -> Some single
  | _ -> None


let length = List.length

let reverse = List.rev

let is_empty = List.is_empty

let rec is_prefix ~prefix reference =
  match prefix, reference with
  | [], _ -> true
  | "" :: prefix, _ -> is_prefix ~prefix reference
  | prefix_head :: prefix, head :: reference when String.equal prefix_head head ->
      is_prefix ~prefix reference
  | _ -> false


let is_suffix ~suffix reference = is_prefix ~prefix:(List.rev suffix) (List.rev reference)

let rec is_strict_prefix ~prefix reference =
  match prefix, reference with
  | [], _ :: _ -> true
  | "" :: prefix, _ -> is_strict_prefix ~prefix reference
  | prefix_head :: prefix, head :: reference when String.equal prefix_head head ->
      is_strict_prefix ~prefix reference
  | _ -> false

let rec is_contain ~base ~target =
  (* whether base contains target *)
  match base, target with
  | _, [] -> true
  | base_hd::base_tl, target_hd::target_tl -> (String.equal base_hd target_hd) && (is_contain ~base:base_tl ~target:target_tl)
  | _ -> false


let drop_prefix ~prefix reference =
  let rec strip stripped reference prefix =
    match prefix, reference with
    | _, [_] when not stripped -> None
    | prefix_head :: prefix_tail, head :: tail when prefix_head = head ->
        strip true tail prefix_tail
    | [], reference -> Some reference
    | _ -> None
  in
  strip false reference prefix |> Option.value ~default:reference

let drop_suffix ~suffix reference =
  List.rev (drop_prefix ~prefix:suffix (List.rev reference)) 

let prefix reference =
  match List.rev reference with
  | [] -> None
  | _ :: prefix_reversed -> Some (List.rev prefix_reversed)


let head reference = List.hd reference >>| fun head -> [head]

let drop_head = function
  | [] -> [""]
  | _::tl -> tl

let drop_last reference = List.rev (drop_head (List.rev reference))

let first = function
  | [] -> ""
  | head :: _ -> head


let last = function
  | [] -> ""
  | reference -> List.last_exn reference


let map_last ~f reference =
  match List.rev reference with
  | [] -> []
  | head :: tail -> f head :: tail |> List.rev


let possible_qualifiers reference =
  let rec recurse reversed sofar =
    match reversed with
    | [] -> sofar
    | [_] -> sofar
    | _ :: tail -> recurse tail (reverse tail :: sofar)
  in
  recurse (reverse reference) []

let is_init name =
  String.is_substring ~substring:"__init__" (last name)

let is_new name =
  String.is_substring ~substring:"__new__" (last name)

let is_initialize name = 
  is_init name || is_new name