(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Core
open Pyre
open Ast
open Annotation



module MapLattice = struct
  module type MapSignature = sig
    type key

    type 'data t

    val empty : 'data t

    val mem : 'data t -> key -> bool

    val set : 'data t -> key:key -> data:'data -> 'data t

    val find : 'data t -> key -> 'data option

    val remove : 'data t -> key -> 'data t

    val fold : 'data t -> init:'a -> f:(key:key -> data:'data -> 'a -> 'a) -> 'a

    val fold2
      :  'data t ->
      'data t ->
      init:'a ->
      f:(key:key -> data:[ `Both of 'data * 'data | `Left of 'data | `Right of 'data ] -> 'a -> 'a) ->
      'a
  end

  module Make (Map : MapSignature) = struct
    include Map

    (** The keys of `right` have to be a subset of the keys of `left` for `left` to be less than or
        equal to `right`, since more keys = more restrictions = lower in the lattice *)
    let less_or_equal ~less_or_equal_one ~left ~right =
      let f ~key ~data:right_data sofar =
        sofar
        &&
        match find left key with
        | Some left_data -> less_or_equal_one ~left:left_data ~right:right_data
        | None -> false
      in
      fold right ~init:true ~f


    let join ~join_one left right =
      let f ~key ~data sofar =
        match data with
        | `Both (left, right) -> set sofar ~key ~data:(join_one left right)
        | `Left _
        | `Right _ ->
            sofar
      in
      fold2 left right ~init:empty ~f

    let meet ~meet_one left right =
      let f ~key ~data sofar =
        match data with
        | `Both (left, right) -> set sofar ~key ~data:(meet_one left right)
        | `Left data
        | `Right data ->
            set sofar ~key ~data
      in
      fold2 left right ~init:empty ~f


    (** Merge maps (take the union of all keys) *)
    let merge_with ~merge_one left right =
      let f ~key ~data sofar =
        match data with
        | `Both (left, right) -> set sofar ~key ~data:(merge_one left right)
        | `Left data
        | `Right data ->
            set sofar ~key ~data
      in
      fold2 left right ~init:empty ~f


    let update_existing ~old_map ~new_map =
      let update_unit ~key ~data map =
        if mem map key then
          set ~key ~data map
        else
          map
      in
      fold ~init:old_map ~f:update_unit new_map
  end
end

module IdentifierMap = MapLattice.Make (struct
  include Identifier.Map.Tree

  type key = Identifier.t
end)

module ReferenceMap = MapLattice.Make (struct
  include Reference.Map

  type key = Reference.t
end)

module Unit = struct
  type t = {
    base: Annotation.t option;
    attributes: t Identifier.Map.Tree.t;
  }
  [@@deriving sexp, eq]

  let empty = { base = None; attributes = IdentifierMap.empty }

  let create base = { empty with base = Some base }

  let create_all base attributes = { base; attributes; }

  let create_mutable type_ = create (Annotation.create_mutable type_)

  let top = create (Annotation.create_mutable Type.Top)

  (*
  let compare { base=base1; attributes=attrs1; } { base=base2; attributes=attrs2; } =
    match base1, base2 with
    | Some _, None -> -1
    | None, Some _ -> 1
    | Some b1, Some b2 -> Annotation.compare b1 b2
    | None, None -> 
  *)

  let rec pp format { base; attributes } =
    let attribute_map_entry (identifier, refinement_unit) =
      Format.asprintf "%a -> %a" Identifier.pp identifier pp refinement_unit
    in
    (match base with
    | Some base -> Format.fprintf format "[Base: %a; " Annotation.pp base
    | None -> Format.fprintf format "[Base: (); ");
    Map.Tree.to_alist attributes
    |> List.map ~f:attribute_map_entry
    |> String.concat ~sep:", "
    |> Format.fprintf format "Attributes: [%s]]"

  let rec pp_json format { base; attributes } =
    let attribute_map_entry (identifier, refinement_unit) =
      Format.asprintf {|"%a" : {%a}|} Identifier.pp identifier pp_json refinement_unit
    in
    (match base with
    | Some base -> Format.fprintf format {|"Base" : "%a", |} Annotation.pp base
    | None -> Format.fprintf format {|"Base" : "()", |}); 
    Map.Tree.to_alist attributes
    |> List.map ~f:attribute_map_entry
    |> String.concat ~sep:", "
    |> Format.fprintf format {|"Attributes" : {%s}|}


  let show = Format.asprintf "%a" pp

  let find = Identifier.Map.Tree.find

  let base { base; _ } = base

  let attributes { attributes; _ } = attributes

  let set_base refinement_unit ~base = { refinement_unit with base = Some base }

  let set_attributes refinement_unit ~attributes = { refinement_unit with attributes }

  let set_base_if_none refinement_unit ~base =
    { refinement_unit with base = Option.first_some refinement_unit.base base }


  (** If `attribute_path` is empty, set the base annotation. Otherwise, find the appropriate
      attribute (traversing intermediate units and constructing new ones as needed) and set the base
      there. *)
  let set_annotation ?(wipe_subtree = false) ~attribute_path ~annotation refinement_unit =
    let rec recurse ~annotation ~identifiers ({ attributes; _ } as refinement_unit) =
      match identifiers with
      | [] ->
          if wipe_subtree then
            { empty with base = Some annotation }
          else
            { refinement_unit with base = Some annotation }
      | identifier :: identifiers ->
          {
            refinement_unit with
            attributes =
              attributes
              |> IdentifierMap.set
                   ~key:identifier
                   ~data:
                     (find attributes identifier
                     |> Option.value ~default:empty (* TODO : is empty? or remain unknown? *)
                     |> recurse ~annotation ~identifiers);
          }
    in
    let x = recurse ~annotation ~identifiers:(attribute_path |> Reference.as_list) refinement_unit in
    x


  (** If `attribute_path` is empty, get the base annotation. Otherwise, find the appropriate
      attribute (traversing intermediate units until we finish or hit a dead end) and return the
      base found there, if any *)
  let get_annotation ~attribute_path refinement_unit =
    let rec recurse { base; attributes } ~identifiers =
      match identifiers with
      | [] -> base
      | identifier :: identifiers -> (
          match find attributes identifier with
          | Some refinement_unit -> recurse refinement_unit ~identifiers
          | None -> None)
    in
    recurse refinement_unit ~identifiers:(attribute_path |> Reference.as_list)


  let rec less_or_equal ~global_resolution ~left ~right =
    let base_less_or_equal left_base right_base =
      match left_base, right_base with
      | Some left, Some right ->
          Annotation.less_or_equal
            ~type_less_or_equal:(GlobalResolution.less_or_equal global_resolution)
            ~left
            ~right
      | None, None -> true (* intermediate refinement units don't require computation *)
      | _ -> false
    in
    let less_or_equal_one = less_or_equal ~global_resolution in
    base_less_or_equal left.base right.base
    && IdentifierMap.less_or_equal ~less_or_equal_one ~left:left.attributes ~right:right.attributes


  let rec join ~global_resolution left right =
    if equal left top || equal right top then
      top
    else
      (
      let should_recurse, base =
        match left.base, right.base with
        | Some left, Some right ->
            ( GlobalResolution.types_are_orderable global_resolution left.annotation right.annotation,
              Some (Annotation.join ~type_join:(GlobalResolution.join global_resolution) left right)
            )
        | None, None ->
            (* you only want to continue the nested join should both attribute trees exist *)
            not (Map.Tree.is_empty left.attributes || Map.Tree.is_empty right.attributes), None
        | _ -> false, None
      in
      let attributes =
        if should_recurse then
          IdentifierMap.join ~join_one:(join ~global_resolution) left.attributes right.attributes
        else
          IdentifierMap.empty
      in
      { base; attributes }
      )

  let rec join_with_merge ~global_resolution left right =
    if equal left top || equal right top then
      top
    else
      let base, attributes =
        match left.base, right.base with
        | Some left_base, Some right_base ->
            (
              Some (Annotation.join ~type_join:(GlobalResolution.join global_resolution) left_base right_base),
              IdentifierMap.merge_with ~merge_one:(join_with_merge ~global_resolution) left.attributes right.attributes
            )
        | Some left_base, None -> Some left_base, left.attributes
        | None, Some right_base -> Some right_base, right.attributes
        | None, None ->
            (* you only want to continue the nested join should both attribute trees exist *)
            None, IdentifierMap.empty
      in
      { base; attributes }

  let rec add_new_attribute ~global_resolution left right =
    if equal left top || equal right top then
      top
    else
      let base, attributes =
        match left.base, right.base with
        | Some left_base, Some right_base when Annotation.equal left_base right_base ->
            (
              Some left_base,
              IdentifierMap.merge_with ~merge_one:(add_new_attribute ~global_resolution) left.attributes right.attributes
            )
        | Some left_base, _ -> Some left_base, left.attributes
        | None, Some right_base -> Some right_base, right.attributes
        | None, None ->
            (* you only want to continue the nested join should both attribute trees exist *)
            None, IdentifierMap.empty
      in
      { base; attributes }

  let rec merge_attribute ~global_resolution left right =
    if equal left top || equal right top then
      top
    else
      let base, attributes =
        match left.base, right.base with
        | Some left_base, Some right_base when Annotation.equal left_base right_base ->
            (
              Some left_base,
              IdentifierMap.merge_with ~merge_one:(merge_attribute ~global_resolution) left.attributes right.attributes
            )
        | Some left_base, Some right_base ->
            (
              Some (Annotation.join ~type_join:(GlobalResolution.join global_resolution) left_base right_base),
              IdentifierMap.merge_with ~merge_one:(merge_attribute ~global_resolution) left.attributes right.attributes
            )
        | Some left_base, _ -> Some left_base, left.attributes
        | None, Some right_base -> Some right_base, right.attributes
        | None, None ->
            (* you only want to continue the nested join should both attribute trees exist *)
            None, IdentifierMap.empty
      in
      { base; attributes }


  let rec meet ~global_resolution left right =
    let should_recurse, base =
      match left.base, right.base with
      | Some left, Some right ->
          ( GlobalResolution.types_are_orderable global_resolution left.annotation right.annotation,
            Some (Annotation.meet ~type_meet:(GlobalResolution.meet global_resolution) left right) )
      | None, None ->
          (* you only want to continue the nested meet should at least one attribute tree exists *)
          not (Map.Tree.is_empty left.attributes && Map.Tree.is_empty right.attributes), None
      | _ -> false, None
    in
    let attributes =
      if should_recurse then
        IdentifierMap.meet ~meet_one:(meet ~global_resolution) left.attributes right.attributes
      else
        IdentifierMap.empty
    in
    { base; attributes }


  let widen ~global_resolution ~widening_threshold ~iteration left right =
    if iteration + 1 >= widening_threshold then
      create (Annotation.create_mutable Type.Top)
    else
      join ~global_resolution left right

  let widen_with_merge ~global_resolution ~widening_threshold ~iteration left right =
    if iteration + 1 >= widening_threshold then
      create (Annotation.create_mutable Type.Top)
    else
      join_with_merge ~global_resolution left right

  let rec remain_attrs (old_attrs: t IdentifierMap.t) (new_attrs: t IdentifierMap.t) =
    let f ~key:name ~data:u (sofar, flag) =
      match u with
      | `Left _ -> sofar, false || flag
      | `Right new_unit -> IdentifierMap.set sofar ~key:name ~data:new_unit, true
      | `Both (old_unit, new_unit) -> 
        let update_unit, is_update = remain_new old_unit new_unit in
        if (base update_unit) |> Option.is_some 
        then
          IdentifierMap.set sofar ~key:name ~data:update_unit, (is_update || flag)
        else sofar, false || flag
    in
    IdentifierMap.fold2 ~init:(IdentifierMap.empty, false) ~f old_attrs new_attrs

  and remain_base old_base new_base flag =
    if flag then new_base, flag else
    match old_base, new_base with
    | _, None -> None, false
    | None, Some anno -> Some anno, true
    | Some old_anno, Some new_anno ->
      if Annotation.equal old_anno new_anno then None, false else Some new_anno, true

  and remain_new old_t new_t =
    let update_attrs, is_update = remain_attrs old_t.attributes new_t.attributes in
    let update_base, is_update = remain_base (base old_t) (base new_t) is_update in
    { base=update_base; attributes=update_attrs; }, is_update

  let rec fold_full_reference ?(skip_none=false) { base; attributes; } (f : Annotation.t option -> 'a) =
    if Identifier.Map.Tree.is_empty attributes 
    then
      let result_opt = f base in
      match result_opt with
      | Some e_list -> List.map e_list ~f:(fun e -> [], Some e)
      | None -> [[], None]
    else
      let candidates = Identifier.Map.Tree.fold attributes ~init:[] ~f:(fun ~key ~data sofar -> 
        let attrs_result = fold_full_reference data f ~skip_none in
        List.fold attrs_result ~init:[] ~f:(fun sofar (str_list, f_result) ->
          if skip_none && Option.is_none f_result
          then
            sofar
          else
            (key::str_list, f_result)::sofar
        )@sofar
      )
      in
      candidates

  let rec top_to_unknown { base; attributes; } =
    let new_base =
      match base with
      | Some anno -> Some (transform_types ~f:Type.top_to_unknown anno)
      | _ -> base
    in

    {
      base = new_base;
      attributes = Identifier.Map.Tree.map attributes ~f:top_to_unknown
    }

  let rec add_unknown { base; attributes; } =
    let new_base =
      match base with
      | Some anno -> Some (transform_types ~f:Type.add_unknown anno)
      | _ -> base
    in

    {
      base = new_base;
      attributes = Identifier.Map.Tree.map attributes ~f:add_unknown
    }

end

module Store = struct
  type t = {
    annotations: Unit.t Reference.Map.t;
    temporary_annotations: Unit.t Reference.Map.t;
  }
  [@@deriving sexp, eq, equal]

  let empty = { annotations = ReferenceMap.empty; temporary_annotations = ReferenceMap.empty }

  let set_annotations { temporary_annotations; _ } annotations = { annotations; temporary_annotations; }

  let set_temporary_annotations { annotations; _ } temporary_annotations = { annotations; temporary_annotations; }

  let pp format { annotations; temporary_annotations } =
    let show_annotation (reference, unit) =
      Format.asprintf "%a -> %a" Reference.pp reference Unit.pp unit
    in
    Map.to_alist annotations
    |> List.map ~f:show_annotation
    |> String.concat ~sep:", "
    |> Format.fprintf format "Annotations: [%s]\n";
    Map.to_alist temporary_annotations
    |> List.map ~f:show_annotation
    |> String.concat ~sep:", "
    |> Format.fprintf format "Temporary Annotations: [%s]"

  let show = Format.asprintf "%a" pp

  let to_yojson format { annotations; temporary_annotations } =
    let show_annotation (reference, unit) =
      Format.asprintf {|"%a" : {%a}|} Reference.pp reference Unit.pp_json unit
    in
    Map.to_alist annotations
    |> List.map ~f:show_annotation
    |> String.concat ~sep:", "
    |> Format.fprintf format {|"Annotations" : {%s},|};
    Map.to_alist temporary_annotations
    |> List.map ~f:show_annotation
    |> String.concat ~sep:", "
    |> Format.fprintf format {|"Temporary Annotations" : {%s}|}

  let has_temporary_annotation ~name { temporary_annotations; _ } = ReferenceMap.mem temporary_annotations name
  let has_nontemporary_annotation ~name { annotations; _ } = ReferenceMap.mem annotations name

  let get_unit ?(include_temporary = true) ~name { annotations; temporary_annotations } =
    let temporary =
      if include_temporary then
        ReferenceMap.find temporary_annotations name
      else
        None
    in
    let found =
      match temporary with
      | Some _ -> temporary
      | None -> ReferenceMap.find annotations name
    in
    Option.value ~default:Unit.empty found


  (** Map an operation over what's at a given name. If there's nothing already existing, use
      `empty`.

      The way we handle temporary vs non-temporary is very particular:

      - If `temporary` is true we only apply this to `temporary_annotations`
      - Otherwise, we apply it to `annotations` and also apply it to any *existing* data in
        `temporary_annotations`, but we don't create any new `temporary_annotations`.
      - The idea here is to minimize the amount of duplicated data, but ensure that `annotations`
        and `temporary_annotations` always have a consistent view of (non-temporary) refinements. *)
  let map_over_name ~temporary ~name ~f { annotations; temporary_annotations } =
    let map_over_reference_map ~fallback reference_map =
      match Option.first_some (ReferenceMap.find reference_map name) fallback with
      | Some unit -> ReferenceMap.set ~key:name ~data:(f unit) reference_map
      | None -> reference_map
    in
    if temporary then
      {
        annotations;
        temporary_annotations =
          map_over_reference_map ~fallback:(Some Unit.empty) temporary_annotations;
      }
    else
      {
        annotations = map_over_reference_map ~fallback:(Some Unit.empty) annotations;
        temporary_annotations = map_over_reference_map ~fallback:None temporary_annotations;
      }


  let get_base ~name store = get_unit ~name store |> Unit.base

  let get_base_of_anno ~name store = get_unit ~include_temporary:false ~name store |> Unit.base

  let get_attributes ~name store = get_unit ~name store |> Unit.attributes
  
  let get_annotation_of_anno ~name ~attribute_path store = 
    get_unit ~include_temporary:false ~name store |> Unit.get_annotation ~attribute_path

  let get_annotation_of_temp ~name ~attribute_path store = 
    get_unit ~include_temporary:true ~name store |> Unit.get_annotation ~attribute_path

  let get_annotation ~name ~attribute_path store =
    let anno = get_unit ~name store |> Unit.get_annotation ~attribute_path in
    match anno with
    | None -> get_unit ~include_temporary:false ~name store |> Unit.get_annotation ~attribute_path
    | _ -> anno



  let set_base ?(temporary = false) ~name ~base store =
    map_over_name ~temporary ~name ~f:(Unit.set_base ~base) store


  let new_as_base ?(temporary = false) ~name ~base { annotations; temporary_annotations } =
    if temporary then
      {
        annotations;
        temporary_annotations =
          ReferenceMap.set temporary_annotations ~key:name ~data:(Unit.create base);
      }
    else
      {
        annotations = ReferenceMap.set annotations ~key:name ~data:(Unit.create base);
        temporary_annotations = ReferenceMap.remove temporary_annotations name;
      }


  let set_annotation
      ?(temporary = false)
      ?(wipe_subtree = false)
      ~name
      ~attribute_path
      ~base
      ~annotation
      store
    =
    let set_unit_annotation unit =
      unit
      |> Unit.set_annotation ~wipe_subtree ~attribute_path ~annotation
      |> Unit.set_base_if_none ~base
    in
    map_over_name ~temporary ~name ~f:set_unit_annotation store


  let less_or_equal ~global_resolution ~left ~right =
    let less_or_equal_one = Unit.less_or_equal ~global_resolution in
    ReferenceMap.less_or_equal ~less_or_equal_one ~left:left.annotations ~right:right.annotations
    && ReferenceMap.less_or_equal
         ~less_or_equal_one
         ~left:left.temporary_annotations
         ~right:right.temporary_annotations


  (** Whenever we know for sure that right is pointwise less_or_equal to left, then we can save
      computation by only checking for equality pointwise, which doesn't require type ordering
      operations *)
  let less_or_equal_monotone ~left ~right =
    let less_or_equal_one ~left ~right = Unit.equal left right in
    ReferenceMap.less_or_equal ~less_or_equal_one ~left:left.annotations ~right:right.annotations
    && ReferenceMap.less_or_equal
         ~less_or_equal_one
         ~left:left.temporary_annotations
         ~right:right.temporary_annotations


  let meet ~global_resolution left right =
    let meet_one = Unit.meet ~global_resolution in
    {
      annotations = ReferenceMap.meet ~meet_one left.annotations right.annotations;
      temporary_annotations =
        ReferenceMap.meet ~meet_one left.temporary_annotations right.temporary_annotations;
    }


  (** Use an "outer" join to join or widen stores, which means we are strict about types (a proper
      join) but permissive about variables that might only be instantiated on one side.

      This can be done as either a join or a widen depending whether we set `widening_threshod`,
      which is applied at the `Refinement.Unit` level. *)
  let widen_or_join ~merge_one left right =
    {
      (* Newly-instantiated locals live in `annotations`, so we merge with join *)
      annotations = ReferenceMap.merge_with ~merge_one left.annotations right.annotations;
      (* `temporary_annotations` only has type info, so we do a proper join *)
      temporary_annotations =
        ReferenceMap.merge_with ~merge_one left.temporary_annotations right.temporary_annotations;
        (*ReferenceMap.join ~join_one:merge_one left.temporary_annotations right.temporary_annotations;*)
    }

  let widen_or_join_with_merge ~merge_one left right =
    {
      (* Newly-instantiated locals live in `annotations`, so we merge with join *)
      annotations = ReferenceMap.merge_with ~merge_one left.annotations right.annotations;
      (* `temporary_annotations` only has type info, so we do a proper join *)
      temporary_annotations =
        ReferenceMap.merge_with ~merge_one left.temporary_annotations right.temporary_annotations;
    }

  let outer_join ~global_resolution =
    let merge_one = Unit.join ~global_resolution in
    widen_or_join ~merge_one


  let outer_widen ~global_resolution ~iteration ~widening_threshold =
    let merge_one = Unit.widen ~global_resolution ~iteration ~widening_threshold in
    widen_or_join ~merge_one

  let join_with_merge ~global_resolution =
    let merge_one = Unit.join_with_merge ~global_resolution in
    widen_or_join_with_merge ~merge_one

  let widen_with_merge ~global_resolution ~iteration ~widening_threshold =
    let merge_one = Unit.widen_with_merge ~global_resolution ~iteration ~widening_threshold in
    widen_or_join_with_merge ~merge_one


  let update_existing ~old_store ~new_store =
    {
      annotations =
        ReferenceMap.update_existing ~old_map:old_store.annotations ~new_map:new_store.annotations;
      temporary_annotations =
        ReferenceMap.update_existing
          ~old_map:old_store.temporary_annotations
          ~new_map:new_store.temporary_annotations;
    }


  let update_with_filter ~old_store ~new_store ~filter =
    let update_map old_map new_map =
      let f ~key ~data sofar =
        if Unit.base data |> Option.map ~f:(filter key) |> Option.value ~default:false then
          sofar |> ReferenceMap.set ~key ~data
        else
          sofar
      in
      ReferenceMap.fold ~init:old_map ~f new_map
    in
    {
      annotations = update_map old_store.annotations new_store.annotations;
      temporary_annotations =
        update_map old_store.temporary_annotations new_store.temporary_annotations;
    }

  let remain_new ~old_store ~new_store =
    let update_map (old_map: Unit.t ReferenceMap.t) (new_map: Unit.t ReferenceMap.t) =
      let f ~key:new_ref ~data:u sofar =
        match u with
        | `Left _ -> sofar
        | `Right new_unit -> ReferenceMap.set sofar ~key:new_ref ~data:new_unit
        | `Both (old_unit, new_unit) -> 
          let result, _ = Unit.remain_new old_unit new_unit in
          if (Unit.base result) |> Option.is_some
          then
            ReferenceMap.set sofar ~key:new_ref ~data:result
          else
            sofar
      in
      ReferenceMap.fold2 ~init:ReferenceMap.empty ~f old_map new_map
    in
    {
      annotations = update_map old_store.annotations new_store.annotations;
      temporary_annotations =
        update_map old_store.temporary_annotations new_store.temporary_annotations;
    }

  let update_self ~global_resolution ({ annotations; temporary_annotations; } as t) =
    (*let merge_one = Unit.join ~global_resolution in*)
    let merge_one = Unit.meet ~global_resolution in
    let extract_self = update_with_filter ~old_store:empty ~new_store:t ~filter:(fun reference _ -> 
        String.is_suffix ~suffix:"$self" (Reference.last reference)
    )
    in
    let x =
    {
      annotations = ReferenceMap.meet ~meet_one:merge_one annotations extract_self.temporary_annotations;
      temporary_annotations = temporary_annotations;
    }
    in
    x

  let fold_map ~(f:(key:Reference.t -> data:Unit.t -> Unit.t Reference.Map.t -> Unit.t Reference.Map.t)) (init:t) ({ annotations; temporary_annotations; }):t
  = 
  {
    annotations = ReferenceMap.fold ~init:init.annotations ~f annotations;
    temporary_annotations = temporary_annotations;
  }

  let update_from_top_to_unknown { annotations; temporary_annotations; } =
    let rec f data:Unit.t =
        let base = Unit.base data in
        let attributes = Unit.attributes data in
        if Identifier.Map.Tree.is_empty attributes
        then
          let new_base = 
            match base with
            | Some { annotation; mutability; } -> if Type.is_top annotation or Type.is_any annotation then Some { annotation=Type.Bottom; mutability; } else base
            | _ -> base
          in
          { base=new_base; attributes; }
        else
          let new_attributes = Identifier.Map.Tree.map attributes ~f in
          { base; attributes=new_attributes; }
    in

    { 
      annotations=Reference.Map.map annotations ~f;
      temporary_annotations=Reference.Map.map temporary_annotations ~f;
    }

  let update_possible ~global_resolution ({ annotations=prev_anno; temporary_annotations=prev_temp_anno; } as prev) { annotations=cur_anno; temporary_annotations=cur_temp_anno; } =
      let join left_anno opt =
        match opt with
        | None -> left_anno
        | Some right_anno ->
          let x = Unit.join_with_merge ~global_resolution left_anno right_anno in
          (*Format.printf "[[[ JOIN ]]] \n\n%a\n\n" Unit.pp x;*)
          x
      in
      ReferenceMap.fold ~init:prev ~f:(fun ~key ~data { annotations=sofar_anno; temporary_annotations=sofar_temp_anno; } ->
          let cur_anno_data = ReferenceMap.find cur_anno key in
          let prev_anno_data = ReferenceMap.find prev_anno key in
          let prev_temp_anno_data = ReferenceMap.find prev_temp_anno key in
          let new_anno, new_temp = 
            if Option.is_some cur_anno_data
            then
              if Option.is_some prev_anno_data then
                ReferenceMap.set sofar_anno ~key ~data:(join data prev_anno_data), sofar_temp_anno
              else
                sofar_anno, ReferenceMap.set sofar_temp_anno ~key ~data:(join data prev_temp_anno_data)
            else
              ReferenceMap.remove sofar_anno key, ReferenceMap.set sofar_temp_anno ~key ~data:(join data prev_temp_anno_data) 
          in

        { annotations=new_anno; temporary_annotations=new_temp; }
      ) cur_temp_anno

  let combine_join_with_merge ~global_resolution { annotations; temporary_annotations; } =
    ReferenceMap.merge_with ~merge_one:(Unit.join_with_merge ~global_resolution) annotations temporary_annotations

  let make_map_function_of_types { annotations; temporary_annotations; } f =
    let result_of_anno = ReferenceMap.fold annotations ~init:[] ~f:(fun ~key ~data sofar -> 
      let reference_list = Unit.fold_full_reference data f ~skip_none:true in
      sofar@(List.map reference_list ~f:(fun (str_list, res) -> (Reference.show key)::str_list, res))
    )
    in

    let result_of_temp = ReferenceMap.fold temporary_annotations ~init:[] ~f:(fun ~key ~data sofar -> 
      let reference_list = Unit.fold_full_reference data f ~skip_none:true in
      sofar@(List.map reference_list ~f:(fun (str_list, res) -> (Reference.show key)::str_list, res))
    )
    in
    
    result_of_anno@result_of_temp


  let top_to_unknown { annotations; temporary_annotations; } =
    {
      annotations = Reference.Map.map annotations ~f:Unit.top_to_unknown;
      temporary_annotations = Reference.Map.map temporary_annotations ~f:Unit.top_to_unknown;
    }

  let add_unknown { annotations; temporary_annotations; } =
    {
      annotations = Reference.Map.mapi annotations ~f:(fun ~key ~data -> if Reference.is_self key then data else Unit.add_unknown data);
      temporary_annotations = Reference.Map.mapi temporary_annotations ~f:(fun ~key ~data -> if Reference.is_self key then data else Unit.add_unknown data);
    }

  let update_self_attributes_tree ~global_resolution { annotations; temporary_annotations; } self_attributes_tree temp_self_attributes_tree class_param =
    let merge_one = Unit.merge_attribute ~global_resolution in
    let add_one = Unit.add_new_attribute ~global_resolution in
    
    let self_base = 
      ReferenceMap.find annotations class_param 
      >>| (fun u -> 
        { u with attributes=IdentifierMap.empty; }  
      )
    in

    let annotations =
      match (ReferenceMap.find annotations class_param) with
      | Some u ->
        (ReferenceMap.set annotations ~key:class_param ~data:(u |> Unit.set_attributes ~attributes:self_attributes_tree))
        |> ReferenceMap.merge_with ~merge_one annotations
      | _ ->
        annotations
    in

    
    
    let temporary_annotations =
      match (ReferenceMap.find temporary_annotations class_param) with
      | Some u ->
        (ReferenceMap.set temporary_annotations ~key:class_param ~data:(u |> Unit.set_attributes ~attributes:temp_self_attributes_tree))
        |> ReferenceMap.merge_with ~merge_one:add_one temporary_annotations
      | _ when Option.is_some self_base ->
        let u = Option.value_exn self_base in
        (ReferenceMap.set temporary_annotations ~key:class_param ~data:(u |> Unit.set_attributes ~attributes:temp_self_attributes_tree))
        |> ReferenceMap.merge_with ~merge_one:add_one temporary_annotations
      | _ -> temporary_annotations
    in

   

    { annotations; temporary_annotations; }

end