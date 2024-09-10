open Core
open Ast
open Pyre
open AttributeAnalysis
(*
open Usedef
exception NotEqualException;;
*)

let check_dir : string -> bool 
= fun path ->
  match Sys.is_directory path with
  | `Yes -> true
  | _ -> false

let check_and_make_dir : string -> unit
= fun path ->
  if check_dir path then ()
  else Unix.mkdir path



(*
let check_file : string -> bool
= fun path ->
match Sys.file_exists path with
| `Yes -> true
| _ -> false
  *)
  
let data_path = ref ""

let save_mode (mode: string) =
  check_and_make_dir !data_path;
  let target_path = !data_path ^ "/mode" ^ ".marshalled" in
  let data_out = open_out target_path in
  let sexp = String.sexp_of_t mode in
  Marshal.to_channel data_out sexp [];
  close_out data_out

let load_mode () =
  let data_in = open_in (!data_path ^ "/mode" ^ ".marshalled") in
  let mode = String.t_of_sexp (Marshal.from_channel data_in) in
  close_in data_in;
  mode

let on_any = ref true
let on_dataflow = ref true

let type_sensitive = ref true
let on_class_var = ref true
let on_attribute = ref true

let ignore_error = ref true

let baseline = ref false

let debug = ref false

let skip_reference_map = ref (Reference.Map.empty)

module ReferenceSet = Reference.Set

module ReferenceHash = struct
  include Reference.Table

  (* let join_type ~type_join left right =
    merge_into ~src:left ~dst:right ~f:(fun ~key:_ src dst ->
      match dst with
      | Some v -> Set_to (type_join src v)
      | _ -> Set_to src
    ) *)
    (* merge left right ~f:(fun ~key:_ data ->
      match data with
      | `Both (left, right) -> if Type.equal left right then Some left else (
        try
          Some (type_join left right)
        with
        | (* ClassHierarchy.Untracked *) _ -> Log.dump "%a\n%a\n" Type.pp left Type.pp right; Some (Type.union_join left right)
      )
      | `Left data | `Right data -> Some data
    ) *)

  let join ~data_join ~equal left right =
    (* let timer = Timer.start () in
    let t_list = ref [] in *)
    merge_into ~src:left ~dst:right ~f:(fun ~key:_ src dst ->
      match dst with 
      | Some v -> 
        
        if equal src v then (
          Set_to v
          ) else Set_to (data_join src v)
      | _ -> 

        Set_to src
    )

  (* let pp ~data_pp format t =
    iteri ~f:(fun ~key ~data ->
      Format.fprintf format "%a => %a\n" Reference.pp key data_pp data
    ) t *)
end

module TypeFromFuncs = struct
  type t = Reference.Set.t Type.Map.t [@@deriving sexp, equal]

  let empty = Type.Map.empty

  let is_empty = Type.Map.is_empty

  let set = Type.Map.set

  let fold = Type.Map.fold

  let existsi = Type.Map.existsi

  let reference_set_pp format t =
    Reference.Set.iter t ~f:(fun r ->
      Format.fprintf format "%a, " Reference.pp r
    )

  let get_type ~type_join t =
    let result = 
      Type.Map.fold t ~init:Type.Bottom ~f:(fun ~key ~data:_ typ ->
        try
          type_join key typ
        with
        | (* ClassHierarchy.Untracked *) _ -> Type.union_join key typ
      )
    in

    if Type.is_bottom result then None else Some result
    
  let get_all_callees t =
    Type.Map.fold t ~init:Reference.Set.empty ~f:(fun ~key:_ ~data acc ->
      Reference.Set.union acc data
    )

  let get_callees ~typ ~less_or_equal t =
    if Type.is_unknown typ then 
      Type.Map.find t typ |> Option.value ~default:Reference.Set.empty
    else (
      let typ = Type.filter_unknown typ in
      Type.Map.fold t ~init:Reference.Set.empty ~f:(fun ~key ~data acc ->
        if less_or_equal ~left:key ~right:typ then Reference.Set.union acc data
        else acc
      )
    )

  (* let callees t =
    Type.Map.fold t ~init:Reference.Set.empty ~f:(fun ~key:_ ~data acc ->
      Reference.Set.union acc data
    ) *)

  let pp format t =
    Type.Map.iteri t ~f:(fun ~key ~data ->
      Format.fprintf format "%a => %a\n" Type.pp key reference_set_pp data
    )

  let join left right =
    Type.Map.merge left right ~f:(fun ~key:_ data ->
      match data with
      | `Left t | `Right t -> Some t
      | `Both (t1, t2) -> Some (ReferenceSet.union t1 t2)
    )
end

module ReferenceMap = struct
  include Map.Make (Reference)

  let yojson_of_t ~yojson_of_data t =
    (* let open Yojson.Basic in *)
    `Assoc (
      fold t ~init:[] ~f:(fun ~key ~data acc ->
        (Reference.show key, yojson_of_data data)::acc
      )
    )

  let find_by_suffix t key =
    fold t ~init:None ~f:(fun ~key:ref ~data acc ->
      if String.equal (Reference.last ref) key then Some data
      else acc
    )
  let update_default_value prev next =
    merge prev next ~f:(fun ~key:_ data ->
      match data with
      | `Both (_, data) -> Some data
      | `Left data | `Right data -> Some data
    )
   
  let join_type ~type_join left right =
    (* merge_into ~src:left ~dst:right ~f:(fun ~key:_ src dst ->
      match dst with
      | Some v¸¸¸¸¸¸  
    ) *)
    merge left right ~f:(fun ~key:_ data ->
      match data with
      | `Both (left, right) -> if Type.equal left right then Some left else (
        try
          Some (type_join left right)
        with
        | (* ClassHierarchy.Untracked *) _ -> Log.dump "%a\n%a\n" Type.pp left Type.pp right; Some (Type.union_join left right)
      )
      | `Left data | `Right data -> Some data
    )

  let join_var_from_funcs left right =
    merge left right ~f:(fun ~key:_ data ->
      match data with
      | `Both (left, right) -> Some (TypeFromFuncs.join left right)
      | `Left data | `Right data -> Some data
    )

  let join ~data_join ~equal left right =
    (* let timer = Timer.start () in
    let t_list = ref [] in *)
    let x =
      (* fold left ~init:right ~f:(fun ~key ~data acc ->
          let x = find acc key in
          let tt0 = Timer.stop_in_sec timer in
          t_list := (tt0, "find")::!t_list;
          match x with
          | Some v when equal v data -> 
            let tt0 = Timer.stop_in_sec timer in
            t_list := (tt0, "equal")::!t_list;
            acc
          | Some v -> 
            let x = set acc ~key ~data:(data_join data v) in
            let tt0 = Timer.stop_in_sec timer in
            t_list := (tt0, "join")::!t_list;
            x
          | _ -> 
            let x = set acc ~key ~data in
            let tt0 = Timer.stop_in_sec timer in
            t_list := (tt0, "concat")::!t_list;
            x
            
      ) *)
     (* merge_into ~src:left ~dst:right ~f:(fun ~key:_ src dst ->
      match dst with 
      | Some v -> if equal src v then Set_to v else Set_to (data_join src v)
      | _ -> Set_to src *)
    merge left right ~f:(fun ~key:_ data ->
      match data with
      | `Both (left, right) -> 
        let x = if equal left right then Some left else Some (data_join left right) in
        (* let tt0 = Timer.stop_in_sec timer in
        t_list := (tt0, "join")::!t_list; *)
        x
      | `Left data | `Right data -> 
        (* let tt0 = Timer.stop_in_sec timer in
        t_list := (tt0, "concat")::!t_list;  *)
        Some data
    )
    in
    (* let total_time = Timer.stop_in_sec timer in
      if Float.(>.) total_time 0.1 then (
        Log.dump "MAP JOIN %.3f" total_time;
        List.iter !t_list ~f:(fun (t, msg) -> Log.dump "%s... %.3f" msg t);
      ); *)
    x

  let diff left right =
    fold2 left right ~init:ReferenceSet.empty ~f:(fun ~key ~data refset->
      match data with
      | `Both (left, right) -> if Type.equal left right then refset else ReferenceSet.add refset key
      | `Left v | `Right v when not (Type.is_unknown v) -> ReferenceSet.add refset key
      | _ -> refset
    )

  let diff_var_from_funcs left right =
    fold2 left right ~init:ReferenceSet.empty ~f:(fun ~key ~data refset->
      match data with
      | `Both (left, right) -> if TypeFromFuncs.equal left right then refset else ReferenceSet.add refset key
      | `Left v | `Right v when not (TypeFromFuncs.is_empty v) -> ReferenceSet.add refset key
      | _ -> refset
    )  

  let to_set t =
    keys t
    |> List.fold ~init:ReferenceSet.empty ~f:(fun set key -> ReferenceSet.add set key)

  let pp ~data_pp format t =
    iteri ~f:(fun ~key ~data ->
      Format.fprintf format "%a => %a\n" Reference.pp key data_pp data
    ) t
end

module StringSet = Set.Make (String)

module TypeSet = Set.Make (Type)

module VarTypeSet = struct
  type t = TypeSet.t Reference.Map.t [@@deriving sexp, compare, equal]

  let empty = Reference.Map.empty

  let type_set_pp format t =
    TypeSet.iter t ~f:(fun typ ->
      Format.fprintf format "%a" Type.pp typ
    )
  let pp format t =
    Reference.Map.iteri t ~f:(fun ~key ~data ->
      Format.fprintf format "%a => %a\n" Reference.pp key type_set_pp data
    )

  let join left right = Reference.Map.merge left right ~f:(fun ~key:_ data ->
    match data with
    | `Left t | `Right t -> Some t
    | `Both (t1, t2) -> Some (TypeSet.union t1 t2)
  )

  let fold = Reference.Map.fold

  let set = Reference.Map.set
end

module CallerSet = Reference.Set
module FunctionSet = Reference.Set
module StoreMap = ReferenceMap
module ClassMap = ReferenceMap
module FunctionMap = ReferenceMap

module ClassHash = ReferenceHash
module FunctionHash = ReferenceHash

module AttrsSet = StringSet

module MethodMap = Map.Make (Identifier)

module IdentifierMap = Map.Make (Identifier)

let weaken_typ typ =
  let weaken_typ = Type.weaken_literals typ in
  let weaken_typ =
    match weaken_typ with
    | Type.IntExpression _ -> Type.Primitive "int"
    | _ -> weaken_typ
  in
  weaken_typ

module type ArgTypes = sig
  type t = Type.t IdentifierMap.t
end



module ArgTypes = struct
  type t = Type.t IdentifierMap.t [@@deriving sexp, equal, compare]

  let empty = IdentifierMap.empty

  let yojson_of_t t : Yojson.Safe.json =
    (* let open Yojson.Basic in *)
    `Assoc (
      IdentifierMap.fold t ~init:[] ~f:(fun ~key ~data acc ->
        (key, Type.to_yojson data)::acc
      )
    )

  let is_empty = IdentifierMap.is_empty

  let fold = IdentifierMap.fold
  let filter ~f t = IdentifierMap.filter ~f t

  let filter_keys = IdentifierMap.filter_keys
  let map ~f t = IdentifierMap.map ~f t

  let mem = IdentifierMap.mem

  let set_arg_type t ident typ =
    let modified_typ = weaken_typ typ in
    let exn_typ = IdentifierMap.find t ident |> Option.value ~default:modified_typ in
    match exn_typ with
    | Bottom | Any | Top -> t
    | _ ->
      IdentifierMap.set ~key:ident ~data:modified_typ t

  let add_arg_type ~join t ident typ =
    let modified_typ = weaken_typ typ in
    let exn_typ = IdentifierMap.find t ident |> Option.value ~default:modified_typ in
    match exn_typ with
    | Bottom | Any | Top -> t
    | _ ->
      IdentifierMap.set ~key:ident ~data:(join modified_typ exn_typ) t

  let join ~type_join left right =
    IdentifierMap.merge left right ~f:(fun ~key:_ data ->
      match data with
      | `Left t | `Right t -> Some t
      | `Both (t1, t2) -> 
        try
          Some (type_join t1 t2)
        with
        | (* ClassHierarchy.Untracked *) _ -> Log.dump "%a\n%a\n" Type.pp t1 Type.pp t2; Some (Type.union_join t1 t2)
    ) 

  let less_or_equal ~less_or_equal left right =
    IdentifierMap.fold2 left right ~init:true ~f:(fun ~key:_ ~data flag ->
      flag &&
      match data with
      | `Left _ -> false
      | `Right _ -> true
      | `Both (v1, v2) -> less_or_equal v1 v2 
    )

  (* let less_or_equal_keys left right =
    IdentifierMap.fold2 left right ~init:true ~f:(fun ~key:_ ~data flag ->
      flag &&
      match data with
      | `Left _ -> false
      | `Right _ -> true
      | `Both (v1, v2)  -> Type.equal v1 v2
    )

  let can_arg_merge left right =
    IdentifierMap.fold2 left right ~init:true ~f:(fun ~key:_ ~data flag ->
      flag &&
      match data with
      | `Left _ -> true
      | `Right _ -> true
      | `Both (v1, v2) -> Type.equal v1 v2 
    )

  let arg_merge left right =
    if can_arg_merge left right then (
      Some (
        IdentifierMap.merge left right ~f:(fun ~key:_ data ->
          match data with
          | `Left t | `Right t -> Some t
          | `Both (t1, t2) -> 
            let _ = t2 in
            Some t1
        ) 
      )
    ) else 
      None *)

  let pp format t =
    IdentifierMap.iteri ~f:(fun ~key ~data ->
      Format.fprintf format "%a -> %a \n" Identifier.pp key Type.pp data;
    ) t

  let get_type t ident =
    IdentifierMap.find t ident |> Option.value ~default:Type.Unknown

  let make_arg_types arg_typ_list =
    List.fold arg_typ_list ~init:empty ~f:(fun arg_types (arg, typ) -> set_arg_type arg_types arg typ)
end

module ArgTypesOpt = struct
  type t = ArgTypes.t option [@@deriving sexp, compare]
end

module ArgTypesOptSet = Set.Make (ArgTypesOpt)

module ArgTypesKey = struct
  type t = Reference.t * (Identifier.t * Type.t) list [@@deriving sexp, compare, hash, show]

  let to_key define arg_types = 
  define,  
  ArgTypes.fold arg_types ~init:[] ~f:(fun ~key ~data acc -> 
    (key, data)::acc
  )

  let from_key key = 
  let define, arg_types = key in
  define,  
  List.fold arg_types ~init:ArgTypes.empty ~f:(fun arg_types (key, data) -> 
    ArgTypes.set_arg_type arg_types key data  
  )
  
end


module ClassAttributes = struct
  type t = {
    attributes: AttrsSet.t;
    properties: AttrsSet.t;
    methods: AttributeAnalysis.CallSet.t Identifier.Map.t;
  } [@@deriving sexp, equal]

  let empty = {
    attributes=AttrsSet.empty;
    properties=AttrsSet.empty;
    methods=Identifier.Map.empty;
  }
  
  let pp_attrs_set format attrs_set =
    let attrs_string = (AttrsSet.fold attrs_set ~init:"{" ~f:(fun acc attr ->
      acc ^ ", " ^ attr
    )) ^ "}"
  in
  Format.fprintf format "%s" attrs_string

  let pp_method_set format method_set =
    let attrs_string = (Identifier.Map.fold method_set ~init:"{" ~f:(fun ~key:method_ ~data:_ acc ->
      acc ^ ", " ^ method_
    )) ^ "}"
  in
  Format.fprintf format "%s" attrs_string

  let pp format { attributes; properties; methods; } =
    Format.fprintf format "
      [[ Attributes ]]\n%a\n
      [[ Properties ]]\n%a\n
      [[ Methods ]]\n%a\n
    "
    pp_attrs_set attributes pp_attrs_set properties pp_method_set methods

  let join left right =
    {
      attributes=AttrsSet.union left.attributes right.attributes;
      properties=AttrsSet.union left.properties right.properties;
      methods=Identifier.Map.merge left.methods right.methods ~f:(fun ~key:_ data ->
        match data with
        | `Both (left, right) -> Some (AttributeAnalysis.CallSet.union left right)
        | `Left v | `Right v -> Some v
      );
    }

  let add_attribute ({ attributes; _} as t) attr =
    { t with attributes=AttrsSet.add attributes attr }

  let add_property ({ properties; _} as t) prop =
    { t with properties=AttrsSet.add properties prop }

  let add_method ~call_info ({ methods; _} as t) meth =
    let call_set = 
      Identifier.Map.find methods meth 
      |> Option.value ~default:AttributeAnalysis.CallSet.empty
    in
    { t with methods=Identifier.Map.set methods ~key:meth ~data:(AttributeAnalysis.CallSet.add call_set call_info) }

  let get_class_property { properties; _ } = properties

  let is_used_attr { attributes; properties; methods; } attr =
    let methods = AttrsSet.of_list (Identifier.Map.keys methods) in
    AttrsSet.exists (AttrsSet.union_list [attributes; properties; methods;]) ~f:(fun elem -> String.equal elem attr)
    (*
  let total_attributes { attributes; properties; methods; } =
    AttrsSet.union_list [attributes; properties; methods;]


  let is_subset_with_total_attributes t attributes =
    AttrsSet.is_subset attributes ~of_:(total_attributes t)
    *)

  let str_attributes () =
    let startswith_data = { AttributeAnalysis.CallInfo.empty with position=1; } |> AttributeAnalysis.CallSet.singleton in
    let endswith_data = { AttributeAnalysis.CallInfo.empty with position=1; } |> AttributeAnalysis.CallSet.singleton in
    let getitem_data = { AttributeAnalysis.CallInfo.empty with position=1; } |> AttributeAnalysis.CallSet.singleton in
    let methods = 
      Identifier.Map.empty
      |> Identifier.Map.set ~key:"startswith" ~data:startswith_data
      |> Identifier.Map.set ~key:"endswith" ~data:endswith_data
      |> Identifier.Map.set ~key:"__getitem__" ~data:getitem_data
    in
    
    { empty with methods }
end

module StubInfo = struct
  type info = {
    attribute_set: AttrsSet.t;
    call_set: AttributeAnalysis.CallSet.t Identifier.Map.t;
  } [@@deriving equal, sexp]

  type t = info Identifier.Map.t [@@deriving equal, sexp]

  let empty = Identifier.Map.empty

  let make_call_info posarg defaults vararg kwarg =
    let call_info = { 
      CallInfo.empty with
      position=List.length posarg; 
      default=List.fold defaults ~init:Identifier.Set.empty ~f:(fun acc default -> Identifier.Set.add acc default);
      star=vararg;
      double_star=kwarg;
    } 
    in
    AttributeAnalysis.CallSet.singleton call_info
   
  let pp_attribute_set format t =
    AttrsSet.iter t ~f:(fun attr ->
      Format.fprintf format "%s, " attr
    )

  let pp format t =
    Identifier.Map.iteri t ~f:(fun ~key ~data:{ attribute_set; _ } ->
      Format.fprintf format "%s => %a\n" key pp_attribute_set attribute_set
    )

  let is_empty = Identifier.Map.is_empty

  let create () =
    let home =
      try
        Sys.getenv "HOME"
      with Not_found -> failwith "HOME environment variable is not set"
    in

    let stub_json = 
      match home with
      | Some home -> Yojson.Basic.from_file (home ^ "/Pyinder/stubs/typeshed/typeshed-master/stub_info.json")
      | _ -> failwith "HOME environment variable is not set"
    in
    let open Yojson.Basic.Util in
    let json_list = stub_json |> to_list in

    let x = 
      List.fold json_list ~init:empty ~f:(fun acc json -> 
        let cls_name = json |> member "name" |> to_string in
        let attributes = json |> member "info" |> member "attributes" |> to_list |> filter_string in
        let properties = json |> member "info" |> member "properties" |> to_list |> filter_string in
        let attribute_set = AttrsSet.union_list [AttrsSet.of_list attributes; AttrsSet.of_list properties;] in
        let methods = json |> member "info" |>  member "method" |> to_list in

        (* Log.dump "Name : %s" name;
        Log.dump "Attributes : %s" (String.concat ~sep:", " attributes);
        Log.dump "Properties : %s" (String.concat ~sep:", " properties); *)

        let call_set =
          List.fold methods ~init:Identifier.Map.empty ~f:(fun acc method_json -> 
            let name = method_json |> member "name" |> to_string in
            let posargs = method_json |> member "info" |> member "posargs" |> to_list |> filter_string in
            let defaults = method_json |> member "info" |> member "defaults" |> to_list |> filter_string in
            let vararg = method_json |> member "info" |> member "vararg" |> to_bool in
            let kwarg = method_json |> member "info" |> member "kwarg" |> to_bool in  

            let call_set = make_call_info posargs defaults vararg kwarg in
            Identifier.Map.set ~key:name ~data:call_set acc
            (* Log.dump "Method Name : %s" name;
            Log.dump "Posargs : %s" (String.concat ~sep:", " posargs);
            Log.dump "Defaults : %s" (String.concat ~sep:", " defaults);
            Log.dump "Vararg : %b" vararg;
            Log.dump "Kwarg : %b" kwarg; *)
          )
        in

        let info = { attribute_set; call_set; } in
        Identifier.Map.set ~key:cls_name ~data:info acc
      )
    in

    x
end

module ClassSummary = struct
  type t = {
    class_var_type: TypeFromFuncs.t ReferenceMap.t;
    temp_class_var_type : TypeFromFuncs.t ReferenceMap.t;
    join_temp_class_var_type : TypeFromFuncs.t ReferenceMap.t;
    seen_var_type: Reference.Set.t ReferenceMap.t;
    class_attributes: ClassAttributes.t;
    usage_attributes: AttributeStorage.t;
    change_set : ReferenceSet.t;
    (* should_analysis: bool *)
  } [@@deriving sexp, equal]

  let empty = {
    class_var_type=ReferenceMap.empty;
    seen_var_type=ReferenceMap.empty;
    temp_class_var_type=ReferenceMap.empty;
    join_temp_class_var_type=ReferenceMap.empty;
    (* updated_var = ReferenceSet.empty; *)
    class_attributes=ClassAttributes.empty;
    usage_attributes=AttributeStorage.empty;
    change_set=ReferenceSet.empty;
    (* should_analysis=true; *)
  }

  let add_implicit_to_join ({ join_temp_class_var_type; _ } as t) reference typ =
    let empty_typefuncs = TypeFromFuncs.empty in
    let typefuncs = TypeFromFuncs.set ~key:typ ~data:Reference.Set.empty empty_typefuncs in
    { t with join_temp_class_var_type=ReferenceMap.set join_temp_class_var_type ~key:reference ~data:typefuncs; }

  let filter_seen_var ~func_name { seen_var_type; _ } var_set =
    let var_set = Reference.Set.filter var_set ~f:(fun var -> 
      
      if Reference.is_self var
      then (
        match ReferenceMap.find seen_var_type func_name with
        | Some refset -> not (Reference.Set.exists refset ~f:(fun ref_ -> 
          (* Log.dump "?? %a vs %a" Reference.pp (Reference.drop_head var) Reference.pp ref_; *)
          Reference.is_contain ~base:(Reference.drop_head var) ~target:ref_
        ))
        | _ -> true
      ) else true
    ) 
    in
    var_set
    

  (* let should_analysis { should_analysis; _ } = should_analysis *)
  let get_class_var_type { class_var_type; _ } = class_var_type

  let get_temp_class_var_type { temp_class_var_type; _ } = temp_class_var_type

  let get_usage_attributes { usage_attributes; _ } = usage_attributes

  let get_properties { class_attributes; _ } = ClassAttributes.get_class_property class_attributes

  let add_attribute ({ class_attributes; _} as t) attr =
    let class_attributes = ClassAttributes.add_attribute class_attributes attr in
    { t with class_attributes }

  let add_property ({ class_attributes; _} as t) property =
    let class_attributes = ClassAttributes.add_property class_attributes property in
    { t with class_attributes }

  let add_method ~call_info ({ class_attributes; _} as t) meth =
    let class_attributes = ClassAttributes.add_method class_attributes ~call_info meth in
    { t with class_attributes }

  let add_usage_attributes ({ usage_attributes; _ } as t) storage =
    { t with usage_attributes=AttributeStorage.join usage_attributes storage }


  let update_unseen_temp_class_var_type ~type_join ~updated_vars ({ class_var_type; temp_class_var_type; join_temp_class_var_type; _ } as t) =
    let _ = type_join in
    let class_var_type =
      ReferenceMap.fold2 temp_class_var_type join_temp_class_var_type ~init:class_var_type ~f:(fun ~key ~data acc ->
        if Reference.Set.mem updated_vars key then acc
        else (
          match data with
          | `Left data -> 
            (* ReferenceMap.iteri join_temp_class_var_type ~f:(fun ~key ~data -> Log.dump "JOIN : %a ---> %a" Reference.pp key Type.pp data); *)
            ReferenceMap.update acc key ~f:(fun d -> 
            match d with
            | Some t -> 
              (* Log.dump "Unseen %a ==> %a" Reference.pp key TypeFromFuncs.pp data; *) 
              TypeFromFuncs.join t data
            | _ -> data
          )
          | _ -> acc
        )
      )
    in

    { t with class_var_type; }

  let update_unseen_temp_class_var_type_to_unknown ({ class_var_type; temp_class_var_type; _ } as t) =
    let class_var_type =
      ReferenceMap.fold temp_class_var_type ~init:class_var_type ~f:(fun ~key ~data:_ acc ->
        if ReferenceMap.mem class_var_type key then acc
        else (
          (* Log.dump "??? %a" Reference.pp key; *)
          let data = TypeFromFuncs.empty |> TypeFromFuncs.set ~key:Type.Unknown ~data:Reference.Set.empty in
          ReferenceMap.set acc ~key ~data
        )
      )
    in

    { t with class_var_type; }

  let update_unseen_temp_class_var_type_to_var ({ class_var_type; temp_class_var_type; _ } as t) =
    let class_var_type =
      ReferenceMap.fold temp_class_var_type ~init:class_var_type ~f:(fun ~key ~data acc ->
        (* Log.dump "??? %a" Reference.pp key; *)
        if ReferenceMap.mem class_var_type key then acc
        else (
          (* Log.dump "OH"; *)
          ReferenceMap.set acc ~key ~data
        )
      )
    in

    { t with class_var_type; }

  let set_class_var_type_to_empty t =
    { t with class_var_type=ReferenceMap.empty }

  let set_temp_class_var_type_from_join t =
    { t with temp_class_var_type=t.join_temp_class_var_type; join_temp_class_var_type=ReferenceMap.empty; }

  let set_join_temp_class_var_type_to_empty t =
    { t with join_temp_class_var_type=ReferenceMap.empty }

  let get_class_vars { class_var_type; _ } =
    let update_var_list = ReferenceMap.keys class_var_type in
    let updated_var = List.fold update_var_list ~init:Reference.Set.empty ~f:(fun updated_var var -> ReferenceSet.add updated_var var) in
    updated_var

  let get_class_property { class_attributes; _ } =
    ClassAttributes.get_class_property class_attributes

  let check_attr ~attr { class_attributes; _ } =
    ClassAttributes.is_used_attr class_attributes attr
  

  let update_default_value prev next =
    let class_var_type = ReferenceMap.update_default_value prev.class_var_type next.class_var_type in
    (* ReferenceMap.iteri next.class_var_type ~f:(fun ~key ~data -> Log.dump "%a ==> %a" Reference.pp key Type.pp data);
    Log.dump "---";
    ReferenceMap.iteri class_var_type ~f:(fun ~key ~data -> Log.dump "%a ==> %a" Reference.pp key Type.pp data); *)
    let change_set = (ReferenceMap.diff_var_from_funcs class_var_type next.class_var_type) in
    (* Reference.Set.iter change_set ~f:(fun r -> Log.dump ">>> %a" Reference.pp r); *)
    {
      next with class_var_type; change_set;
    }

  let join_only_attribute left right =
    let class_attributes = ClassAttributes.join left.class_attributes right.class_attributes in
    let usage_attributes = AttributeStorage.join left.usage_attributes right.usage_attributes in
    {
      right with class_attributes; usage_attributes;
    }

  let join ~type_join left right =
    let _ = type_join in
    let class_var_type = ReferenceMap.join_var_from_funcs left.class_var_type right.class_var_type in
    let seen_var_type = ReferenceMap.merge left.seen_var_type right.seen_var_type ~f:(fun ~key:_ data ->
        match data with
        | `Both (left, right) -> Some (Reference.Set.union left right)
        | `Left data | `Right data -> Some data
      )  
    in
    let join_temp_class_var_type = ReferenceMap.join_var_from_funcs left.temp_class_var_type right.join_temp_class_var_type in
    (* let update_var_list = ReferenceMap.keys left.class_var_type @ ReferenceMap.keys left.temp_class_var_type in
    let updated_var = List.fold update_var_list ~init:right.updated_var ~f:(fun updated_var var -> ReferenceSet.add updated_var var) in *)
    let change_set = 
      ReferenceSet.union right.change_set (ReferenceMap.diff_var_from_funcs right.class_var_type class_var_type) 
      |> ReferenceSet.union (ReferenceMap.diff_var_from_funcs join_temp_class_var_type right.join_temp_class_var_type)
    in

    (* ReferenceSet.iter change_set ~f:(fun c -> Log.dump "CHANGE : %a" Reference.pp c); *)

    (* let should_analysis = right.should_analysis || ((not (ReferenceMap.equal Type.equal class_var_type right.class_var_type)) && left.should_analysis) in *)
    {
      class_var_type;
      seen_var_type;
      temp_class_var_type=right.temp_class_var_type;
      join_temp_class_var_type;
      (* updated_var; *)
      class_attributes = ClassAttributes.join left.class_attributes right.class_attributes;
      usage_attributes = AttributeStorage.join left.usage_attributes right.usage_attributes;
      change_set;
    }

  let ref_set_pp format refset =
    Reference.Set.iter refset ~f:(fun ref_ ->
      Format.fprintf format "%a, " Reference.pp ref_
    )

  let pp_class_var_type format { class_var_type; join_temp_class_var_type; temp_class_var_type; seen_var_type; _ } =
      Format.fprintf format "[[[ Class Variable Type ]]] 
      \n%a\n[[[ Classs JOIN Variable Type ]]]\n%a\n
      \n[[[ Classs Temp Variable Type ]]]\n%a\n
      \n[[[ Seen Variable Type ]]]\n%a\n" 
      (ReferenceMap.pp ~data_pp:TypeFromFuncs.pp) class_var_type 
      (ReferenceMap.pp ~data_pp:TypeFromFuncs.pp) join_temp_class_var_type  
      (ReferenceMap.pp ~data_pp:TypeFromFuncs.pp) temp_class_var_type 
      (ReferenceMap.pp ~data_pp:ref_set_pp) seen_var_type

  let pp_class_info format { class_attributes; _ } =
      Format.fprintf format "[[[ Class Info ]]] \n%a\n" ClassAttributes.pp class_attributes

  let pp_usage_attributes format { usage_attributes; _ } =
      Format.fprintf format "[[[ Class Usage Attrs ]]] \n%a\n" AttributeStorage.pp usage_attributes

  let pp format t =
    Format.fprintf format "%a\n%a\n%a" pp_class_var_type t pp_class_info t pp_usage_attributes t

  let has_analysis { change_set; _ } = not (ReferenceSet.is_empty change_set)
end

module type ClassTable = sig
  type t = ClassSummary.t ClassHash.t 
end

module ClassTable = struct
  type t = ClassSummary.t ClassHash.t [@@deriving sexp, equal]

  let empty = ClassHash.create

  let find_default t name = ClassHash.find t name |> Option.value ~default:ClassSummary.empty 


  let filter_seen_var ~class_name ~func_name ~var_set t =
    let class_info = find_default t class_name in
    ClassSummary.filter_seen_var ~func_name class_info var_set


  let add ~class_name ~data ~f t =
    let class_info = find_default t class_name in
    ClassHash.set t ~key:class_name ~data:(f class_info data)

  let add_implicit_to_join t class_name reference typ =
    let class_info = find_default t class_name in
    let class_info = ClassSummary.add_implicit_to_join class_info reference typ in
    ClassHash.set t ~key:class_name ~data:class_info

  let add_attribute t class_name attr = add t ~class_name ~data:attr ~f:ClassSummary.add_attribute

  let add_property t class_name property = add t ~class_name ~data:property ~f:ClassSummary.add_property

  let add_method ~call_info t class_name meth = add t ~class_name ~data:meth ~f:(ClassSummary.add_method ~call_info)

  let add_usage_attributes t class_name storage = add t ~class_name ~data:storage ~f:ClassSummary.add_usage_attributes

  let update_unseen_temp_class_var_type ~type_join ~updated_vars t =
    ClassHash.mapi_inplace t ~f:(fun ~key ~data:class_info -> 
      let updated_vars = Reference.Map.find updated_vars key |> Option.value ~default:Reference.Set.empty in
      (ClassSummary.update_unseen_temp_class_var_type ~type_join ~updated_vars class_info)
    )

  let update_unseen_temp_class_var_type_to_unknown t =
    ClassHash.mapi_inplace t ~f:(fun ~key:_ ~data:class_info -> 
      ClassSummary.update_unseen_temp_class_var_type_to_unknown class_info
    )

  let update_unseen_temp_class_var_type_to_var t =
    ClassHash.mapi_inplace t ~f:(fun ~key:_ ~data:class_info -> 
      ClassSummary.update_unseen_temp_class_var_type_to_var class_info
    )

  let set_all_class_var_type_to_empty t =
    ClassHash.map_inplace t ~f:(fun class_info -> (ClassSummary.set_class_var_type_to_empty class_info))

  let set_all_temp_class_var_type_from_join t =
    ClassHash.map_inplace t ~f:(fun class_info -> (ClassSummary.set_temp_class_var_type_from_join class_info))

  let set_all_join_temp_class_var_type_to_empty t =
    ClassHash.map_inplace t ~f:(fun class_info -> (ClassSummary.set_join_temp_class_var_type_to_empty class_info))
    
  let set_class_info t class_name class_info =
    ClassHash.set t ~key:class_name ~data:class_info

  let get_class_vars t =
    ClassHash.fold t ~init:Reference.Map.empty ~f:(fun ~key ~data acc ->
      let data = ClassSummary.get_class_vars data in
       Reference.Map.set ~key ~data acc
    )

  let get ~class_name ~f t = 
    let class_info = find_default t class_name in
    f class_info

  let get_class_info t class_name = get t ~class_name ~f:(fun x -> x)

  let get_class_var_type t class_name = get t ~class_name ~f:ClassSummary.get_class_var_type

  let get_temp_class_var_type t class_name = get t ~class_name ~f:ClassSummary.get_temp_class_var_type

  let get_usage_attributes t class_name = get t ~class_name ~f:ClassSummary.get_usage_attributes

  let get_class_property t class_name = get t ~class_name ~f:ClassSummary.get_class_property

  let check_attr ~attr t class_name = get t ~class_name ~f:(ClassSummary.check_attr ~attr)

  let update_default_value prev next =
    ClassHash.join prev next ~equal:ClassSummary.equal ~data_join:ClassSummary.update_default_value

  let join_only_attribute left right =
    ClassHash.join left right ~equal:ClassSummary.equal ~data_join:(ClassSummary.join_only_attribute)

  let join ~type_join left right =
    ClassHash.join left right ~equal:ClassSummary.equal ~data_join:(ClassSummary.join ~type_join)

  let pp format t =
    ClassHash.iteri ~f:(fun ~key ~data ->
      Format.fprintf format "[[[ Class : %a ]]] \n%a\n" Reference.pp key ClassSummary.pp data
    ) t

  let get_analysis_set ~get_functions ~get_usage_self_attributes t =
    let _ = get_usage_self_attributes in
    ClassHash.fold t ~init:ReferenceMap.empty ~f:(fun ~key ~data map ->
      if ClassSummary.has_analysis data then (
        get_functions key
        |> ReferenceSet.filter ~f:(fun func_name -> 
          not (ReferenceSet.is_empty (ReferenceSet.inter data.change_set (get_usage_self_attributes func_name)))
        )
        |> ReferenceSet.fold ~init:map ~f:(fun map ref -> 
          ReferenceMap.set map ~key:ref ~data:(ArgTypesOptSet.singleton None))
      )
      else
        map
    )

  let has_analysis t =
    ClassHash.fold t ~init:false ~f:(fun ~key:_ ~data acc ->
      acc || ClassSummary.has_analysis data
    )

  let get_functions_of_class ~get_functions t =
    ClassHash.mapi t ~f:(fun ~key ~data:_ ->
        get_functions key |> ReferenceSet.to_list
    )
    |> ClassHash.data
end

(* module type FunctionSummary = sig
  type t = {
    arg_types: ArgTypes.t; (* Argumets의 Input Type *)
    arg_annotation: ArgTypes.t; (* Argument Annotation *)
    return_var_type: Type.t ReferenceMap.t; (* Return 했을 때의 parameter 정보 *)
    return_type: Type.t; (* Function의 Return Type *)
    callers: CallerSet.t;
    usage_attributes : AttributeStorage.t;
    (*usedef_tables: UsedefStruct.t option;*)
  }

  val add_return_var_type : t -> Reference.t -> Type.t -> t
end *)

module Signatures = struct
  type return_info = {
    return_var_type: Type.t ReferenceMap.t; (* Return 했을 때의 parameter 정보 *)
    return_type: Type.t; (* Function의 Return Type *)
    should_analysis: bool;
    caller_analysis: bool;
    caller_set : ReferenceSet.t;
  } [@@deriving sexp, equal]

  module ArgTypesMap = Map.Make (ArgTypes)

  type t = return_info ArgTypesMap.t [@@deriving sexp, equal](* Argumets의 Type*)

  let yojson_of_return_info : return_info -> Yojson.Safe.json =
    (* let open Yojson.Basic in *)
    function
    | { return_var_type; return_type; _ } ->
      `Assoc [
        ("return_var_type", ReferenceMap.yojson_of_t ~yojson_of_data:Type.to_yojson return_var_type);
        ("return_type", Type.to_yojson return_type);
      ]

  let yojson_of_t t : Yojson.Safe.t =
    (* let open Yojson.Basic in *)
    let f (arg_types, return_info) =
      `Assoc [
        ("arg_types", ArgTypes.yojson_of_t arg_types);
        ("return_info", yojson_of_return_info return_info);
      ]
    in
    `List (List.map (ArgTypesMap.to_alist t) ~f)

  let empty = ArgTypesMap.empty

  let empty_return_info = {
    return_var_type = ReferenceMap.empty;
    return_type = Bottom;
    should_analysis = true;
    caller_analysis = true;
    caller_set = ReferenceSet.empty;
  }

  (* let equal_except_parameter left right =
    Type.equal left.return_type right.return_type &&
    ReferenceMap.fold2 left.return_var_type right.return_var_type ~init:true ~f:(fun ~key ~data flag ->
        if Reference.is_self key || Reference.is_cls key
        then (
          match data with
          | `Both (v1, v2) -> flag && Type.equal v1 v2
          | _ -> false
        ) else (
          flag
        )
    ) *)

  let update_return_info ~type_join left right =
    (* let timer = Timer.start () in *)

    let return_var_type = (* ReferenceMap.join_type ~type_join left.return_var_type *) right.return_var_type in
    (* let tt0 = Timer.stop_in_sec timer in *)
    let return_type = type_join left.return_type right.return_type in
    (* let tt1 = Timer.stop_in_sec timer in *)
    let should_analysis = left.should_analysis || right.should_analysis in
    let caller_analysis = (not (Type.equal return_type right.return_type)) in
    let caller_set = ReferenceSet.union left.caller_set right.caller_set in
    (* let tt2 = Timer.stop_in_sec timer in
    let total_time = Timer.stop_in_sec timer in *)
    let x =
    {
      return_var_type; (* Return 했을 때의 parameter 정보 *)
      return_type; (* Function의 Return Type *)
      should_analysis;
      caller_analysis;
      caller_set;
    }
  in

    
    (* if Float.(>.) total_time 0.001 then (
      Log.dump "HOODA %.5f %.5f %.5f" tt0 tt1 tt2;
      Log.dump "LEFT %a RIGHT %a" Type.pp left.return_type Type.pp right.return_type;
    );   *)
  
    x

  let join_return_info ~type_join left right =

    {
      return_var_type = ReferenceMap.join_type ~type_join left.return_var_type right.return_var_type; (* Return 했을 때의 parameter 정보 *)
      return_type = type_join left.return_type right.return_type; (* Function의 Return Type *)
      should_analysis = left.should_analysis || right.should_analysis;
      caller_analysis = left.caller_analysis || right.caller_analysis;
      caller_set = ReferenceSet.union left.caller_set right.caller_set;
    }
    

(*   let merge_arg_types ~type_join arg_types prev_key prev_data =
    let new_arg_types, flag =
      ArgTypesMap.fold arg_types ~init:(ArgTypesMap.empty, false) ~f:(fun ~key:next_key ~data:next_data (new_arg_types, flag) ->
        match ArgTypes.arg_merge prev_key next_key with
        | Some new_arg ->
          let return_info = 
            if equal_return_info prev_data next_data then next_data else (update_return_info ~type_join prev_data next_data) 
          in
          ArgTypesMap.set new_arg_types ~key:new_arg ~data:return_info, true

        | None -> ArgTypesMap.set new_arg_types ~key:next_key ~data:next_data, flag
      )
    in
    if flag then new_arg_types else ArgTypesMap.set arg_types ~key:prev_key ~data:prev_data *)

  let update ~type_join prev next =
    (* ArgTypesMap.fold ~init:next ~f:(fun ~key:prev_key ~data:prev_data arg_types ->
      merge_arg_types ~type_join arg_types prev_key prev_data
      (* let new_arg_types, flag =
        ArgTypesMap.fold arg_types ~init:(ArgTypesMap.empty, false) ~f:(fun ~key:next_key ~data:next_data (new_arg_types, flag) ->
          match ArgTypes.arg_merge prev_key next_key with
          | Some new_arg ->
            let return_info = 
              if equal_return_info prev_data next_data then next_data else (update_return_info ~type_join prev_data next_data) 
            in
            ArgTypesMap.set new_arg_types ~key:new_arg ~data:return_info, true

          | None -> ArgTypesMap.set new_arg_types ~key:next_key ~data:next_data, flag
        )
      in

      if flag then new_arg_types else ArgTypesMap.set arg_types ~key:prev_key ~data:prev_data *)
    ) prev *)

    ArgTypesMap.merge ~f:(fun ~key:_ data ->
      match data with
      | `Left v | `Right v -> Some v
      | `Both (v1, v2) -> (* if equal_return_info v1 v2 then Some v1 else  *)Some (update_return_info ~type_join v1 v2)
    ) prev next


  

  let pp_return_info format { return_var_type; return_type; should_analysis; _ } =
    Format.fprintf format 
    "\n<Return Var Type>\n%a\n\n<Return Type> %a\nShould : %b"
    (ReferenceMap.pp ~data_pp:Type.pp) return_var_type 
    Type.pp return_type should_analysis

  let pp format t =
    ArgTypesMap.iteri t ~f:(fun ~key ~data ->
      Format.fprintf format "%a ==> %a" ArgTypes.pp key pp_return_info data
    )

  let join ~type_join left right =
    (* let timer = Timer.start () in *)
    let x = 
    ArgTypesMap.merge ~f:(fun ~key:_ data ->
      match data with
      | `Left v | `Right v -> Some v
      | `Both (v1, v2) -> if equal_return_info v1 v2 then Some v1 else Some (join_return_info ~type_join v1 v2)
    ) left right
    in
    (* let total_time = Timer.stop_in_sec timer in
    if Float.(>.) total_time 0.001 then (
      Log.dump "LEFT\n %a \nRIGHT %a" pp left pp right;
    );   *)
    x

  let find_signature t arg_types = 
    (* ArgTypesMap.filter_keys t ~f:(fun k -> ArgTypes.less_or_equal_keys arg_types k) *)
    ArgTypesMap.find t arg_types

  

  let filter_unknown arg_types =
    
    arg_types
    |> ArgTypes.map ~f:(Type.our_dict_to_dict)
    |> ArgTypes.map ~f:(Type.narrow_iterable ~max_depth:2)
    |> ArgTypes.map ~f:Type.filter_unknown
    |> ArgTypes.filter ~f:(fun data -> not (Type.is_unknown data))

    


(*   let find_return_type ~type_join t arg_types =
    let new_arg_types = filter_unknown arg_types in
    (* let timer = Timer.start () in *)
    let x =
    find_signature t new_arg_types
    |> ArgTypesMap.fold ~init:Type.Bottom ~f:(fun ~key:_ ~data acc -> 
      type_join data.return_type acc)
    in
(*       let total_time = Timer.stop_in_sec timer in
      if Float.(>.) total_time 5.0 then (
        Log.dump ">>> %a (%.3f)" Type.pp x total_time;
      ); *)
      x *)


  let add_new_signature ~join ?caller_name t arg_typ_list =
    let _ = join in
    (* TODO : is right filter unknown? *)
    (*let new_arg_types = List.fold arg_typ_list ~init:ArgTypes.empty ~f:(fun arg_types (arg, typ) -> ArgTypes.add_arg_type ~join arg_types arg (typ |> Type.filter_unknown)) in*)
    let new_arg_types = filter_unknown arg_typ_list in

    match find_signature t new_arg_types with
    (* | signature when ArgTypesMap.is_empty signature -> 
      merge_arg_types ~type_join:join t new_arg_types empty_return_info
    | _ -> t *)
    | Some v -> 
      let data =
        (match caller_name with
        | Some caller -> { v with caller_set = ReferenceSet.add v.caller_set caller }
        | _ -> v
        )
      in
      ArgTypesMap.set t ~key:new_arg_types ~data
    | None -> 
      let data =
        (match caller_name with
        | Some caller -> { empty_return_info with caller_set = ReferenceSet.singleton caller }
        | _ -> empty_return_info
        )
      in
      ArgTypesMap.set t ~key:new_arg_types ~data

  (*let add_return_info t arg_types return_var_type return_type =
    ArgTypesMap.set t ~key:arg_types ~data:{ return_var_type; return_type; should_analysis=false; }
    *)
  let add_return_var_type t arg_types reference typ =
    let data = ArgTypesMap.find t arg_types |> Option.value ~default:empty_return_info in
    ArgTypesMap.set t ~key:arg_types ~data:{ data with return_var_type=(ReferenceMap.set data.return_var_type ~key:reference ~data:typ); }


  let add_return_type ~type_join t arg_types typ =
    let data = ArgTypesMap.find t arg_types |> Option.value ~default:empty_return_info in

    (* let x = type_join data.return_type typ in *)
    let ret_type = 
      type_join data.return_type typ 
      |> Type.narrow_iterable ~max_depth:2
      (* |> Type.narrow_return_type *) (* Baseline *)
    in
    (* Log.dump "%a + %a => %a => %a" Type.pp data.return_type Type.pp typ Type.pp x Type.pp ret_type; *)
    ArgTypesMap.set t ~key:arg_types ~data:{ data with return_type=ret_type }
    
  let set_return_var_type t arg_types return_var_type =
    let data = ArgTypesMap.find t arg_types |> Option.value ~default:empty_return_info in
    ArgTypesMap.set t ~key:arg_types ~data:{ data with return_var_type; }

  let set_return_type t arg_types return_type =
    let data = ArgTypesMap.find t arg_types |> Option.value ~default:empty_return_info in
    ArgTypesMap.set t ~key:arg_types ~data:{ data with return_type; }
  

  let get_signatures t = 
    ArgTypesMap.map t ~f:(fun data -> data.return_type)

  let get_return_info ?property t arg_types =
    match property with
    | Some true ->
      let x = ArgTypesMap.data t in
      if List.is_empty x then empty_return_info else List.hd_exn x
    | _ when not !on_dataflow ->
      let x = ArgTypesMap.data t in
      if List.is_empty x then empty_return_info else List.hd_exn x
    | _ ->
      ArgTypesMap.find t arg_types |> Option.value ~default:(
        let x = ArgTypesMap.filter t ~f:(fun return_info -> not (FunctionMap.is_empty return_info.return_var_type)) |> ArgTypesMap.data in
        if List.is_empty x then empty_return_info else List.hd_exn x
      )

  let get_return_var_type t arg_types =
    let return_info = get_return_info t arg_types in
    return_info.return_var_type

  let get_return_type ~type_join ?property t arg_types =
    if !type_sensitive then (
      let new_arg_types = filter_unknown arg_types in
      let return_info = get_return_info ?property t new_arg_types in
      (match return_info.return_type with
      | Type.Bottom when String.equal (load_mode ()) "error" ->
        ArgTypesMap.fold t ~init:Type.Unknown ~f:(fun ~key:_ ~data acc ->
          type_join data.return_type acc  
        )
      | return_type when String.equal (load_mode ()) "error" ->
        let default_type = ArgTypesMap.data t in
        (match List.hd default_type with
        | Some default -> type_join default.return_type return_type
        | _ -> return_type
        )
        
      | t -> t
      )
    ) else (
      ArgTypesMap.fold t ~init:Type.Bottom ~f:(fun ~key:_ ~data acc -> 
        type_join data.return_type acc
      )
      |> (fun t ->
        match t with
        | Type.Bottom -> Type.Unknown
        | _ -> t  
      )
    )

    |> (fun x ->
      if !Type.element_join then Type.element_to_any x else x  
    )

  

  let get_analysis_arg_types t = 
    ArgTypesMap.filter t ~f:(fun return_info -> return_info.should_analysis)
    |> ArgTypesMap.keys

  let get_all_arg_types ~type_join t =
    ArgTypesMap.fold t ~init:ArgTypes.empty ~f:(fun ~key ~data:_ arg_types ->
      ArgTypes.join ~type_join key arg_types  
    )

  let get_module_var_type t attribute =
    let return_info_list = ArgTypesMap.data t in
    match return_info_list with
    | [] -> Type.Unknown
    | { return_var_type; _ }::_ ->

      let typ = ReferenceMap.find_by_suffix return_var_type attribute in
      (match typ with
      | Some t -> t
      | _ -> Type.Unknown
      ) 

  let end_analysis t arg_types =
    let data = ArgTypesMap.find t arg_types |> Option.value ~default:empty_return_info in
    ArgTypesMap.set t ~key:arg_types ~data:{ data with should_analysis=false; }


  let analysis_caller_set t =
    ArgTypesMap.fold t ~init:(false, ReferenceMap.empty) ~f:(fun ~key ~data:{ caller_analysis; caller_set; _ } (all_flag, acc) -> 
      if caller_analysis
      then (
        
        if ReferenceSet.is_empty caller_set
        then (all_flag, acc)
        else 
          let caller_set = ReferenceSet.fold caller_set ~init:ReferenceMap.empty ~f:(fun map caller -> 
              let arg_types_opt_set = ReferenceMap.find map caller |> Option.value ~default:ArgTypesOptSet.empty in
              ReferenceMap.set map ~key:caller ~data:(ArgTypesOptSet.add arg_types_opt_set (Some key))
            ) 
          in
          (all_flag, ReferenceMap.join caller_set acc ~data_join:ArgTypesOptSet.union ~equal:ArgTypesOptSet.equal) 
      ) 
      else (all_flag, acc) 
    )

  let change_analysis t =
    ArgTypesMap.map t ~f:(fun return_info -> { return_info with should_analysis=true;} )

  let change_analysis_of_arg_types t arg_types_opt_set =
    ArgTypesMap.mapi t ~f:(fun ~key ~data -> 
      if ArgTypesOptSet.mem arg_types_opt_set (Some key)
      then { data with should_analysis=true; }
      else data
    )    

  let change_analysis_to_false t =
    ArgTypesMap.map t ~f:(fun return_info -> { return_info with should_analysis=false;} )

  (* let should_analysis t =
    ArgTypesMap.fold t ~init:false ~f:(fun ~key:_ ~data:{ should_analysis; _ } flag -> flag || should_analysis)
 *)
  let get_should_analysis t =
    ArgTypesMap.fold t ~init:ArgTypesOptSet.empty ~f:(fun ~key ~data:{ should_analysis; _ } set -> 
      if should_analysis then
        ArgTypesOptSet.add set (Some key)
      else
        set
    )

  (* let caller_analysis t =
    ArgTypesMap.fold t ~init:false ~f:(fun ~key:_ ~data:{ caller_analysis; _ } flag -> flag || caller_analysis) *)

  (* let is_changed_return_info left right =
    ArgTypesMap.fold2 left right ~init:false ~f:(fun ~key:_ ~data flag ->
      flag ||
      match data with
      | `Left _ | `Right _ -> true
      | `Both (v1, v2) -> equal_except_parameter v1 v2
    ) *)

  let has_analysis t = 
    ArgTypesMap.fold t ~init:false ~f:(fun ~key:_ ~data:{ should_analysis; caller_analysis; _ } flag ->
      flag || should_analysis || caller_analysis
    )

  
end


module type FunctionSummary = sig
  type t = {
    signatures: Signatures.t;
    (* arg_types: ArgTypes.t; (* Argumets의 Input Type *)
    arg_annotation: ArgTypes.t; (* Argument Annotation *)
    return_var_type: Type.t ReferenceMap.t; (* Return 했을 때의 parameter 정보 *)
    return_type: Type.t; (* Function의 Return Type *) *)
    callers: CallerSet.t;
    return_annotation: Type.t;
    usage_attributes : AttributeStorage.t;
    unique_analysis : UniqueAnalysis.UniqueStruct.t;
    usedef_defined: VarTypeSet.t;
    call_chain : CallChain.t;
    unknown_decorator : bool;
    (*usedef_tables: UsedefStruct.t option;*)
  } 

  val add_return_var_type : t -> ArgTypes.t -> Reference.t -> Type.t -> t
end

module ExpressionMap = Map.Make (Expression)

module FunctionSummary = struct
  type t = {
    signatures: Signatures.t;
    preprocess: Type.t ExpressionMap.t;
    (* arg_types: ArgTypes.t; (* Argumets의 Input Type *)
    arg_annotation: ArgTypes.t; (* Argument Annotation *)
    return_var_type: Type.t ReferenceMap.t; (* Return 했을 때의 parameter 정보 *)
    return_type: Type.t; (* Function의 Return Type *) *)
    param_varset: Reference.Set.t Identifier.Map.t;
    callers: CallerSet.t;
    return_annotation: Type.t;
    usage_attributes : AttributeStorage.t;
    unique_analysis : UniqueAnalysis.UniqueStruct.t;
    usedef_defined: VarTypeSet.t;
    call_chain : CallChain.t;
    unknown_decorator : bool;
    (*usedef_tables: UsedefStruct.t option;*)
  } [@@deriving sexp, equal]

  let empty = {
    signatures=Signatures.empty;
    preprocess=ExpressionMap.empty;
    (* arg_types= ArgTypes.empty; (* Argumets의 Input Type *)
    arg_annotation= ArgTypes.empty; (* Argument Annotation *)
    return_var_type= ReferenceMap.empty; (* Return 했을 때의 parameter 정보 *)
    return_type= Type.Unknown; (* Function의 Return Type *) *)
    return_annotation=Type.Unknown;
    param_varset=Identifier.Map.empty;
    callers=CallerSet.empty;
    usage_attributes=AttributeStorage.empty;
    unique_analysis=UniqueAnalysis.UniqueStruct.empty;
    usedef_defined=VarTypeSet.empty;
    call_chain = CallChain.empty;
    unknown_decorator=false;
    (*usedef_tables=None;*)
  }

  let find_signature {signatures; unknown_decorator; _} arg_types =
    if unknown_decorator 
    then
      Signatures.find_signature signatures ArgTypes.empty
    else
      Signatures.find_signature signatures arg_types

  let add_param_varset t param_varset =
    let param_varset =
      Identifier.Map.merge t.param_varset param_varset ~f:(fun ~key:_ data ->
        match data with
        | `Left v | `Right v -> Some v
        | `Both (v1, v2) -> Some (Reference.Set.union v1 v2)
      )
    in

    { t with param_varset; }

  let get_param_varset { param_varset; _ } = param_varset

  let add_new_signature ~join ?caller_name ({signatures; unknown_decorator; callers; _ } as t) arg_type_list =
    let callers =
      match caller_name with
      | Some caller_name -> CallerSet.add callers caller_name
      | _ -> callers
    in
    if unknown_decorator then t
    else
    { t with signatures=Signatures.add_new_signature ~join ?caller_name signatures arg_type_list; callers; }
  (* let add_arg_types ~join ({arg_types; _} as t) arg_typ_list =
    { t with arg_types = List.fold arg_typ_list ~init:arg_types ~f:(fun arg_types (arg, typ) -> ArgTypes.add_arg_type ~join arg_types arg typ) }
 *)
  let add_usage_attributes ({usage_attributes; _ } as t) storage =
    let x = { t with usage_attributes=AttributeStorage.join usage_attributes storage} in
    x

  let add_return_var_type ({ signatures; _ } as t) arg_types reference typ =
    { t with signatures=(Signatures.add_return_var_type signatures arg_types reference typ); }

  let add_return_annotation t typ =
    { t with return_annotation=typ }

  let add_return_type ~type_join ({ signatures; _ } as t) arg_types typ =
    { t with signatures=(Signatures.add_return_type ~type_join signatures arg_types typ); }

  let set_return_var_type ({ signatures; _ } as t) arg_types return_var_type =
    { t with signatures=(Signatures.set_return_var_type signatures arg_types return_var_type); }

  let set_return_type ({ signatures; _ } as t) arg_types return_type =
    { t with signatures=(Signatures.set_return_type signatures arg_types return_type); }

  let set_preprocess ({ preprocess; _ } as t) expression typ =
    { t with preprocess=(ExpressionMap.set preprocess ~key:expression ~data:typ)}

  let set_callers t callers =
    { t with callers }

  let set_usage_attributes t usage_attributes =
    { t with usage_attributes }

  let set_unique_analysis t unique_analysis =
    { t with unique_analysis }

  let set_usedef_defined t usedef_defined =
    { t with usedef_defined; }

  let set_call_chain t call_chain =
    { t with call_chain; }
  let set_unknown_decorator t =
    { t with unknown_decorator=true; }

  (* let add_return_var_type ({ return_var_type; _ } as t) reference typ =
    { t with return_var_type=(ReferenceMap.set return_var_type ~key:reference ~data:typ); } *)

  let add_caller ({ callers; _ } as t) caller =
    { t with callers=(CallerSet.add callers caller); }
  
  (* let divide_caller { callers; _ } = *)
    

(*     let set_arg_types t arg_types = 
    { t with arg_types }

  let set_arg_annotation t arg_annotation = 
    { t with arg_annotation }

  let set_return_var_type t return_var_type =
    { t with return_var_type; }

  let set_return_type t return_type =
    { t with return_type }
 *)
    (*
  let set_usedef_tables t usedef_tables =
    { t with usedef_tables; }

  let get_usedef_tables {usedef_tables; _} = usedef_tables
    *)

  (* let get_arg_types { arg_types; _ } = arg_types

  let get_arg_annotation { arg_annotation; _ } = arg_annotation 
  
  let get_return_var_type { return_var_type; _} = return_var_type *)

  let get_signatures { signatures; _ } = Signatures.get_signatures signatures

  let get_return_var_type { signatures; _ } arg_types = Signatures.get_return_var_type signatures arg_types


  let get_return_annotation { return_annotation; _ } = return_annotation

  let get_return_type ~type_join ?property { signatures; _ } arg_types = Signatures.get_return_type ~type_join ?property signatures arg_types

  let get_callers { callers; _ } = callers

  let get_usage_attributes { usage_attributes; _ } = usage_attributes
  (* let get_return_type {return_type; _} = return_type *)

  let get_preprocess { preprocess; _} = preprocess

  let get_unique_analysis { unique_analysis; _ } = unique_analysis

  let get_usedef_defined { usedef_defined; _ } = usedef_defined

  let get_unknown_decorator { unknown_decorator; _ } = unknown_decorator

  let get_call_chain { call_chain; _ } = call_chain


  let join ~type_join left right = 
    (*
    let usedef_tables = 
      (match left.usedef_tables, right.usedef_tables with
      | None, None -> None
      | Some t1, Some t2 -> 
        if UsedefStruct.equal t1 t2 then Some t1 else raise NotEqualException
      | Some t, None | None, Some t -> Some t
      )
    in
    *)

    let signatures=Signatures.join ~type_join left.signatures right.signatures in

    let preprocess=
      ExpressionMap.merge left.preprocess right.preprocess ~f:(fun ~key:_ data ->
        match data with
        | `Left v | `Right v -> Some v
        | `Both (v1, v2) -> Some (type_join v1 v2)    
      )
    in

    let param_varset =
      Identifier.Map.merge left.param_varset right.param_varset ~f:(fun ~key:_ data ->
        match data with
        | `Left v | `Right v -> Some v
        | `Both (v1, v2) -> Some (Reference.Set.union v1 v2)
      )
    in

    let return_annotation =
      match left.return_annotation, right.return_annotation with
      | Type.Unknown, t | t, Type.Unknown -> t
      | _ -> left.return_annotation
    in
    let callers=CallerSet.union left.callers right.callers in
    let usage_attributes=AttributeStorage.join left.usage_attributes right.usage_attributes in
    let usedef_defined=VarTypeSet.join left.usedef_defined right.usedef_defined in 

  {
    signatures;
    preprocess;
    callers;
    param_varset;
    return_annotation;
    usage_attributes;
    unique_analysis=UniqueAnalysis.UniqueStruct.join left.unique_analysis right.unique_analysis; 
    usedef_defined;
    call_chain = CallChain.join left.call_chain right.call_chain;
    unknown_decorator=left.unknown_decorator || right.unknown_decorator
    (*usedef_tables=usedef_tables;*)
  }
(*   let join ~type_join left right = 
    (*
    let usedef_tables = 
      (match left.usedef_tables, right.usedef_tables with
      | None, None -> None
      | Some t1, Some t2 -> 
        if UsedefStruct.equal t1 t2 then Some t1 else raise NotEqualException
      | Some t, None | None, Some t -> Some t
      )
    in
    *)

    let arg_types=ArgTypes.join ~type_join left.arg_types right.arg_types in
    let arg_annotation=ArgTypes.join ~type_join left.arg_annotation right.arg_annotation in
    let return_var_type=ReferenceMap.join_type ~type_join left.return_var_type right.return_var_type in
    let return_type=type_join left.return_type right.return_type in
    let callers=CallerSet.union left.callers right.callers in
    let usage_attributes=AttributeStorage.join left.usage_attributes right.usage_attributes in

  {
    arg_types;
    arg_annotation;
    return_var_type;
    return_type;
    callers;
    usage_attributes;
    (*usedef_tables=usedef_tables;*)
  } *)

(*   let join_return_type ~type_join ({return_type=origin; _} as t) return_type =
    { t with return_type=type_join origin return_type; } *)

  let pp_reference_set ~data_pp format t =
      ReferenceSet.iter ~f:(fun data ->
        Format.fprintf format "%a, " data_pp data
      ) t

  let pp format { signatures; usage_attributes; callers; unknown_decorator; _ } =
    Format.fprintf format 
      "<Signatures>\n%a\n\n<Usage Attributes>\n%a\n\n<Callers>\n%a\n\n==>%b\n\n" 
      Signatures.pp signatures 
      AttributeStorage.pp usage_attributes
      (pp_reference_set ~data_pp:Reference.pp) callers
      unknown_decorator
      (* UniqueAnalysis.UniqueStruct.pp unique_analysis *)
(*   let pp format {arg_types; arg_annotation; return_var_type; return_type; usage_attributes; callers; _} =
    Format.fprintf format 
      "<Arg Types>\n%a\n\n<Arg Anno>\n%a\n\n<Return Var Type>\n%a\n\n<Return Type> %a\n\n<Usage Attributes>\n%a\n<Callers>\n%a\n" 
     ArgTypes.pp arg_types 
     ArgTypes.pp arg_annotation
     (ReferenceMap.pp ~data_pp:Type.pp) return_var_type 
     Type.pp return_type 
     AttributeStorage.pp usage_attributes
     (pp_reference_set ~data_pp:Reference.pp) callers *)

    let update ~type_join prev next = 
      
      (*
      let usedef_tables = 
        (match left.usedef_tables, right.usedef_tables with
        | None, None -> None
        | Some t1, Some t2 -> 
          if UsedefStruct.equal t1 t2 then Some t1 else raise NotEqualException
        | Some t, None | None, Some t -> Some t
        )
      in
      *)
      (* let timer = Timer.start () in *)
      let signatures=Signatures.update ~type_join prev.signatures next.signatures in
      (* let tt = Timer.stop_in_sec timer in *)
      let preprocess = next.preprocess
        (* ExpressionMap.merge prev.preprocess next.preprocess ~f:(fun ~key:_ data ->
          match data with
          | `Left v | `Right v -> Some v
          | `Both (v1, v2) -> Some (type_join v1 v2)    
        ) *)
      in

      let param_varset =
        Identifier.Map.merge prev.param_varset next.param_varset ~f:(fun ~key:_ data ->
          match data with
          | `Left v | `Right v -> Some v
          | `Both (v1, v2) -> Some (Reference.Set.union v1 v2)
        )
      in

      (* if !debug then
        Log.dump "OK!!!! %a" Signatures.pp signatures; *)

      let callers= 
      CallerSet.union prev.callers next.callers 
      in

      let return_annotation =
        match prev.return_annotation, next.return_annotation with
        | Type.Unknown, t | t, Type.Unknown -> t
        | _ -> prev.return_annotation
      in
      (* let tt1 = Timer.stop_in_sec timer in *)
      let usage_attributes = (* next.usage_attributes *) AttributeStorage.join prev.usage_attributes next.usage_attributes in
      let usedef_defined=VarTypeSet.join prev.usedef_defined next.usedef_defined in 
      (* let tt2 = Timer.stop_in_sec timer in *)
      (* let total_time = Timer.stop_in_sec timer in
      if Float.(>.) total_time 0.01 then (
        Log.dump "GOODA %.3f %.3f" tt total_time;
        (* Log.dump "Left : %a\nRight : %a\n" Signatures.pp prev.signatures Signatures.pp next.signatures; *)
      );   *)
      
      
    {
      signatures;
      preprocess;
      callers;
      param_varset;
      return_annotation;
      usage_attributes;
      unique_analysis=next.unique_analysis; 
      usedef_defined;
      call_chain = CallChain.join prev.call_chain next.call_chain;
      unknown_decorator=prev.unknown_decorator || next.unknown_decorator;
      (*usedef_tables=usedef_tables;*)
    }
  


  let get_implementation ~join ~less_or_equal { signatures; unknown_decorator; _ } arg_types callable =
    (* let arg_callable = 
      Type.Callable.map_parameters callable ~f:(fun parameter ->
        match parameter with
        | Defined parameters ->
          let new_parameters =
            List.map parameters ~f:(fun parameter ->
              match parameter with
              | Named named ->
                (match ArgTypes.get_type arg_types named.name with
                | Type.Unknown -> 
                  (match named.annotation with
                  | Type.Top | Any -> Type.Callable.RecordParameter.Named { named with annotation=Type.Unknown }
                  | _ -> parameter
                  )
                | t -> 
                  (match named.annotation with
                  | Type.Top | Any -> Named { named with annotation=t }
                  | anno -> Named { named with annotation=type_join t anno }
                  )
                  
                )
              | KeywordOnly named ->
                (match ArgTypes.get_type arg_types named.name with
                | Type.Unknown ->
                  (match named.annotation with
                  | Type.Top | Any -> KeywordOnly { named with annotation=Unknown }
                  | _ -> parameter
                  )
                | t ->
                  (match named.annotation with
                  | Type.Top | Any -> KeywordOnly { named with annotation=t }
                  | anno -> KeywordOnly { named with annotation=type_join t anno }
                  )
                )
              | _ -> parameter  
            )
          in
          Defined new_parameters
        | _ -> parameter
      )
    in *)
    let _ = arg_types, join in
    let arg_types = 
      if unknown_decorator
      then
        ArgTypes.empty
      else
        ArgTypes.map ~f:(Type.narrow_union ~join ~less_or_equal) arg_types 
    in
    let return_type = Signatures.get_return_type ~type_join:join signatures arg_types in
    
    let arg_callable = Type.Callable.map_parameters callable ~f:(fun x -> x) in 

    let ret_callable =
      match return_type with
      | Type.Unknown | Type.Bottom -> 
        (match arg_callable.implementation.annotation with
        | Type.Top | Any -> Type.Callable.with_return_annotation arg_callable ~annotation:Type.Unknown
        | _ -> arg_callable
        )
      | _ ->
        Type.Callable.with_return_annotation arg_callable ~annotation:return_type
    in

    { callable with implementation=ret_callable.implementation }

  let get_analysis_arg_types { signatures; _ } =
    Signatures.get_analysis_arg_types signatures

  let get_all_arg_types ~type_join { signatures; _ } =
    Signatures.get_all_arg_types ~type_join signatures

  let get_module_var_type { signatures; _ } attribute =
    Signatures.get_module_var_type signatures attribute

  let analysis_caller_set { signatures; callers; _ } = 
    let _ = callers in
    let _, caller_set = Signatures.analysis_caller_set signatures in
    caller_set
    (* if all_flag then callers else caller_set *)
  (* let analysis_caller_set prev next = 
    if Signatures.is_changed_return_info prev.signatures next.signatures
    then next.callers
    else ReferenceSet.empty *)

  let change_analysis ({ signatures; _ } as t) =
    { t with signatures=Signatures.change_analysis signatures; }

  let change_analysis_of_arg_types ({ signatures; _ } as t) arg_types_opt_set = 
    if ArgTypesOptSet.mem arg_types_opt_set None
    then (
      change_analysis t
    )
    else { t with signatures=Signatures.change_analysis_of_arg_types signatures arg_types_opt_set; }

  let change_analysis_to_false ({ signatures; _ } as t) =
    { t with signatures=Signatures.change_analysis_to_false signatures; }

  let end_analysis ({ signatures; _ } as t) arg_types =
    { t with signatures=Signatures.end_analysis signatures arg_types; }

  let get_analysis_set ({signatures; unknown_decorator; _ } as t) =
    if unknown_decorator
    then 
      ArgTypesOptSet.empty, ReferenceMap.empty
    else
      let should_analysis_set = 
        Signatures.get_should_analysis signatures
      in

      (* TODO: skip return_var_type? *)
      (* let analysis_set = 
        if not ((Type.equal prev.return_type next.return_type) && (ReferenceMap.equal Type.equal prev.return_var_type next.return_var_type))
        then next.callers
        else ReferenceSet.empty
      in *)

      let analysis_set = analysis_caller_set t in
      
      should_analysis_set, analysis_set

  let has_analysis { signatures; unknown_decorator; _ } =
    if unknown_decorator then false
    else
      Signatures.has_analysis signatures

  let get_usage_self_attributes { usage_attributes; _ } =
    AttributeAnalysis.AttributeStorage.get_single_class_param usage_attributes
    |> AttributeAnalysis.AttributeStorage.get_all_attributes
    |> Identifier.Set.fold ~init:ReferenceSet.empty ~f:(fun acc ref -> ReferenceSet.add acc (Reference.create ref))
    
end

module type FunctionTable = sig
  type t = FunctionSummary.t FunctionHash.t
end

module FunctionTable = struct
  type t = FunctionSummary.t FunctionHash.t [@@deriving sexp, equal]

  let empty = FunctionHash.create

  let find_signature t reference arg_types =
    let func_summary = FunctionHash.find t reference |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.find_signature func_summary arg_types

  let add_param_varset t reference param_varset =
    let func_summary = FunctionHash.find t reference |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:reference ~data:(FunctionSummary.add_param_varset func_summary param_varset) t

  let get_param_varset t reference =
    let func_summary = FunctionHash.find t reference |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_param_varset func_summary

  let add_new_signature ~join ?caller_name t reference arg_typ_list =
    let func_summary = FunctionHash.find t reference |> Option.value ~default:FunctionSummary.empty in
    let func_summary = FunctionSummary.add_new_signature ~join ?caller_name func_summary arg_typ_list in
    FunctionHash.set ~key:reference ~data:func_summary t
  (* let add_arg_types ~join t reference arg_typ_list =
    let func_summary = FunctionMap.find t reference |> Option.value ~default:FunctionSummary.empty in
    let func_summary = FunctionSummary.add_arg_types ~join func_summary arg_typ_list in
    FunctionMap.set ~key:reference ~data:func_summary t *)



  let add_usage_attributes t func storage =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:func ~data:(FunctionSummary.add_usage_attributes func_summary storage) t

  let add_caller t func caller =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:func ~data:(FunctionSummary.add_caller func_summary caller) t

  let add_return_annotation t func return_type =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
      FunctionHash.set ~key:func ~data:(FunctionSummary.add_return_annotation func_summary return_type) t

  let add_return_type ~type_join t func arg_types return_type =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
      FunctionHash.set ~key:func ~data:(FunctionSummary.add_return_type ~type_join func_summary arg_types return_type) t

(*   let set_arg_types t func arg_types =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:func ~data:(FunctionSummary.set_arg_types func_summary arg_types) t

  let set_arg_annotation t func arg_annotation =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:func ~data:(FunctionSummary.set_arg_annotation func_summary arg_annotation) t *)
  
  let set_return_var_type t func arg_types return_var_type =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:func ~data:(FunctionSummary.set_return_var_type func_summary arg_types return_var_type) t

  let set_return_type t func arg_types return_type =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:func ~data:(FunctionSummary.set_return_type func_summary arg_types return_type) t

  let set_preprocess t func expression typ =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:func ~data:(FunctionSummary.set_preprocess func_summary expression typ) t

  let set_callers t func callers =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:func ~data:(FunctionSummary.set_callers func_summary callers) t
  
  let set_usage_attributes t func usage_attributes =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:func ~data:(FunctionSummary.set_usage_attributes func_summary usage_attributes) t

  let set_unique_analysis t func unique_analysis =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:func ~data:(FunctionSummary.set_unique_analysis func_summary unique_analysis) t

  let set_usedef_defined t func usedef_defined =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:func ~data:(FunctionSummary.set_usedef_defined func_summary usedef_defined) t

  let set_call_chain t func call_chain =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:func ~data:(FunctionSummary.set_call_chain func_summary call_chain) t
  
  let set_unknown_decorator t func =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:func ~data:(FunctionSummary.set_unknown_decorator func_summary) t


(*   let set_return_var_type t func return_var_type =
    let func_summary = FunctionMap.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionMap.set ~key:func ~data:(FunctionSummary.set_return_var_type func_summary return_var_type) t

  let set_return_type t func return_type =
    let func_summary = FunctionMap.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionMap.set ~key:func ~data:(FunctionSummary.set_return_type func_summary return_type) t *)

    (*
  let set_usedef_tables t func usedef_tables =
    let func_summary = FunctionMap.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionMap.set ~key:func ~data:(FunctionSummary.set_usedef_tables func_summary usedef_tables) t

  let get_usedef_tables t func_name =
    let func_summary = FunctionMap.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_usedef_tables func_summary
    *)

(*   let get_arg_types t func_name =
    let func_summary = FunctionMap.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_arg_types func_summary

  let get_arg_annotation t func_name =
    let func_summary = FunctionMap.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_arg_annotation func_summary *)

  let get_return_var_type t func_name arg_types =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_return_var_type func_summary arg_types

  let get_return_type ~type_join ~less_or_equal ?property t func_name arg_types =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    let annotation = FunctionSummary.get_return_annotation func_summary in
    let real_type = FunctionSummary.get_return_type ~type_join ?property func_summary arg_types in

    (* if String.is_substring (Reference.show func_name) ~substring:"MultiIndex.format" then (
      Log.dump "%a => %a" Reference.pp func_name Type.pp real_type;
      Log.dump "OK %a" FunctionSummary.pp func_summary;
    ); *)

    let return_type =
      match annotation with
      | t when not !on_dataflow -> t
      | Type.Unknown -> real_type
      | t when not (Type.is_unknown real_type) -> 
        let filtered_annotation = Type.filter_unknown t in
        let filtered_real_type = Type.filter_unknown real_type in
        if less_or_equal ~left:filtered_real_type ~right:filtered_annotation
        then real_type
        else filtered_annotation
      | t -> t
    in

    (* Log.dump "??? %a => %a (%a) => %a" Reference.pp func_name Type.pp real_type Type.pp annotation Type.pp return_type; *)

    (* let old_type = return_type in *)

    let return_type =
      if !on_any 
      then return_type
      else (if Type.can_unknown return_type then Type.Any else return_type)
    in

    (* if String.is_substring (Reference.show func_name) ~substring:"MultiIndex.format" then (
      Log.dump "%a => %a (%a) (%a)" Reference.pp func_name Type.pp return_type Type.pp old_type Type.pp real_type;
      (* Log.dump "OK %a" FunctionSummary.pp func_summary; *)
    ); *)

    return_type

  let get_callers t func_name =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_callers func_summary

  let get_usage_attributes t func_name =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_usage_attributes func_summary

  let get_preprocess t func_name =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_preprocess func_summary

  let get_unique_analysis t func_name =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_unique_analysis func_summary

  let get_usedef_defined t func_name =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_usedef_defined func_summary

  let get_unknown_decorator t func_name =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_unknown_decorator func_summary

  let update ~type_join prev next =
    FunctionHash.join prev next ~equal:FunctionSummary.equal ~data_join:(FunctionSummary.update ~type_join)



  let join ~type_join left right =
    FunctionHash.join left right ~equal:FunctionSummary.equal ~data_join:(FunctionSummary.join ~type_join)

(*   let join_return_type ~type_join t func return_type =
    let func_summary = FunctionHash.find t func |> Option.value ~default:FunctionSummary.empty in
    FunctionMap.set ~key:func ~data:(FunctionSummary.join_return_type ~type_join func_summary return_type) t
 *)
  let pp format table =
    FunctionHash.iteri ~f:(fun ~key ~data ->
      Format.fprintf format "[[[ Function Info ]]] \n%a \n%a \n" Reference.pp key FunctionSummary.pp data
    ) table

  let get_callable ~join ~less_or_equal ~successors t arg_types (callable: Type.Callable.t) =
    match callable.kind with
    | Named name ->
      (* let class_name = Reference.drop_last name in 
      let func_name = Reference.last name in
      let successors = 
        successors (Reference.show class_name) 
        |> List.map ~f:(fun s -> Reference.create ~prefix:(Reference.create s) func_name ) 
      in *)
      let _ = successors in

      let func_summary = 
        List.find [name] ~f:(fun name -> FunctionHash.find t name |> Option.is_some)
        >>| FunctionHash.find_exn t
        |> Option.value ~default:FunctionSummary.empty
      in

      let callable = FunctionSummary.get_implementation ~join ~less_or_equal func_summary arg_types callable in
      callable
    | _ -> callable

  let get_callable_return_type ~type_join ~successors t arg_types (callable: Type.Callable.t) =
    match callable.kind with
    | Named name ->
      (* let class_name = Reference.drop_last name in 
      let func_name = Reference.last name in
      let successors = 
        successors (Reference.show class_name) 
        |> List.map ~f:(fun s -> Reference.create ~prefix:(Reference.create s) func_name ) 
      in *)
      let _ = successors in

      let func_summary = 
        List.find [name] ~f:(fun name -> FunctionHash.find t name |> Option.is_some)
        >>| FunctionHash.find_exn t
        |> Option.value ~default:FunctionSummary.empty
      in

      (* let func_summary = FunctionHash.find t name |> Option.value ~default:FunctionSummary.empty in *)
      let x = FunctionSummary.get_return_type ~type_join func_summary arg_types in

      (* if String.is_substring (Reference.show name) ~substring:"solveset" then
        Log.dump "%a ==> %a" Reference.pp name Type.pp x; *)

      x
    | _ -> Type.Unknown

  let get_functions t prefix =
    List.filter (FunctionHash.keys t) ~f:(fun key ->
      Reference.is_prefix key ~prefix  
    )
    |>
    List.fold ~init:ReferenceSet.empty ~f:(fun ref_set key ->
      ReferenceSet.add ref_set key
    )

  let get_usage_self_attributes t func_name =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_usage_self_attributes func_summary


  let get_all_functions t =
    List.fold (FunctionHash.keys t) ~init:ReferenceSet.empty ~f:(fun ref_set key ->
      ReferenceSet.add ref_set key
    )

  let get_analysis_arg_types t func_name =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_analysis_arg_types func_summary

  let get_all_arg_types ~type_join t func_name =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_all_arg_types ~type_join func_summary

  let get_module_var_type t func_name attribute =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionSummary.get_module_var_type func_summary attribute

  let change_analysis_of_argtypes t callers =
    ReferenceMap.iteri callers ~f:(fun ~key ~data -> 
      match FunctionHash.find t key with
      | Some func_summary (* when not (Reference.is_initialize key) *) -> 
        (* Log.dump "%a ..." Reference.pp key; *)
        (* Log.dump "%a ..." Reference.pp key;
        ArgTypesOptSet.iter data ~f:(fun arg_types -> 
          match arg_types with
          | None -> Log.dump "NONE";
          | _ -> Log.dump "Somethingh";  
        ); *)
        let func_summary = FunctionSummary.change_analysis_of_arg_types func_summary data in
        FunctionHash.set ~key ~data:func_summary t
      | _ -> ()
    )
  
  let end_analysis t func_name arg_types =
    let func_summary = FunctionHash.find t func_name |> Option.value ~default:FunctionSummary.empty in
    FunctionHash.set ~key:func_name ~data:(FunctionSummary.end_analysis func_summary arg_types) t


  let change_analysis_of_func t func_name =
    match FunctionHash.find t func_name with
    | Some v when not (Reference.is_initialize func_name) -> 
      (* Log.dump "%a ..." Reference.pp func_name; *)
      FunctionHash.set ~key:func_name ~data:(FunctionSummary.change_analysis v) t
    | _ -> ()

  let change_analysis_to_false_of_func t func_name =
    match FunctionHash.find t func_name with
    | Some v -> FunctionHash.set ~key:func_name ~data:(FunctionSummary.change_analysis_to_false v) t
    | _ -> ()

  let get_analysis_set t =
    FunctionHash.fold t ~init:(ReferenceMap.empty, ReferenceMap.empty) ~f:(fun ~key ~data (self, callers) ->
      let should_analysis_set, analysis_set = FunctionSummary.get_analysis_set data in
      let new_analysis_set = analysis_set |> ReferenceMap.join ~data_join:ArgTypesOptSet.union ~equal:ArgTypesOptSet.equal callers in
      (if ArgTypesOptSet.is_empty should_analysis_set
      then self, new_analysis_set
      else 
        let self_data = ReferenceMap.find self key |> Option.value ~default:ArgTypesOptSet.empty in
        ReferenceMap.set self ~key ~data:(ArgTypesOptSet.union self_data should_analysis_set), new_analysis_set
      )
    )

  let has_analysis t =
    FunctionHash.fold t ~init:false ~f:(fun ~key:_ ~data acc ->
      acc || FunctionSummary.has_analysis data
    )

end

module type OurSummary = sig
  type t = {
    class_table : ClassTable.t;
    function_table : FunctionTable.t;
    stub_info : StubInfo.t;
    recheck_info: (Type.t Reference.Map.t) Reference.Map.t;
    errors: Ppx_sexp_conv_lib.Sexp.t;
    (* errors: OurErrorDomain.OurErrorList.t; *)
  }
end

module OurSummary = struct
  type t = {
    class_table : ClassTable.t;
    function_table : FunctionTable.t;
    stub_info : StubInfo.t;
    recheck_info: (Type.t Reference.Map.t) Reference.Map.t;
    errors: Ppx_sexp_conv_lib.Sexp.t;
  }
  [@@deriving equal, sexp]

  let empty ?(size=5) () = {
    class_table=ClassTable.empty ~size ();
    function_table=FunctionTable.empty ~size ();
    stub_info=StubInfo.empty;
    recheck_info=Reference.Map.empty;
    errors = Ppx_sexp_conv_lib.Sexp.Atom "";
  }

  let set_errors t errors = { t with errors}

  let get_errors { errors; _ } = errors

  let set_recheck_info t recheck_info =
    { t with recheck_info }

  let get_recheck_info { recheck_info; _ } = recheck_info

  let set_skip_reference_map ~define_name { recheck_info; _ } =
    skip_reference_map := Reference.Map.find recheck_info define_name |> Option.value ~default:Reference.Map.empty

  let update_default_value ~prev next =
    ClassTable.update_default_value prev.class_table next.class_table


  let update_check_preprocess ~define ~type_join ~prev next =
    if (Reference.is_initialize define)
    then ( 
      ClassTable.join ~type_join prev.class_table next.class_table;
      ClassTable.set_all_class_var_type_to_empty next.class_table;
    ) else (
      ClassTable.join_only_attribute prev.class_table next.class_table;
      ClassTable.set_all_class_var_type_to_empty next.class_table;
    );
    (*  let class_time = Timer.stop_in_sec timer in *)
    FunctionTable.update ~type_join prev.function_table next.function_table

  let update ~type_join ~prev next = 
    (* let timer = Timer.start () in *)
    ClassTable.join ~type_join prev.class_table next.class_table;
   (*  let class_time = Timer.stop_in_sec timer in *)
    FunctionTable.update ~type_join prev.function_table next.function_table
    (* let function_time = Timer.stop_in_sec timer -. class_time in *)

    (* if Float.(>) (function_time +. class_time) 0.1 then
      Log.dump "Class %.3f Function %.3f" class_time function_time; *)

  let join ~type_join left right = 
    ClassTable.join ~type_join left.class_table right.class_table;
    FunctionTable.join ~type_join left.function_table right.function_table
    (*Log.dump "Class %f \nFunction %f" class_time function_time;*)


(*   let join_return_type ~type_join ({function_table; _} as t) func_name return_type =
    { t with function_table = FunctionTable.join_return_type ~type_join function_table func_name return_type }
 *)

 let filter_seen_var ~class_name ~func_name ~var_set { class_table; _ } =
  ClassTable.filter_seen_var ~class_name ~func_name ~var_set class_table

 let find_signature {function_table; _ } reference arg_types =
  FunctionTable.find_signature function_table reference arg_types

 let add_param_varset { function_table; _ } reference param_varset =
  FunctionTable.add_param_varset function_table reference param_varset

 let get_param_varset { function_table; _ } reference =
  FunctionTable.get_param_varset function_table reference

 let add_new_signature ~join ?caller_name { function_table; _} reference arg_typ_list =
  FunctionTable.add_new_signature ~join ?caller_name function_table reference arg_typ_list

(*   let add_arg_types ~join ({ function_table; _} as t) reference arg_typ_list =
    { t with function_table = FunctionTable.add_arg_types ~join function_table reference arg_typ_list }
 *)


  let add_usage_attributes ?class_name ?class_var {class_table; function_table; _ } func_name storage =
    let storage =
      match class_name, class_var with
      | Some class_name, Some class_var ->
        let filtered_storage = AttributeStorage.filter_by_prefix storage ~prefix:(Reference.create class_var) in
        ClassTable.add_usage_attributes class_table class_name filtered_storage;
              
        storage
        (* let filter_class_var_storage = AttributeStorage.filter_class_var storage ~prefix:(Reference.create class_var) in
        filter_class_var_storage *)
      | _ -> storage
    in
    (*let class_summary =  in*)
    FunctionTable.add_usage_attributes function_table func_name storage

  let add_caller { function_table; _} ~caller callee =
    FunctionTable.add_caller function_table callee caller

  let add_return_annotation {function_table; _ } func_name return_type =
    FunctionTable.add_return_annotation function_table func_name return_type

  let add_return_type ~type_join {function_table; _ } func_name arg_types return_type =
    FunctionTable.add_return_type ~type_join function_table func_name arg_types return_type
(*   let set_arg_types ({function_table; _} as t) func_name arg_types =
    { t with function_table=FunctionTable.set_arg_types function_table func_name arg_types }

  let set_arg_annotation ({function_table; _} as t) func_name arg_annotation =
    { t with function_table=FunctionTable.set_arg_annotation function_table func_name arg_annotation } *)
  let set_return_var_type {function_table; _} func_name arg_types return_var_type =
    FunctionTable.set_return_var_type function_table func_name arg_types return_var_type

  let set_return_type {function_table; _} func_name arg_types return_type =
    FunctionTable.set_return_type function_table func_name arg_types return_type

  let set_preprocess {function_table; _} func_name expression typ =
    FunctionTable.set_preprocess function_table func_name expression typ

  let set_callers {function_table; _} func_name callers =
    FunctionTable.set_callers function_table func_name callers 
  let set_usage_attributes {function_table; _} func_name usage_attributes =
    FunctionTable.set_usage_attributes function_table func_name usage_attributes

  let set_unique_analysis { function_table; _ } func_name unique_analysis =
    FunctionTable.set_unique_analysis function_table func_name unique_analysis

  let set_usedef_defined { function_table; _ } func_name usedef_defined =
    FunctionTable.set_usedef_defined function_table func_name usedef_defined

  let set_call_chain { function_table; _ } func_name call_chain =
    FunctionTable.set_call_chain function_table func_name call_chain

  let set_unknown_decorator { function_table; _ } func_name =
    FunctionTable.set_unknown_decorator function_table func_name

  let get_class_vars { class_table; _ } =
    ClassTable.get_class_vars class_table
  let get_class_table { class_table; _ } = class_table

  let get_function_table { function_table; _ } = function_table
(*
  let get_usedef_tables {function_table; _} func_name = 
    FunctionTable.get_usedef_tables function_table func_name
    *)
  
(*   let get_arg_types {function_table; _} func_name =
    FunctionTable.get_arg_types function_table func_name

  let get_arg_annotation {function_table; _} func_name =
    FunctionTable.get_arg_annotation function_table func_name *)
  let get_return_var_type {function_table; _} func_name arg_types =
    FunctionTable.get_return_var_type function_table func_name arg_types

  let get_return_type ~type_join ~less_or_equal {function_table; _} func_name arg_types  =
    FunctionTable.get_return_type ~type_join ~less_or_equal function_table func_name arg_types

  let get_callers {function_table; _} func_name =
    FunctionTable.get_callers function_table func_name

  let get_usage_attributes_from_func { function_table; _ } func_name =
    FunctionTable.get_usage_attributes function_table func_name

  let get_preprocess { function_table; _ } func_name =
    FunctionTable.get_preprocess function_table func_name

  let get_callable ~join ~less_or_equal ~successors { function_table; _ } arg_types callable =
    FunctionTable.get_callable ~join ~less_or_equal ~successors function_table arg_types callable

  let get_callable_return_type ~type_join ~successors { function_table; _ } arg_types callable =
    FunctionTable.get_callable_return_type ~type_join ~successors function_table arg_types callable

  let get_unique_analysis { function_table; _ } func_name =
    FunctionTable.get_unique_analysis function_table func_name

  let get_usedef_defined { function_table; _ } func_name =
    FunctionTable.get_usedef_defined function_table func_name

  let get_unknown_decorator { function_table; _ } func_name =
    FunctionTable.get_unknown_decorator function_table func_name

  let add_class_attribute {class_table; _} parent attr =
    ClassTable.add_attribute class_table parent attr 

  let add_class_property {class_table; _} parent property =
    ClassTable.add_property class_table parent property 

  let add_class_method {class_table; _} parent call_info meth =
    ClassTable.add_method ~call_info class_table parent meth

  let set_class_summary { class_table; _ } class_name class_info =
    ClassTable.set_class_info class_table class_name class_info 

  let set_stub_info t stub_info =
    { t with stub_info }

  let update_unseen_temp_class_var_type ~type_join ~updated_vars { class_table; _ } =
    ClassTable.update_unseen_temp_class_var_type ~type_join ~updated_vars class_table

  let update_unseen_temp_class_var_type_to_var { class_table; _ } =
    ClassTable.update_unseen_temp_class_var_type_to_var class_table
  let update_unseen_temp_class_var_type_to_unknown { class_table; _ } =
    ClassTable.update_unseen_temp_class_var_type_to_unknown class_table
  let set_all_class_var_type_to_empty { class_table; _ } =
    ClassTable.set_all_class_var_type_to_empty class_table

  let set_all_temp_class_var_type_from_join { class_table; _ } =
    ClassTable.set_all_temp_class_var_type_from_join class_table
  let set_all_join_temp_class_var_type_to_empty { class_table; _ } =
    ClassTable.set_all_join_temp_class_var_type_to_empty class_table

  let set_class_table t class_table =
    { t with class_table; }

  let get_class_summary { class_table; _ } class_name =
    ClassTable.get_class_info class_table class_name

  let get_usage_attributes_from_class { class_table; _ } class_name = 
    ClassTable.get_usage_attributes class_table class_name

  let get_class_property {class_table; _} parent =
    ClassTable.get_class_property class_table parent 

  let check_attr ~attr { class_table; _ } class_name =
    ClassTable.check_attr ~attr class_table class_name

  let pp_class format {class_table; _} =
    Format.fprintf format "%a" ClassTable.pp class_table
  let pp_func format {function_table; _} = 
    Format.fprintf format "%a" FunctionTable.pp function_table

  let pp formatter t =
    (* let _ = pp_class in
    Format.fprintf formatter "%a" pp_func t *)
    Format.fprintf formatter "%a\n\n%a" pp_class t pp_func t

  let get_analysis_arg_types { function_table; _ } func_name =
    FunctionTable.get_analysis_arg_types function_table func_name

  let get_all_arg_types ~type_join { function_table; _ } func_name =
    FunctionTable.get_all_arg_types ~type_join function_table func_name

  let get_module_var_type { function_table; _ } func_prefix attribute =
    let func_name = Reference.combine func_prefix (Reference.create "$toplevel") in
    FunctionTable.get_module_var_type function_table func_name attribute

  let get_analysis_set { class_table; function_table; _ } =
    let get_functions =
      FunctionTable.get_functions function_table
    in

    let get_usage_self_attributes =
      FunctionTable.get_usage_self_attributes function_table
    in

    let class_functions = ClassTable.get_analysis_set ~get_functions ~get_usage_self_attributes class_table in
    let self, callers = FunctionTable.get_analysis_set function_table in 
    let join = ReferenceMap.join ~data_join:ArgTypesOptSet.union ~equal:ArgTypesOptSet.equal in
    let total_analysis_set = join class_functions self |> join callers in

    FunctionTable.change_analysis_of_argtypes function_table total_analysis_set;

    total_analysis_set

  let get_functions_of_class { class_table; function_table; _ } = 
    let get_functions =
      FunctionTable.get_functions function_table
    in

    ClassTable.get_functions_of_class ~get_functions class_table

  let change_analysis { function_table; _ } =
    let _, callers = FunctionTable.get_analysis_set function_table in 
    FunctionTable.change_analysis_of_argtypes function_table callers

  let end_analysis { function_table; _ } func_name arg_types =
    FunctionTable.end_analysis function_table func_name arg_types

  let change_analysis_of_func { function_table; _ } func_name =
    FunctionTable.change_analysis_of_func function_table func_name

  let change_analysis_to_false_of_func { function_table; _ } func_name =
    FunctionTable.change_analysis_to_false_of_func function_table func_name

  let get_skip_set ({function_table; _ } as t) =
    let analysis_set = get_analysis_set t in
    let get_all_functions= FunctionTable.get_all_functions function_table in
    ReferenceSet.diff get_all_functions (ReferenceMap.to_set analysis_set)


  let has_analysis { class_table; function_table; _ } =
    ClassTable.has_analysis class_table && FunctionTable.has_analysis function_table

  let add_implicit_to_join { class_table; _ } =
    ClassTable.add_implicit_to_join class_table

end

let global_summary = "Pyinder.finalSummary"




let is_func_model_exist () = check_dir !data_path

let set_data_path (configuration: Configuration.Analysis.t) =
  if String.equal !data_path "" then
    data_path :=
      (List.nth_exn configuration.source_paths 0 
      |> SearchPath.get_root
      |> PyrePath.show) ^ "/pyinder_analysis"



let our_model = ref (OurSummary.empty ());;

let our_summary = ref (OurSummary.empty ());;

let stub_info = ref StubInfo.empty;;

let cache = ref false;;

let is_search_mode = String.equal "search"

let is_inference_mode = String.equal "inference"

let is_last_inference_mode = String.equal "last_inference"

let is_error_mode = String.equal "error"

let is_recheck_mode = String.equal "recheck"

let is_check_preprocess_mode = String.equal "check_preprocess"

let is_preprocess = ref false;;



let save_summary (summary: OurSummary.t) func_name =
  check_and_make_dir !data_path;
  let target_path = !data_path ^ "/" ^ (Reference.show func_name) ^ ".marshalled" in
  let data_out = open_out target_path in
  let sexp = OurSummary.sexp_of_t summary in
  Marshal.to_channel data_out sexp [];
  close_out data_out

let save_global_summary () = save_summary !our_model (Reference.create global_summary)

let load_summary func_name =
  let filename = !data_path ^ "/" ^ (Reference.show func_name) ^ ".marshalled" in
  let x =
  match Sys.file_exists filename with
  | `Yes ->
      let data_in = open_in filename in
      let our_summary = OurSummary.t_of_sexp (Marshal.from_channel data_in) in
      close_in data_in;
      our_summary
  | _ ->
    OurSummary.empty ()
  in
  x

let load_global_summary () = load_summary (Reference.create global_summary)

let load_all_summary_test () =
  (
    cache := true;
    let list_files = Sys.readdir !data_path |> Array.to_list in 
    let _ = List.iter list_files ~f:(fun file -> 
      if String.equal file "mode.marshalled" then ()
      else
      (
        Log.dump "%s Load..." file;
        let data_in = open_in (!data_path ^ "/" ^ file) in
        let t = OurSummary.t_of_sexp (Marshal.from_channel data_in) in
        close_in data_in;
        Log.dump "%a" OurSummary.pp t;
        ()
      )
    )
    in
    ()
  )

let global_cache = ref false

let rec load_global_summary_cache () =
  Thread.delay((Random.float 1.0) /. 1000.0);
  if !global_cache then (
    ()
  )
  else
  (
    
    (*
    global_cache := true;
    
    let data_out = open_out filename in
    Marshal.to_channel data_out "" [];
    close_out data_out;
    
    our_model := load_global_summary ();
    *)
      
    let filename = !data_path ^ "/" ^ "lock" in
    match Sys.file_exists filename with
    | `Yes ->

      Thread.delay((Random.float 1.0) /. 1000.0);
      load_global_summary_cache ()
    | _ ->
      global_cache := true;
      let data_out = open_out filename in
      Marshal.to_channel data_out "" [];
      close_out data_out;
      our_model := load_global_summary ();
      Sys.remove filename;
      
  )

(* let load_all_summary ?(use_cache=true) ~type_join ~skip_set prev_model =
  if use_cache && !cache then
    ()
  else
  (
    cache := true;
    let list_files = Sys.readdir !data_path |> Array.to_list in 
    our_model := List.fold list_files ~init:prev_model ~f:(fun summary file -> 
      if (String.equal file "mode.marshalled") || 
        (Reference.Set.exists skip_set ~f:(fun ref -> String.is_prefix file ~prefix:(Reference.show ref)))
      then (
        summary
      )
      else
      (
        let data_in = open_in (!data_path ^ "/" ^ file) in
        let other_summary = OurSummary.t_of_sexp (Marshal.from_channel data_in) in
        close_in data_in;
        OurSummary.join ~type_join summary other_summary
      )
    )
  ) *)

let load_specific_file () =
  let list_files = [
    "airflow.dag.serialization.serialization.Serialization._serialize.marshalled";
  ]
  in
  List.iter list_files ~f:(fun file ->
    let data_in = open_in (!data_path ^ "/" ^ file) in
    let other_summary = OurSummary.t_of_sexp (Marshal.from_channel data_in) in
    Log.dump "START %a" OurSummary.pp other_summary;
    close_in data_in;
  )

let select_our_model func_name =
  if is_inference_mode (load_mode ()) then
    load_summary func_name
  else 
    !our_model

let is_first = ref true



(* module OurDomainReadOnly = struct
  module FuncSummary = struct
    module ArgTypesMap = Map.Make (ArgTypes)

    type t = {
      signatures: Type.t ArgTypesMap.t;
      preprocess: Type.t ExpressionMap.t;
      usedef_defined: VarTypeSet.t;
      unknown_decorator : bool;
    }
  end

  module ClsSummary = struct
    type t = {
      class_var_type: Type.t ReferenceMap.t;
      temp_class_var_type : Type.t ReferenceMap.t;
      properties : AttrsSet.t;
    }
  end

  type t = {
    func_summary : FuncSummary.t Reference.Map.t;
    class_summary : ClsSummary.t Reference.Map.t;
  }

  let create (model: OurSummary.t) =
    let func_summary = 
      FunctionHash.fold model.function_table ~init:Reference.Map.empty ~f:(fun ~key:reference ~data:func_summary acc ->
        let signatures = FunctionSummary.get_signatures func_summary in
        let preprocess = FunctionSummary.get_preprocess func_summary in
        let usedef_defined = FunctionSummary.get_usedef_defined func_summary in
        let unknown_decorator = FunctionSummary.get_unknown_decorator func_summary in
        Reference.Map.set acc ~key:reference ~data:{ FuncSummary.signatures; preprocess; usedef_defined; unknown_decorator }
      )
    in
    let class_summary = 
      ClassHash.fold model.class_table ~init:Reference.Map.empty ~f:(fun ~key:reference ~data:class_summary acc ->
        let class_var_type = ClassSummary.get_class_var_type class_summary in
        let temp_class_var_type = ClassSummary.get_temp_class_var_type class_summary in
        let properties = ClassSummary.get_properties class_summary in
        Reference.Map.set acc ~key:reference ~data:{ ClsSummary.class_var_type; temp_class_var_type; properties }
      )
    in
    { func_summary; class_summary } 
end *)

let all_defines = ref []