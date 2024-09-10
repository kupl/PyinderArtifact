(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

type t = {
  configuration: Configuration.Analysis.t;
  populate_call_graph: bool;
  our_summary: OurDomain.OurSummary.t;
  our_errors: OurErrorDomainReadOnly.OurErrorListReadOnly.t;
}

let create ?(populate_call_graph = false) ?(our_summary = OurDomain.OurSummary.empty ()) ?(our_errors = OurErrorDomainReadOnly.OurErrorListReadOnly.empty) configuration = 
  { configuration; populate_call_graph; our_summary; our_errors; }

let create_for_overlay parent = { parent with populate_call_graph = false }

let configuration { configuration; _ } = configuration

let populate_call_graph { populate_call_graph; _ } = populate_call_graph

let our_summary { our_summary; _} = our_summary

let our_errors { our_errors; _ } = our_errors

let set_our_summary t our_summary = { t with our_summary; }

let track_dependencies { configuration = { Configuration.Analysis.incremental_style; _ }; _ } =
  match incremental_style with
  | Configuration.Analysis.Shallow -> false
  | Configuration.Analysis.FineGrained -> true


let debug { configuration = { Configuration.Analysis.debug; _ }; _ } = debug

module PythonVersionInfo = struct
  type t = {
    major_version: int;
    minor_version: int;
    micro_version: int;
  }
end

let python_version_info
    {
      configuration =
        {
          Configuration.Analysis.python_major_version = major_version;
          python_minor_version = minor_version;
          python_micro_version = micro_version;
          _;
        };
      _;
    }
  =
  { PythonVersionInfo.major_version; minor_version; micro_version }


module TypeCheckControls = struct
  type t = {
    constraint_solving_style: Configuration.Analysis.constraint_solving_style;
    include_type_errors: bool;
    include_local_annotations: bool;
    debug: bool;
  }
end

let type_check_controls
    {
      configuration =
        {
          Configuration.Analysis.debug;
          store_type_errors;
          store_type_check_resolution;
          constraint_solving_style;
          _;
        };
      _;
    }
  =
  TypeCheckControls.
    {
      debug;
      constraint_solving_style;
      include_type_errors = store_type_errors;
      include_local_annotations = store_type_check_resolution;
    }
