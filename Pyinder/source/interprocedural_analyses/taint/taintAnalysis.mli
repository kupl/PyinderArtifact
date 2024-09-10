(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

val initialize_configuration : static_analysis_configuration:Configuration.StaticAnalysis.t -> unit

val parse_and_save_decorators_to_skip : inline_decorators:bool -> Configuration.Analysis.t -> unit

val run_taint_analysis
  :  static_analysis_configuration:Configuration.StaticAnalysis.t ->
  build_system:Server.BuildSystem.t ->
  scheduler:Scheduler.t ->
  unit ->
  unit
