open Core
open Ast
open Statement

module Error = AnalysisError

module LocalErrorMap = struct
  type t = Error.t list Int.Table.t

  let empty () = Int.Table.create ()

  let set ~statement_key ~errors error_map = Int.Table.set error_map ~key:statement_key ~data:errors

  let append ~statement_key ~error error_map =
    Int.Table.add_multi error_map ~key:statement_key ~data:error


  let all_errors error_map = Int.Table.data error_map |> List.concat
end

module type Context = sig
  val qualifier : Reference.t

  val debug : bool

  val constraint_solving_style : Configuration.Analysis.constraint_solving_style

  val define : Define.t Node.t

  (* Where to store local annotations during the fixpoint. `None` discards them. *)
  val resolution_fixpoint : LocalAnnotationMap.t option

  (* Where to store errors found during the fixpoint. `None` discards them. *)
  val error_map : LocalErrorMap.t option

  module Builder : Callgraph.Builder
end

module type OurContext = sig
  val qualifier : Reference.t

  val debug : bool

  val constraint_solving_style : Configuration.Analysis.constraint_solving_style

  val define : Define.t Node.t

  (* Where to store local annotations during the fixpoint. `None` discards them. *)
  val resolution_fixpoint : LocalAnnotationMap.t option

  (* Where to store errors found during the fixpoint. `None` discards them. *)
  val error_map : LocalErrorMap.t option

  val our_summary : OurDomain.OurSummary.t ref

  val entry_arg_types : OurDomain.ArgTypes.t ref

  val ignore_lines : Ignore.t list

  module Builder : Callgraph.Builder
end