(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Tacinterp
open Decl_expr
open Mod_subst


val intern_proof_instr : glob_sign -> raw_proof_instr -> glob_proof_instr
val interp_proof_instr : Decl_mode.pm_info ->
  Evd.evar_map -> Environ.env -> glob_proof_instr -> proof_instr
