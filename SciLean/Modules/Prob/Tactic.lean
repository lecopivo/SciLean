import SciLean.Modules.Prob.Rand
import SciLean.Modules.Prob.DRand
import SciLean.Modules.Prob.FDRand
import SciLean.Modules.Prob.RandDeriv
import SciLean.Modules.Prob.RandFwdDeriv
import SciLean.Modules.Prob.PushPullE

namespace SciLean.Prob

open Lean Meta in
simproc_decl push_fdE_into_let (FDRand.fdE _ _) := fun e => do
  unless (e.isAppOfArity ``FDRand.fdE 7) do return .visit { expr := e}
  let f := e.getArg! 5
  match f with
  | .letE name type val body nonDep =>
    let e' := .letE name type val (e.setArg 5 body) nonDep
    return .visit { expr := e' }
  | _ => return .visit { expr := e}


macro "rand_AD" : conv =>
  `(conv| simp (config := {zeta:=false}) (disch:=sorry) only [rand_AD,fderiv_id,fderiv_const])

macro "rand_push_E" : conv =>
  `(conv| simp (config := {zeta:=false}) (disch:=sorry) only [rand_push_E,FDRand.fdmean,push_fdE_into_let,fderiv_id,fderiv_const,id,ContinuousLinearMap.coe_id'])

macro "rand_pull_E" : conv =>
  `(conv| simp (config := {zeta:=false}) (disch:=sorry) only [rand_pull_E])

macro "rand_fdE_as_E" x:term : conv =>
  `(conv| simp (config := {zeta:=false}) only [FDRand.fdE_as_E $x, FDRand.fdE'_as_E $x])



open Lean Meta Elab.Term Parser.Tactic.Conv in
elab " derive_mean_fwdDeriv " f:term " by " t:convSeq : term => do

  let e ← elabTerm (← `(term| (fun x dx => fwdDeriv ℝ (fun x' => Rand.mean ($f x')) x dx) rewrite_by $t)).raw none

  lambdaTelescope e fun xs b => do

    unless xs.size = 2 do
      throwError s!"deriving probabilistic derivative should end with a lambda function of two arguments but got {← ppExpr e}"

    unless (b.isAppOfArity ``Rand.mean 5) do
      throwError "deriving probabilistic derivative should end with a term of the form `Rand.mean _`"

    let f' := b.getArg! 4

    mkLambdaFVars xs f'
