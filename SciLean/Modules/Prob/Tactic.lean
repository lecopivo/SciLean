import SciLean.Modules.Prob.Rand
import SciLean.Modules.Prob.DRand
import SciLean.Modules.Prob.FDRand
import SciLean.Modules.Prob.RandDeriv
import SciLean.Modules.Prob.RandFwdDeriv
import SciLean.Modules.Prob.PushPullE
import SciLean.Modules.Prob.ADTheorems


namespace SciLean.Prob


elab "push_fdE_into_let" : conv => do
  IO.println "running push_fdE_into_let"

-- open Lean Meta in
-- simproc_decl push_fdE_into_let (FDRand.fdE _ _) := fun e => do
--   unless (e.isAppOfArity ``FDRand.fdE 7) do return .visit { expr := e}
--   let f := e.getArg! 5
--   match f with
--   | .letE name type val body nonDep =>
--     let e' := .letE name type val (e.setArg 5 body) nonDep
--     return .visit { expr := e' }
--   | _ => return .visit { expr := e}


macro "rand_AD" : conv =>
  `(conv| (simp  (disch:=sorry) only [ftrans_simp,rand_AD,fderiv_id,fderiv_const]))

macro "rand_push_E" : conv =>
  `(conv| (simp (config := {zeta:=false}) (disch:=sorry) only [rand_push_E,FDRand.fdmean,fderiv_id,fderiv_const,id,ContinuousLinearMap.coe_id']))

macro "rand_pull_E" : conv =>
  `(conv| simp (config := {zeta:=false}) (disch:=sorry) only [rand_pull_E])

macro "rand_fdE_as_E" R:term ", " x:term : conv =>
  `(conv| simp (config := {zeta:=false}) only [FDRand.fdE_as_E $R $x, FDRand.fdE'_as_E $R $x])

macro "rand_compute_mean" : conv =>
  `(conv| simp (config := {zeta:=false}) (disch:=sorry) only [Rand.mean,Rand.E,rand_simp,id,weightByDensity',ftrans_simp,weightByDensityM'])

macro "simp'" : conv => `(conv| simp (config := {zeta:=false}) (disch:=sorry))



open Lean Meta Elab.Term Parser.Tactic.Conv in
elab " derive_mean_fwdDeriv " R:term " : " f:term " by " t:convSeq : term => do
  --
  let e ← elabTerm (← `(term| (fun x dx => fwdFDeriv $R (fun x => SciLean.Prob.Rand.mean ($f x)) x dx) rewrite_by $t)).raw none

  lambdaTelescope e fun xs b => do

    unless xs.size = 2 do
      throwError s!"deriving probabilistic derivative should end with a lambda function of two arguments but got {← ppExpr e}"

    unless (b.isAppOfArity ``Rand.mean 5) do
      throwError "deriving probabilistic derivative should end with a term of the form `Rand.mean _`"

    let f' := b.getArg! 4

    mkLambdaFVars xs f'


open Lean Meta Elab.Term Parser.Tactic.Conv in
elab " derive_random_approx " e:term " by " t:convSeq : term => do
  --
  let e ← elabTerm (← `(term| $e rewrite_by $t)).raw none

  unless (e.isAppOfArity ``Rand.mean 5) do
    throwError "deriving probabilistic derivative should end with a term of the form `Rand.mean _`"

  let e'' := e.getArg! 4

  return e''


/-- this function is for testing purposes and should be moved somewhere else -/
def print_mean_variance {R} [RealScalar R] [ToString R] (r : Rand (R×R)) (n : ℕ) (msg : String) : IO Unit := do
  let mut xs : Array (R×R) := #[]
  for _ in [0:n] do
    xs := xs.push (← r.get)

  let mean := ((1:R)/n) • xs.foldl (init:=(0:R×R)) (fun s x => s + x)
  let var := ((1:R)/(n-1)) •  xs.foldl (init:=(0:R×R)) (fun s x => s + ((x.1 - mean.1)^2, (x.2-mean.2)^2))
  IO.println s!"Estimates value{msg}: {mean} ± {var}"



def print_mean_variance1 {R} [RealScalar R] [ToString R] (r : Rand R) (n : ℕ) (msg : String) : IO Unit := do
  let mut xs : Array R := #[]
  for _ in [0:n] do
    xs := xs.push (← r.get)

  let mean := ((1:R)/n) • xs.foldl (init:=(0:R)) (fun s x => s + x)
  let var := Scalar.sqrt (((1:R)/(n-1)) •  xs.foldl (init:=(0:R)) (fun s x => s + (x - mean)^2))
  IO.println s!"Estimates value{msg}: {mean} ± {var}"
