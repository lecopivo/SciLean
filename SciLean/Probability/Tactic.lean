import SciLean.Probability.PushPullExpectation
import SciLean.Util.RewriteBy

namespace SciLean.Rand


macro "rand_AD" : conv =>
  `(conv| (simp  (disch:=sorry) only [ftrans_simp]))

macro "rand_push_E" : conv =>
  `(conv| (simp (config := {zeta:=false}) (disch:=sorry) only [rand_push_E,id,ContinuousLinearMap.coe_id']))

macro "rand_pull_E" : conv =>
  `(conv| simp (config := {zeta:=false}) (disch:=sorry) only [rand_pull_E])

macro "rand_fdE_as_E" R:term ", " x:term : conv =>
  `(conv| simp (config := {zeta:=false}) only [FDRand.fdE_as_E $R $x, FDRand.fdE'_as_E $R $x])

macro "rand_compute_mean" : conv =>
  `(conv| simp (config := {zeta:=false}) (disch:=sorry) only [Rand.mean,Rand.E,rand_simp,id,weightByDensity',ftrans_simp,weightByDensityM'])


syntax Parser.assumptions := ("assuming" bracketedBinder*)?

open Lean Meta Elab.Term Parser.Tactic.Conv Parser in
elab " derive_random_approx " e:term as:assumptions " by " t:convSeq : term => do
  --
  let e ← elabTermAndSynthesize e none
  let as := as.raw[0][1].getArgs
  let (e,_prf) ← elabConvRewrite e as (← `(conv| ($t)))

  letTelescope e fun xs e => do

    unless e.isAppOfArity ``Rand.mean 6 do
      throwError "deriving probabilistic derivative should end with a term of the form `Rand.mean _`"

    mkLambdaFVars xs e.appArg!

def print_mean_variance {R} [RealScalar R] [ToString R] (r : Rand R) (n : ℕ) (msg : String) : IO Unit := do
  let mut xs : Array R := #[]
  for _ in [0:n] do
    xs := xs.push (← r.get)

  let mean := ((1:R)/n) • xs.foldl (init:=(0:R)) (fun s x => s + x)
  let var := Scalar.sqrt (((1:R)/(n-1)) •  xs.foldl (init:=(0:R)) (fun s x => s + (x - mean)^2))
  IO.println s!"Estimates value{msg}: {mean} ± {var}"
