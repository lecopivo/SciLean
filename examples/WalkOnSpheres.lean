import SciLean.Core.Rand.Distributions.WalkOnSpheres
import SciLean.Core.Rand.RandGen

import SciLean.Util.DefOptimize

import Mathlib.Tactic.LiftLets

-- namespace SciLean
open SciLean Prob

set_default_scalar Float

def φ (x : Vec3) : Float := |‖x‖₂ - 1|
def g (x : Vec3) : Float := if ‖x‖₂² < 1.5 then 1 else 0

def walkOnSpheres' := @walkOnSpheres rewrite_by unfold walkOnSpheres

def_optimize walkOnSpheres' by
  simp[uniform,Bind.bind,Pure.pure,UniformRand.uniform]

def uniformSpherePoint : SciLean.Rand Float := do
  let p ← (uniform (sphere (0:Vec3) 1.0))
  return p.1.x


@[inline]
def uniformR (R) [RealScalar R] : SciLean.Rand R := {
  spec :=
    erase sorry
  rand :=
    fun g => do
    let N : Nat := stdRange.2
    let (n,g) := stdNext g
    let y := (n : R) / (N : R)
    pure (y, g)
}

@[inline]
def uniformF : SciLean.Rand Float := {
  spec :=
    erase sorry
  rand :=
    fun g => do
    let N : Nat := stdRange.2
    let (n,g) := stdNext g
    let y := (n.toUInt64.toFloat) / (N.toUInt64.toFloat)
    pure (y, g)
}

def bnormalize (d : sphere (0:Vec3) 1.0) (s : Float) (x : sphere (0:Vec3) 1.0) :
    sphere (0:Vec3) 1.0 :=
  let xd := ⟪d.1,x.1⟫[Float]
  let xp := x.1 - xd • d.1
  let x' := (s * xd) • d.1 + xp
  ⟨x'.normalize, sorry_proof⟩

def hih (n x : Vec3) (s : Float) : Vec3 :=
  let x' := ((s-1) * ⟪n,x⟫[Float]) • n + x
  (1/‖x'‖₂) • x'

variable (n x : Vec3) (s : Float)

set_option trace.Meta.Tactic.fun_prop true in
example : SciLean.CDifferentiableAt Float (↿fun x' x' : Vec3 => (1/‖x'‖₂[Float]) • x')
        (x, ((s - 1) * ⟪n, x⟫_Float) • n + x) := by fun_prop (disch:=sorry_proof)


open Lean Parser Term in
syntax (name := lift_lets) "lift_lets" (Parser.Tactic.config)? : conv

open Lean Meta Elab.Tactic.Conv Mathlib Tactic in
elab_rules : tactic
  | `(conv| lift_lets $[$cfg:config]?) => do
    let config ← elabConfig (mkOptionalNode cfg)
    let lhs ← getLhs
    let lhs' ← lhs.liftLets mkLetFVars config
    changeLhs lhs'




set_option profiler true in
set_option profiler.threshold 5 in
-- set_option trace.Meta.Tactic.fun_trans true in
-- set_option trace.Meta.Tactic.fun_prop true in
-- set_option trace.Meta.Tactic.fun_trans.unify true in
-- set_option trace.Meta.Tactic.fun_trans.discharge true in
-- set_option trace.Meta.Tactic.let_normalize true in
#check ((∂> x', hih n x' s) x)
  rewrite_by assuming (h : x≠0)
    unfold hih
    fun_trans (config:={zeta:=false,singlePass:=true}) (disch:=sorry) only [hih,ftrans_simp]
    simp (config:={zeta:=false,singlePass:=true}) only [Tactic.let_normalize,ftrans_simp]
    lift_lets


    -- fun_trans (config:={zeta:=false}) (disch:=sorry) only [hih,ftrans_simp]



def main : IO Unit := do

  timeit "  auto impl" <| Prob.print_mean_variance (walkOnSpheres φ g 100 v[10,0,0]) 1000 ""
  -- timeit "manual impl" <| Prob.print_mean_variance (walkOnSpheres.manualImpl φ g 100 v[10,0,0]) 10000 ""
  -- timeit "manual2impl" <| Prob.print_mean_variance (walkOnSpheres.manualImplV2 φ g 100 v[10,0,0]) 10000 ""
  -- timeit "   opt impl" <| Prob.print_mean_variance (walkOnSpheres' φ g 100 v[10,0,0]) 10000 ""
  timeit "referece time" <| Prob.print_mean_variance (uniformSpherePoint) 1000000 ""

  timeit "uniformI time" <| Prob.print_mean_variance (uniformI Float) 2000000 ""
  timeit "uniformR time" <| Prob.print_mean_variance (uniformR Float) 2000000 ""
  timeit "uniformF time" <| Prob.print_mean_variance (uniformF) 2000000 ""
  timeit " custom rand num generation" <| randGenTest 200000
  timeit "    std rand num generation" <| randStdGenTest 200000
  timeit "    std rand num generation" <| randStdGenNatTest 200000
  timeit "mathlib rand num generation" <| randMathlibTest 200000





#check _root_.Rand
