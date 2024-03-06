import SciLean.Core.Rand.Rand
import SciLean.Core.Rand.Tactic
import SciLean.Core.Rand.Distributions.Uniform
import SciLean.Core.Rand.Distributions.Sphere

import SciLean.Core.FunctionTransformations
import SciLean.Core.Notation.CDeriv
import SciLean.Core.Notation.FwdDeriv

import SciLean.Core.FloatAsReal
import SciLean.Tactic.LetUtils
import SciLean.Tactic.LetEnter

import SciLean.Tactic.ConvInduction

open MeasureTheory

namespace SciLean

-- Pretty printing of `Nat.recOn`
local syntax "rec_val" term ppLine "| " term " => " term ppLine "| " term ", " term " => "  term : term
@[local app_unexpander Nat.recOn]
def unexpandNatRecOn : Lean.PrettyPrinter.Unexpander
  | `($(_) $mot $n $base $succ) =>
    match succ with
    | `(fun ($m:ident : $Y:term) ($prev:ident : $P:term) $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | `(fun $m:ident $prev:ident $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | _ => throw ()
  | `($(_) $n $base $succ) =>
    match succ with
    | `(fun ($m:ident : $Y:term) ($prev:ident : $P:term) $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | `(fun $m:ident $prev:ident $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | _ => throw ()
  | _ => throw ()

@[local app_unexpander Nat.rec]
def unexpandNatRec : Lean.PrettyPrinter.Unexpander
  | `($(_) $mot $base $succ $n) =>
    match succ with
    | `(fun ($m:ident : $Y:term) ($prev:ident : $P:term) $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | `(fun $m:ident $prev:ident $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | _ => throw ()
  | `($(_) $base $succ $n) =>
    match succ with
    | `(fun ($m:ident : $Y:term) ($prev:ident : $P:term) $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | `(fun $m:ident $prev:ident $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | _ => throw ()
  | _ => throw ()




variable {Y : Type} [SemiHilbert Float Y] [Module ℝ Y] [IsScalarTower ℝ Float Y]
set_default_scalar Float


open RealScalar in
noncomputable
def harmonicRec (n : ℕ) (φ : Vec3 → Float) (g : Vec3 → Y) (x : Vec3) : Y :=
  match n with
  | 0 => g x
  | m+1 => (4*(pi:Float))⁻¹ • ∫' (x' : sphere (0:Vec3) (1:Float)), harmonicRec m φ g (x + φ x • x'.1)


def walkOnSpheres (φ : Vec3 → Float) (g : Vec3 → Y) (n : ℕ) (x : Vec3) : Rand Y := do
  let f : Rand (Vec3 → Y) :=
    derive_random_approx
      (fun x => harmonicRec n φ g x)
    by
      induction n n' prev h
        . simp[harmonicRec]
        . simp[harmonicRec,h]
          simp only [smul_push,cintegral.arg_f.push_lambda]
          rw[integral_as_uniform_E Float]
      rw[pull_E_nat_recOn (x₀:=_) (r:=_) (hf:=by fun_prop)]
      let_unfold density
      simp (config:={zeta:=false})
  let f' ← f
  pure (f' x)



#exit
#check Nat

def φ (x : Vec3) : Float := |‖x‖₂ - 1|
def g (x : Vec3) : Float := if ‖x‖₂² < 1.01 then 1 else 0

#eval φ v[1,0,0]

#eval Prob.print_mean_variance (walkOnSpheres φ g 10 v[3,0,0]) 1000 ""



@[fun_prop]
theorem harmonicRec.arg_x.CDifferentiable_rule (n : ℕ)
    (φ : Vec3 → Float) (g : Vec3 → Y)
    (hφ : CDifferentiable Float φ) (hg : CDifferentiable Float g) :
    CDifferentiable Float (fun x : Vec3 => harmonicRec n φ g x) := by
  induction n <;> (simp[harmonicRec]; fun_prop)


noncomputable
def harmonicRec.arg_x.cderiv (n : ℕ)
    (φ : Vec3 → Float) (φ' : Vec3 → Vec3 → Float) (g : Vec3 → Y) (g' : Vec3 → Vec3 → Y) :=
    (∂ x, harmonicRec n φ g x)
  rewrite_by
    assuming (hφ' : ∂ φ = φ') (hφ : CDifferentiable Float φ)
             (hg' : ∂ g = g') (hg : CDifferentiable Float g)
    induction n n' du h
      . simp[harmonicRec]; fun_trans
      . simp only [harmonicRec]; fun_trans only [ftrans_simp]

noncomputable
def harmonicRec.arg_x.fwdDeriv (n : ℕ)
    (φ : Vec3 → Float) (φ' : Vec3 → Vec3 → Float×Float)
    (g : Vec3 → Y) (g' : Vec3 → Vec3 → Y×Y) :=
    (∂> x, harmonicRec n φ g x)
  rewrite_by
    assuming (hφ' : ∂> φ = φ') (hφ : CDifferentiable Float φ)
             (hg' : ∂> g = g') (hg : CDifferentiable Float g)
    induction n n' du h
      . simp[harmonicRec]; fun_trans
      . simp[harmonicRec];
        enter[x];
        -- simp (config:={zeta:=false}) only [smul_push]
        fun_trans (config:= {zeta:=false,singlePass:=true}) only [Tactic.let_normalize,ftrans_simp]
