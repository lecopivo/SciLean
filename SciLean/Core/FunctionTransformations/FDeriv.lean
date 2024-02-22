import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

import Mathlib.Tactic.FunTrans.Attr
import Mathlib.Tactic.FunTrans.Elab

import SciLean.Core.Meta.ToAnyPoint
import SciLean.Core.FunctionPropositions.IsContinuousLinearMap
import SciLean.Core.FunctionPropositions.Differentiable

variable
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]

namespace SciLean

attribute [fun_trans] fderiv

-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem fderiv.id_rule :
    (fderiv K fun x : X => x) = fun _ => fun dx =>L[K] dx := by ext x dx; simp

@[fun_trans]
theorem fderiv.const_rule (x : X) :
    (fderiv K fun _ : Y => x)
    =
    -- fun _ => fun =>[K] 0 := by -- todo: fix fun_prop
    fun _ => ContinuousLinearMap.mk' K (fun _ => 0) (IsContinuousLinearMap.const_rule) := by
  ext x dx; simp

@[fun_trans]
theorem fderiv.apply_rule (i : ι) :
    (fderiv K fun (x : (i : ι) → E i) => x i)
    =
    fun _ => fun dx =>L[K] dx i := by
  funext x; sorry_proof -- somehow use fderiv_pi

@[fun_trans, to_any_point]
theorem fderiv.comp_rule_at
    (f : Y → Z) (g : X → Y) (x : X)
    (hf : DifferentiableAt K f (g x)) (hg : DifferentiableAt K g x) :
    (fderiv K fun x : X => f (g x)) x
    =
    let y := g x
    fun dx =>L[K]
      let dy := fderiv K g x dx
      let dz := fderiv K f y dy
      dz :=
by
  rw[show (fun x => f (g x)) = f ∘ g by rfl]
  rw[fderiv.comp x hf hg]
  ext dx; simp


@[fun_trans, to_any_point]
theorem fderiv.let_rule_at
    (f : X → Y → Z) (g : X → Y) (x : X)
    (hf : DifferentiableAt K (fun xy : X×Y => f xy.1 xy.2) (x, g x))
    (hg : DifferentiableAt K g x) :
    (fderiv K fun x : X => let y := g x; f x y) x
    =
    let y := g x
    fun dx =>L[K]
      let dy := fderiv K g x dx
      let dz := fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
      dz :=
by
  have h : (fun x => f x (g x)) = (fun xy : X×Y => f xy.1 xy.2) ∘ (fun x => (x, g x)) := by rfl
  conv =>
    lhs
    rw[h]
    rw[fderiv.comp x hf (DifferentiableAt.prod (by simp) hg)]
    rw[DifferentiableAt.fderiv_prod (by simp) hg]
  ext dx; simp[ContinuousLinearMap.comp]



@[fun_trans, to_any_point]
theorem fderiv.pi_rule_at
    (f : X → (i : ι) → E i) (x : X) (hf : ∀ i, DifferentiableAt K (f · i) x) :
    (fderiv K fun (x : X) (i : ι) => f x i) x
    =
    fun dx =>L[K] fun i =>
      fderiv K (f · i) x dx := fderiv_pi hf

end SciLean

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

-- Prod.mk -----------------------------------v---------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem Prod.mk.arg_fstsnd.fderiv_rule_at  (x : X)
    (g : X → Y) (hg : DifferentiableAt K g x)
    (f : X → Z) (hf : DifferentiableAt K f x) :
    fderiv K (fun x => (g x, f x)) x
    =
    fun dx =>L[K]
      (fderiv K g x dx, fderiv K f x dx) := by
  apply DifferentiableAt.fderiv_prod hg hf



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem Prod.fst.arg_self.fderiv_rule_at (x : X)
    (f : X → Y×Z) (hf : DifferentiableAt K f x) :
    fderiv K (fun x => (f x).1) x
    =
    fun dx =>L[K] (fderiv K f x dx).1 := by
  apply fderiv.fst hf


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.snd.arg_self.fderiv_rule_at (x : X)
    (f : X → Y×Z) (hf : DifferentiableAt K f x) :
    fderiv K (fun x => (f x).2) x
    =
    fun dx =>L[K] (fderiv K f x dx).2 := by
  apply fderiv.snd hf


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem HAdd.hAdd.arg_a0a1.fderiv_rule_at (x : X)
    (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fderiv K fun x => f x + g x) x
    =
    fun dx =>L[K]
      fderiv K f x dx + fderiv K g x dx := fderiv_add hf hg


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem HSub.hSub.arg_a0a1.fderiv_rule_at (x : X)
    (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fderiv K fun x => f x - g x) x
    =
    fun dx =>L[K]
      fderiv K f x dx - fderiv K g x dx := fderiv_sub hf hg


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.fderiv_rule (f : X → Y) :
    (fderiv K fun x => - f x)
    =
    fun x => fun dx =>L[K] -fderiv K f x dx := by funext x; apply fderiv_neg


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem HMul.hMul.arg_a0a1.fderiv_rule_at
    {Y : Type _} [NormedCommRing Y] [NormedAlgebra K Y] (x : X)
    (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fderiv K fun x => f x * g x) x
    =
    let fx := f x
    let gx := g x
    fun dx =>L[K]
      (fderiv K g x dx) * fx + (fderiv K f x dx) * gx := by
  ext dx
  simp[fderiv_mul hf hg, mul_comm]



-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem HSMul.hSMul.arg_a0a1.fderiv_rule_at (x : X)
    (f : X → K) (g : X → Y)
    (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fderiv K fun x => f x • g x) x
    =
    let k := f x
    let y := g x
    fun dx =>L[K]
      k • (fderiv K g x dx) + (fderiv K f x dx) • y := fderiv_smul hf hg


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem HDiv.hDiv.arg_a0a1.fderiv_rule_at
    {R : Type _} [NontriviallyNormedField R] [NormedAlgebra R K]
    (x : R) (f : R → K) (g : R → K)
    (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x) (hx : g x ≠ 0) :
    (fderiv R fun x => f x / g x) x
    =
    let k := f x
    let k' := g x
    fun dx =>L[R]
      ((fderiv R f x dx) * k' - k * (fderiv R g x dx)) / k'^2 := by
  have h : ∀ (f : R → K) x, fderiv R f x 1 = deriv f x := by simp[deriv]
  ext; simp[h]; apply deriv_div hf hg hx


-- HPow.hPow ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
def HPow.hPow.arg_a0.fderiv_rule_at (n : Nat) (x : X)
    (f : X → K) (hf : DifferentiableAt K f x) :
    fderiv K (fun x => f x ^ n) x
    =
    fun dx =>L[K] n * fderiv K f x dx * (f x ^ (n-1)) :=
by
  induction n
  case zero =>
    simp; rfl
  case succ n hn =>
    ext dx
    simp_rw[pow_succ]
    rw[HMul.hMul.arg_a0a1.fderiv_rule_at x f _ (by fun_prop) (by fun_prop)]
    rw[hn]
    induction n
    case zero => simp
    case succ =>
      rw[show ∀ (n : Nat), n.succ - 1 = n by simp]
      rw[pow_succ]
      simp; ring
