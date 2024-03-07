import SciLean.Core.FunctionTransformations.CDeriv
import SciLean.Core.Meta.ToAnyPoint

open SciLean

variable
  {K : Type _} [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {W : Type _} [Vec K W]
  {ι : Type _} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]

namespace SciLean

variable (K)

@[fun_trans]
noncomputable
def fwdDeriv (f : X → Y) (x dx : X) : Y×Y := (f x, cderiv K f x dx)

variable {K}

namespace fwdDeriv


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem id_rule
  : fwdDeriv K (fun x : X => x) = fun x dx => (x,dx) :=
by
  unfold fwdDeriv; fun_trans

@[fun_trans]
theorem const_rule (y : Y) :
    fwdDeriv K (fun _ : X => y) = fun x dx => (y, 0) := by unfold fwdDeriv; fun_trans

@[fun_trans, to_any_point]
theorem comp_rule_at (x : X)
    (f : Y → Z) (g : X → Y)
    (hf : CDifferentiableAt K f (g x)) (hg : CDifferentiableAt K g x) :
    fwdDeriv K (fun x : X => f (g x)) x
    =
    fun dx =>
      let ydy := fwdDeriv K g x dx
      let zdz := fwdDeriv K f ydy.1 ydy.2
      zdz := by
  unfold fwdDeriv; fun_trans

@[fun_trans]
theorem comp_rule
    (f : Y → Z) (g : X → Y)
    (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    fwdDeriv K (fun x : X => f (g x))
    =
    fun x dx =>
      let ydy := fwdDeriv K g x dx
      let zdz := fwdDeriv K f ydy.1 ydy.2
      zdz := by
  unfold fwdDeriv; fun_trans

@[fun_trans, to_any_point]
theorem let_rule_at (x : X)
    (f : X → Y → Z) (g : X → Y)
    (hf : CDifferentiableAt K (fun (xy : X×Y) => f xy.1 xy.2) (x,g x)) (hg : CDifferentiableAt K g x) :
    fwdDeriv K (fun x : X => let y := g x; f x y) x
    =
    fun dx =>
      let ydy := fwdDeriv K g x dx
      let zdz := fwdDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz := by
  unfold fwdDeriv; fun_trans

@[fun_trans]
theorem let_rule
    (f : X → Y → Z) (g : X → Y)
    (hf : CDifferentiable K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : CDifferentiable K g) :
    fwdDeriv K (fun x : X => let y := g x; f x y)
    =
    fun x dx =>
      let ydy := fwdDeriv K g x dx
      let zdz := fwdDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz := by
  unfold fwdDeriv; fun_trans

@[fun_trans]
theorem apply_rule (i : ι) :
    fwdDeriv K (fun (x : (i : ι) → E i) => x i) = fun x dx => (x i, dx i) := by
  unfold fwdDeriv; fun_trans

@[fun_trans, to_any_point]
theorem pi_rule_at (x : X)
    (f : X → (i : ι) → E i) (hf : ∀ i, CDifferentiableAt K (f · i) x) :
    fwdDeriv K (fun (x : X) (i : ι) => f x i) x
    =
    fun dx =>
      (fun i => f x i, fun i => (fwdDeriv K (f · i) x dx).2) := by
  unfold fwdDeriv; fun_trans
  funext x; simp
  rw[cderiv.pi_rule_at (hf:=by fun_prop)]

@[fun_trans]
theorem pi_rule
    (f : X → (i : ι) → E i) (hf : ∀ i, CDifferentiable K (f · i)) :
    fwdDeriv K (fun (x : X) (i : ι) => f x i)
    =
    fun x dx =>
      (fun i => f x i, fun i => (fwdDeriv K (f · i) x dx).2) := by
  unfold fwdDeriv; fun_trans
  funext x; rw[cderiv.pi_rule_at (hf:=by fun_prop)]


open SciLean LeanColls

-- Prod.mk -----------------------------------v---------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem Prod.mk.arg_fstsnd.fwdDeriv_rule_at (x : X)
    (g : X → Y) (hg : CDifferentiableAt K g x)
    (f : X → Z) (hf : CDifferentiableAt K f x) :
    fwdDeriv K (fun x => (g x, f x)) x
    =
    fun dx =>
      let ydy := fwdDeriv K g x dx
      let zdz := fwdDeriv K f x dx
      ((ydy.1, zdz.1), (ydy.2, zdz.2)) := by
  unfold fwdDeriv; fun_trans


@[fun_trans]
theorem Prod.mk.arg_fstsnd.fwdDeriv_rule
    (g : X → Y) (hg : CDifferentiable K g)
    (f : X → Z) (hf : CDifferentiable K f) :
    fwdDeriv K (fun x => (g x, f x))
    =
    fun x dx =>
      let ydy := fwdDeriv K g x dx
      let zdz := fwdDeriv K f x dx
      ((ydy.1, zdz.1), (ydy.2, zdz.2)) := by
  unfold fwdDeriv; fun_trans


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem Prod.fst.arg_self.fwdDeriv_rule_at (x : X)
    (f : X → Y×Z) (hf : CDifferentiableAt K f x) :
    fwdDeriv K (fun x => (f x).1) x
    =
    fun dx =>
      let yzdyz := fwdDeriv K f x dx
      (yzdyz.1.1, yzdyz.2.1) := by
  unfold fwdDeriv; fun_trans

@[fun_trans]
theorem Prod.fst.arg_self.fwdDeriv_rule
    (f : X → Y×Z) (hf : CDifferentiable K f) :
    fwdDeriv K (fun x => (f x).1)
    =
    fun x dx =>
      let yzdyz := fwdDeriv K f x dx
      (yzdyz.1.1, yzdyz.2.1) := by
  unfold fwdDeriv; fun_trans


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem Prod.snd.arg_self.fwdDeriv_rule_at (x : X)
    (f : X → Y×Z) (hf : CDifferentiableAt K f x) :
    fwdDeriv K (fun x => (f x).2) x
    =
    fun dx =>
      let yzdyz := fwdDeriv K f x dx
      (yzdyz.1.2, yzdyz.2.2) := by
  unfold fwdDeriv; fun_trans

@[fun_trans]
theorem Prod.snd.arg_self.fwdDeriv_rule
    (f : X → Y×Z) (hf : CDifferentiable K f) :
    fwdDeriv K (fun x => (f x).2)
    =
    fun x dx =>
      let yzdyz := fwdDeriv K f x dx
      (yzdyz.1.2, yzdyz.2.2) := by
  unfold fwdDeriv; fun_trans


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem HAdd.hAdd.arg_a0a1.fwdDeriv_rule_at (x : X)
    (f g : X → Y) (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) :
    (fwdDeriv K fun x => f x + g x) x
    =
    fun dx =>
      fwdDeriv K f x dx + fwdDeriv K g x dx := by
  unfold fwdDeriv; fun_trans

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.fwdDeriv_rule
    (f g : X → Y) (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    (fwdDeriv K fun x => f x + g x)
    =
    fun x dx =>
      fwdDeriv K f x dx + fwdDeriv K g x dx := by
  unfold fwdDeriv; fun_trans


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem HSub.hSub.arg_a0a1.fwdDeriv_rule_at (x : X)
    (f g : X → Y) (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) :
    (fwdDeriv K fun x => f x - g x) x
    =
    fun dx =>
      fwdDeriv K f x dx - fwdDeriv K g x dx := by
  unfold fwdDeriv; fun_trans

@[fun_trans]
theorem HSub.hSub.arg_a0a1.fwdDeriv_rule
    (f g : X → Y) (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    (fwdDeriv K fun x => f x - g x)
    =
    fun x dx =>
      fwdDeriv K f x dx - fwdDeriv K g x dx := by
  unfold fwdDeriv; fun_trans


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.fwdDeriv_rule (x : X) (f : X → Y) :
    (fwdDeriv K fun x => - f x)
    =
    fun x dx => - fwdDeriv K f x dx := by
  unfold fwdDeriv; fun_trans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem HMul.hMul.arg_a0a1.fwdDeriv_rule_at (x : X) (f g : X → K)
    (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) :
    (fwdDeriv K fun x => f x * g x) x
    =
    fun dx =>
      let ydy := (fwdDeriv K f x dx)
      let zdz := (fwdDeriv K g x dx)
      (ydy.1 * zdz.1, zdz.2 * ydy.1 + ydy.2 * zdz.1) := by
  unfold fwdDeriv; fun_trans

@[fun_trans]
theorem HMul.hMul.arg_a0a1.fwdDeriv_rule (f g : X → K)
    (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    (fwdDeriv K fun x => f x * g x)
    =
    fun x dx =>
      let ydy := (fwdDeriv K f x dx)
      let zdz := (fwdDeriv K g x dx)
      (ydy.1 * zdz.1, zdz.2 * ydy.1 + ydy.2 * zdz.1) := by
  unfold fwdDeriv; fun_trans


-- HSMul.hSMul -----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem HSMul.hSMul.arg_a0a1.fwdDeriv_rule_at (x : X)
    (f : X → K) (g : X → Y)
    (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) :
    (fwdDeriv K fun x => f x • g x) x
    =
    fun dx =>
      let ydy := (fwdDeriv K f x dx)
      let zdz := (fwdDeriv K g x dx)
      (ydy.1 • zdz.1, ydy.1 • zdz.2 + ydy.2 • zdz.1) := by
  unfold fwdDeriv; fun_trans

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.fwdDeriv_rule
    (f : X → K) (g : X → Y)
    (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    (fwdDeriv K fun x => f x • g x)
    =
    fun x dx =>
      let ydy := (fwdDeriv K f x dx)
      let zdz := (fwdDeriv K g x dx)
      (ydy.1 • zdz.1, ydy.1 • zdz.2 + ydy.2 • zdz.1) := by
  unfold fwdDeriv; fun_trans


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem HDiv.hDiv.arg_a0a1.fwdDeriv_rule_at (x : X)
    (f : X → K) (g : X → K)
    (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) (hx : g x ≠ 0) :
    (fwdDeriv K fun x => f x / g x) x
    =
    fun dx =>
      let ydy := (fwdDeriv K f x dx)
      let zdz := (fwdDeriv K g x dx)
      (ydy.1 / zdz.1, (ydy.2 * zdz.1 - ydy.1 * zdz.2) / zdz.1^2) := by
  unfold fwdDeriv
  fun_trans (disch:=assumption)

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.fwdDeriv_rule
    (f : X → K) (g : X → K)
    (hf : CDifferentiable K f) (hg : CDifferentiable K g) (hx : ∀ x, g x ≠ 0) :
    (fwdDeriv K fun x => f x / g x)
    =
    fun x dx =>
      let ydy := (fwdDeriv K f x dx)
      let zdz := (fwdDeriv K g x dx)
      (ydy.1 / zdz.1, (ydy.2 * zdz.1 - ydy.1 * zdz.2) / zdz.1^2) := by
  unfold fwdDeriv
  fun_trans (disch:=assumption)



-- HPow.hPow -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
def HPow.hPow.arg_a0.fwdDeriv_rule_at (n : Nat) (x : X)
    (f : X → K) (hf : CDifferentiableAt K f x) :
    fwdDeriv K (fun x => f x ^ n) x
    =
    fun dx =>
      let ydy := fwdDeriv K f x dx
      (ydy.1 ^ n, n * ydy.2 * (ydy.1 ^ (n-1))) := by
  unfold fwdDeriv; fun_trans

@[fun_trans]
def HPow.hPow.arg_a0.fwdDeriv_rule (n : Nat)
    (f : X → K) (hf : CDifferentiable K f) :
    fwdDeriv K (fun x => f x ^ n)
    =
    fun x dx =>
      let ydy := fwdDeriv K f x dx
      (ydy.1 ^ n, n * ydy.2 * (ydy.1 ^ (n-1))) := by
  unfold fwdDeriv; fun_trans


-- IndexType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem IndexType.sum.arg_f.fwdDeriv_rule_at (x : X)
    (f : X → ι → Y) (hf : ∀ i, CDifferentiableAt K (f · i) x) :
    fwdDeriv K (fun x => ∑ i, f x i) x
    =
    fun dx =>
      let ydy := fun i => fwdDeriv K (f · i) x dx
      ∑ i, ydy i := by
  unfold fwdDeriv; fun_trans; sorry_proof -- need linearity of prod.mk

@[fun_trans]
theorem IndexType.sum.arg_f.fwdDeriv_rule
    (f : X → ι → Y) (hf : ∀ i, CDifferentiable K (f · i)) :
    fwdDeriv K (fun x => ∑ i, f x i)
    =
    fun x dx =>
      let ydy := fun i => fwdDeriv K (f · i) x dx
      ∑ i, ydy i := by
  unfold fwdDeriv; fun_trans; sorry_proof -- need linearity of prod.mk


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem ite.arg_te.fwdDeriv_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y) :
    fwdDeriv K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (fwdDeriv K t y) (fwdDeriv K e y) := by
  induction dec
  case isTrue h  => ext y; simp[h]; simp[h]
  case isFalse h => ext y; simp[h]; simp[h]

@[fun_trans]
theorem dite.arg_te.fwdDeriv_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y) (e : ¬c → X → Y) :
    fwdDeriv K (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => fwdDeriv K (t p) y)
             (fun p => fwdDeriv K (e p) y) := by
  induction dec
  case isTrue h  => ext y; simp[h]; simp[h]
  case isFalse h => ext y; simp[h]; simp[h]


--------------------------------------------------------------------------------

section InnerProductSpace

variable
  {R : Type _} [RealScalar R]
  {X : Type _} [Vec R X]
  {Y : Type _} [SemiHilbert R Y]


-- Inner -----------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate

@[fun_trans, to_any_point]
theorem Inner.inner.arg_a0a1.fwdDeriv_rule_at (x : X)
    (f : X → Y) (g : X → Y)
    (hf : CDifferentiableAt R f x) (hg : CDifferentiableAt R g x) :
    fwdDeriv R (fun x => ⟪f x, g x⟫[R]) x
    =
    fun dx =>
      let y₁dy₁ := fwdDeriv R f x dx
      let y₂dy₂ := fwdDeriv R g x dx
      (⟪y₁dy₁.1, y₂dy₂.1⟫[R],
       ⟪y₁dy₁.2, y₂dy₂.1⟫[R] + ⟪y₁dy₁.1, y₂dy₂.2⟫[R]) := by
  unfold fwdDeriv; fun_trans

@[fun_trans]
theorem Inner.inner.arg_a0a1.fwdDeriv_rule
    (f : X → Y) (g : X → Y)
    (hf : CDifferentiable R f) (hg : CDifferentiable R g) :
    fwdDeriv R (fun x => ⟪f x, g x⟫[R])
    =
    fun x dx =>
      let y₁dy₁ := fwdDeriv R f x dx
      let y₂dy₂ := fwdDeriv R g x dx
      (⟪y₁dy₁.1, y₂dy₂.1⟫[R],
       ⟪y₁dy₁.2, y₂dy₂.1⟫[R] + ⟪y₁dy₁.1, y₂dy₂.2⟫[R]) := by
  unfold fwdDeriv; fun_trans

@[fun_trans, to_any_point]
theorem SciLean.Norm2.norm2.arg_a0.fwdDeriv_rule_at (x : X)
    (f : X → Y) (hf : CDifferentiableAt R f x) :
    fwdDeriv R (fun x => ‖f x‖₂²[R]) x
    =
    fun dx =>
      let ydy := fwdDeriv R f x dx
      (‖ydy.1‖₂²[R], 2 * ⟪ydy.2, ydy.1⟫[R]) := by
  unfold fwdDeriv; fun_trans

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.fwdDeriv_rule
    (f : X → Y) (hf : CDifferentiable R f) :
    fwdDeriv R (fun x => ‖f x‖₂²[R])
    =
    fun x dx =>
      let ydy := fwdDeriv R f x dx
      (‖ydy.1‖₂²[R], 2 * ⟪ydy.2, ydy.1⟫[R]) := by
  unfold fwdDeriv; fun_trans

open Scalar in
@[fun_trans, to_any_point]
theorem SciLean.norm₂.arg_x.fwdDeriv_rule_at (x : X)
    (f : X → Y) (hf : CDifferentiableAt R f x) (hx : f x≠0) :
    fwdDeriv R (fun x => ‖f x‖₂[R]) x
    =
    fun dx =>
      let ydy := fwdDeriv R f x dx
      let ynorm := ‖ydy.1‖₂[R]
      (ynorm, ynorm⁻¹ * ⟪ydy.2,ydy.1⟫[R]) := by
  unfold fwdDeriv
  fun_trans (disch:=assumption)

open Scalar in
@[fun_trans]
theorem SciLean.norm₂.arg_x.fwdDeriv_rule
    (f : X → Y) (hf : CDifferentiable R f) (hx : ∀ x, f x≠0) :
    fwdDeriv R (fun x => ‖f x‖₂[R])
    =
    fun x dx =>
      let ydy := fwdDeriv R f x dx
      let ynorm := ‖ydy.1‖₂[R]
      (ynorm, ynorm⁻¹ * ⟪ydy.2,ydy.1⟫[R]) := by
  unfold fwdDeriv
  fun_trans (disch:=assumption)

end InnerProductSpace
