import SciLean.Analysis.Calculus.CDeriv

open SciLean
#exit

set_option deprecated.oldSectionVars true
set_option linter.unusedVariables false

variable
  {K : Type _} [RCLike K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {W : Type _} [Vec K W]
  {ι : Type _} [IndexType ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]

namespace SciLean

variable (K)

@[fun_trans]
noncomputable
def fwdCDeriv (f : X → Y) (x dx : X) : Y×Y := (f x, cderiv K f x dx)

variable {K}

namespace fwdCDeriv


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem id_rule
  : fwdCDeriv K (fun x : X => x) = fun x dx => (x,dx) :=
by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem const_rule (y : Y) :
    fwdCDeriv K (fun _ : X => y) = fun x dx => (y, 0) := by unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem comp_rule_at (x : X)
    (f : Y → Z) (g : X → Y)
    (hf : CDifferentiableAt K f (g x)) (hg : CDifferentiableAt K g x) :
    fwdCDeriv K (fun x : X => f (g x)) x
    =
    fun dx =>
      let ydy := fwdCDeriv K g x dx
      let zdz := fwdCDeriv K f ydy.1 ydy.2
      zdz := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem comp_rule
    (f : Y → Z) (g : X → Y)
    (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    fwdCDeriv K (fun x : X => f (g x))
    =
    fun x dx =>
      let ydy := fwdCDeriv K g x dx
      let zdz := fwdCDeriv K f ydy.1 ydy.2
      zdz := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem let_rule_at (x : X)
    (f : X → Y → Z) (g : X → Y)
    (hf : CDifferentiableAt K (fun (xy : X×Y) => f xy.1 xy.2) (x,g x)) (hg : CDifferentiableAt K g x) :
    fwdCDeriv K (fun x : X => let y := g x; f x y) x
    =
    fun dx =>
      let ydy := fwdCDeriv K g x dx
      let zdz := fwdCDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem let_rule
    (f : X → Y → Z) (g : X → Y)
    (hf : CDifferentiable K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : CDifferentiable K g) :
    fwdCDeriv K (fun x : X => let y := g x; f x y)
    =
    fun x dx =>
      let ydy := fwdCDeriv K g x dx
      let zdz := fwdCDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem apply_rule (i : ι) :
    fwdCDeriv K (fun (x : (i : ι) → E i) => x i) = fun x dx => (x i, dx i) := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem pi_rule_at (x : X)
    (f : X → (i : ι) → E i) (hf : ∀ i, CDifferentiableAt K (f · i) x) :
    fwdCDeriv K (fun (x : X) (i : ι) => f x i) x
    =
    fun dx =>
      (fun i => f x i, fun i => (fwdCDeriv K (f · i) x dx).2) := by
  unfold fwdCDeriv; fun_trans
  funext x; simp
  rw[cderiv.pi_rule_at (hf:=by fun_prop)]

@[fun_trans]
theorem pi_rule
    (f : X → (i : ι) → E i) (hf : ∀ i, CDifferentiable K (f · i)) :
    fwdCDeriv K (fun (x : X) (i : ι) => f x i)
    =
    fun x dx =>
      (fun i => f x i, fun i => (fwdCDeriv K (f · i) x dx).2) := by
  unfold fwdCDeriv; fun_trans
  funext x; rw[cderiv.pi_rule_at (hf:=by fun_prop)]



-- Prod.mk -----------------------------------v---------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.mk.arg_fstsnd.fwdCDeriv_rule_at (x : X)
    (g : X → Y) (hg : CDifferentiableAt K g x)
    (f : X → Z) (hf : CDifferentiableAt K f x) :
    fwdCDeriv K (fun x => (g x, f x)) x
    =
    fun dx =>
      let ydy := fwdCDeriv K g x dx
      let zdz := fwdCDeriv K f x dx
      ((ydy.1, zdz.1), (ydy.2, zdz.2)) := by
  unfold fwdCDeriv; fun_trans


@[fun_trans]
theorem Prod.mk.arg_fstsnd.fwdCDeriv_rule
    (g : X → Y) (hg : CDifferentiable K g)
    (f : X → Z) (hf : CDifferentiable K f) :
    fwdCDeriv K (fun x => (g x, f x))
    =
    fun x dx =>
      let ydy := fwdCDeriv K g x dx
      let zdz := fwdCDeriv K f x dx
      ((ydy.1, zdz.1), (ydy.2, zdz.2)) := by
  unfold fwdCDeriv; fun_trans


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.fst.arg_self.fwdCDeriv_rule_at (x : X)
    (f : X → Y×Z) (hf : CDifferentiableAt K f x) :
    fwdCDeriv K (fun x => (f x).1) x
    =
    fun dx =>
      let yzdyz := fwdCDeriv K f x dx
      (yzdyz.1.1, yzdyz.2.1) := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem Prod.fst.arg_self.fwdCDeriv_rule
    (f : X → Y×Z) (hf : CDifferentiable K f) :
    fwdCDeriv K (fun x => (f x).1)
    =
    fun x dx =>
      let yzdyz := fwdCDeriv K f x dx
      (yzdyz.1.1, yzdyz.2.1) := by
  unfold fwdCDeriv; fun_trans


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.snd.arg_self.fwdCDeriv_rule_at (x : X)
    (f : X → Y×Z) (hf : CDifferentiableAt K f x) :
    fwdCDeriv K (fun x => (f x).2) x
    =
    fun dx =>
      let yzdyz := fwdCDeriv K f x dx
      (yzdyz.1.2, yzdyz.2.2) := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem Prod.snd.arg_self.fwdCDeriv_rule
    (f : X → Y×Z) (hf : CDifferentiable K f) :
    fwdCDeriv K (fun x => (f x).2)
    =
    fun x dx =>
      let yzdyz := fwdCDeriv K f x dx
      (yzdyz.1.2, yzdyz.2.2) := by
  unfold fwdCDeriv; fun_trans


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.fwdCDeriv_rule_at (x : X)
    (f g : X → Y) (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) :
    (fwdCDeriv K fun x => f x + g x) x
    =
    fun dx =>
      let ydy := fwdCDeriv K f x dx
      let zdz := fwdCDeriv K g x dx
      ydy + zdz := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.fwdCDeriv_rule
    (f g : X → Y) (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    (fwdCDeriv K fun x => f x + g x)
    =
    fun x dx =>
      let ydy := fwdCDeriv K f x dx
      let zdz := fwdCDeriv K g x dx
      ydy + zdz := by
  unfold fwdCDeriv; fun_trans


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSub.hSub.arg_a0a1.fwdCDeriv_rule_at (x : X)
    (f g : X → Y) (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) :
    (fwdCDeriv K fun x => f x - g x) x
    =
    fun dx =>
      let ydy := fwdCDeriv K f x dx
      let zdz := fwdCDeriv K g x dx
      ydy - zdz := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem HSub.hSub.arg_a0a1.fwdCDeriv_rule
    (f g : X → Y) (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    (fwdCDeriv K fun x => f x - g x)
    =
    fun x dx =>
      let ydy := fwdCDeriv K f x dx
      let zdz := fwdCDeriv K g x dx
      ydy - zdz := by
  unfold fwdCDeriv; fun_trans


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.fwdCDeriv_rule (f : X → Y) :
    (fwdCDeriv K fun x => - f x)
    =
    fun x dx => - fwdCDeriv K f x dx := by
  unfold fwdCDeriv; fun_trans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HMul.hMul.arg_a0a1.fwdCDeriv_rule_at (x : X) (f g : X → K)
    (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) :
    (fwdCDeriv K fun x => f x * g x) x
    =
    fun dx =>
      let ydy := (fwdCDeriv K f x dx)
      let zdz := (fwdCDeriv K g x dx)
      (ydy.1 * zdz.1, zdz.2 * ydy.1 + ydy.2 * zdz.1) := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem HMul.hMul.arg_a0a1.fwdCDeriv_rule (f g : X → K)
    (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    (fwdCDeriv K fun x => f x * g x)
    =
    fun x dx =>
      let ydy := (fwdCDeriv K f x dx)
      let zdz := (fwdCDeriv K g x dx)
      (ydy.1 * zdz.1, zdz.2 * ydy.1 + ydy.2 * zdz.1) := by
  unfold fwdCDeriv; fun_trans


-- HSMul.hSMul -----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.fwdCDeriv_rule_at (x : X)
    (f : X → K) (g : X → Y)
    (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) :
    (fwdCDeriv K fun x => f x • g x) x
    =
    fun dx =>
      let ydy := (fwdCDeriv K f x dx)
      let zdz := (fwdCDeriv K g x dx)
      (ydy.1 • zdz.1, ydy.1 • zdz.2 + ydy.2 • zdz.1) := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.fwdCDeriv_rule
    (f : X → K) (g : X → Y)
    (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    (fwdCDeriv K fun x => f x • g x)
    =
    fun x dx =>
      let ydy := (fwdCDeriv K f x dx)
      let zdz := (fwdCDeriv K g x dx)
      (ydy.1 • zdz.1, ydy.1 • zdz.2 + ydy.2 • zdz.1) := by
  unfold fwdCDeriv; fun_trans


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.fwdCDeriv_rule_at (x : X)
    (f : X → K) (g : X → K)
    (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) (hx : g x ≠ 0) :
    (fwdCDeriv K fun x => f x / g x) x
    =
    fun dx =>
      let ydy := (fwdCDeriv K f x dx)
      let zdz := (fwdCDeriv K g x dx)
      (ydy.1 / zdz.1, (ydy.2 * zdz.1 - ydy.1 * zdz.2) / zdz.1^2) := by
  unfold fwdCDeriv
  fun_trans (disch:=assumption)

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.fwdCDeriv_rule
    (f : X → K) (g : X → K)
    (hf : CDifferentiable K f) (hg : CDifferentiable K g) (hx : ∀ x, g x ≠ 0) :
    (fwdCDeriv K fun x => f x / g x)
    =
    fun x dx =>
      let ydy := (fwdCDeriv K f x dx)
      let zdz := (fwdCDeriv K g x dx)
      (ydy.1 / zdz.1, (ydy.2 * zdz.1 - ydy.1 * zdz.2) / zdz.1^2) := by
  unfold fwdCDeriv
  fun_trans (disch:=assumption)



-- HPow.hPow -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
def HPow.hPow.arg_a0.fwdCDeriv_rule_at (n : Nat) (x : X)
    (f : X → K) (hf : CDifferentiableAt K f x) :
    fwdCDeriv K (fun x => f x ^ n) x
    =
    fun dx =>
      let ydy := fwdCDeriv K f x dx
      (ydy.1 ^ n, n * ydy.2 * (ydy.1 ^ (n-1))) := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
def HPow.hPow.arg_a0.fwdCDeriv_rule (n : Nat)
    (f : X → K) (hf : CDifferentiable K f) :
    fwdCDeriv K (fun x => f x ^ n)
    =
    fun x dx =>
      let ydy := fwdCDeriv K f x dx
      (ydy.1 ^ n, n * ydy.2 * (ydy.1 ^ (n-1))) := by
  unfold fwdCDeriv; fun_trans


-- sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem sum.arg_f.fwdCDeriv_rule_at (x : X)
    (f : X → ι → Y) (hf : ∀ i, CDifferentiableAt K (f · i) x) :
    fwdCDeriv K (fun x => ∑ i, f x i) x
    =
    fun dx =>
      let ydy := fun i => fwdCDeriv K (f · i) x dx
      ∑ i, ydy i := by
  unfold fwdCDeriv; fun_trans; sorry_proof -- need linearity of prod.mk

@[fun_trans]
theorem sum.arg_f.fwdCDeriv_rule
    (f : X → ι → Y) (hf : ∀ i, CDifferentiable K (f · i)) :
    fwdCDeriv K (fun x => ∑ i, f x i)
    =
    fun x dx =>
      let ydy := fun i => fwdCDeriv K (f · i) x dx
      ∑ i, ydy i := by
  unfold fwdCDeriv; fun_trans; sorry_proof -- need linearity of prod.mk


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem ite.arg_te.fwdCDeriv_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y) :
    fwdCDeriv K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (fwdCDeriv K t y) (fwdCDeriv K e y) := by
  induction dec
  case isTrue h  => ext y; simp[h]; simp[h]
  case isFalse h => ext y; simp[h]; simp[h]

@[fun_trans]
theorem dite.arg_te.fwdCDeriv_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y) (e : ¬c → X → Y) :
    fwdCDeriv K (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => fwdCDeriv K (t p) y)
             (fun p => fwdCDeriv K (e p) y) := by
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

@[fun_trans]
theorem Inner.inner.arg_a0a1.fwdCDeriv_rule_at (x : X)
    (f : X → Y) (g : X → Y)
    (hf : CDifferentiableAt R f x) (hg : CDifferentiableAt R g x) :
    fwdCDeriv R (fun x => ⟪f x, g x⟫[R]) x
    =
    fun dx =>
      let y₁dy₁ := fwdCDeriv R f x dx
      let y₂dy₂ := fwdCDeriv R g x dx
      (⟪y₁dy₁.1, y₂dy₂.1⟫[R],
       ⟪y₁dy₁.2, y₂dy₂.1⟫[R] + ⟪y₁dy₁.1, y₂dy₂.2⟫[R]) := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem Inner.inner.arg_a0a1.fwdCDeriv_rule
    (f : X → Y) (g : X → Y)
    (hf : CDifferentiable R f) (hg : CDifferentiable R g) :
    fwdCDeriv R (fun x => ⟪f x, g x⟫[R])
    =
    fun x dx =>
      let y₁dy₁ := fwdCDeriv R f x dx
      let y₂dy₂ := fwdCDeriv R g x dx
      (⟪y₁dy₁.1, y₂dy₂.1⟫[R],
       ⟪y₁dy₁.2, y₂dy₂.1⟫[R] + ⟪y₁dy₁.1, y₂dy₂.2⟫[R]) := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.fwdCDeriv_rule_at (x : X)
    (f : X → Y) (hf : CDifferentiableAt R f x) :
    fwdCDeriv R (fun x => ‖f x‖₂²[R]) x
    =
    fun dx =>
      let ydy := fwdCDeriv R f x dx
      (‖ydy.1‖₂²[R], 2 * ⟪ydy.2, ydy.1⟫[R]) := by
  unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.fwdCDeriv_rule
    (f : X → Y) (hf : CDifferentiable R f) :
    fwdCDeriv R (fun x => ‖f x‖₂²[R])
    =
    fun x dx =>
      let ydy := fwdCDeriv R f x dx
      (‖ydy.1‖₂²[R], 2 * ⟪ydy.2, ydy.1⟫[R]) := by
  unfold fwdCDeriv; fun_trans

open Scalar in
@[fun_trans]
theorem SciLean.norm₂.arg_x.fwdCDeriv_rule_at (x : X)
    (f : X → Y) (hf : CDifferentiableAt R f x) (hx : f x≠0) :
    fwdCDeriv R (fun x => ‖f x‖₂[R]) x
    =
    fun dx =>
      let ydy := fwdCDeriv R f x dx
      let ynorm := ‖ydy.1‖₂[R]
      (ynorm, ynorm⁻¹ * ⟪ydy.2,ydy.1⟫[R]) := by
  unfold fwdCDeriv
  fun_trans (disch:=assumption)

open Scalar in
@[fun_trans]
theorem SciLean.norm₂.arg_x.fwdCDeriv_rule
    (f : X → Y) (hf : CDifferentiable R f) (hx : ∀ x, f x≠0) :
    fwdCDeriv R (fun x => ‖f x‖₂[R])
    =
    fun x dx =>
      let ydy := fwdCDeriv R f x dx
      let ynorm := ‖ydy.1‖₂[R]
      (ynorm, ynorm⁻¹ * ⟪ydy.2,ydy.1⟫[R]) := by
  unfold fwdCDeriv
  fun_trans (disch:=assumption)

end InnerProductSpace
