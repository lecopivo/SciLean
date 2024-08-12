import SciLean.Analysis.Convenient.CDifferentiable
import SciLean.Analysis.Convenient.HasSemiAdjoint

import SciLean.Analysis.Calculus.CDeriv

-- import Lean.Meta.Tactic.Assumption

set_option linter.unusedVariables false


namespace SciLean

variable
  (K : Type _) [RCLike K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {ι : Type _} [IndexType ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]

@[fun_prop]
def HasAdjDiffAt (f : X → Y) (x : X) : Prop :=
    CDifferentiableAt K f x ∧ HasSemiAdjoint K (cderiv K f x)

@[fun_prop]
def HasAdjDiff (f : X → Y) : Prop := ∀ x, HasAdjDiffAt K f x

@[fun_prop]
theorem HasAdjDiff.hasAdjDiffAt (f : X → Y) (x) (hf : HasAdjDiff K f) :
    HasAdjDiffAt K f x := hf x

@[fun_prop]
theorem HasAdjDiffAt.CDifferentiableAt (f : X → Y) (x) (hf : HasAdjDiffAt K f x) :
    CDifferentiableAt K f x := hf.1

@[fun_prop]
theorem HasAdjDiff.cdifferentiable (f : X → Y) (hf : HasAdjDiff K f) :
    CDifferentiable K f := fun x => (hf x).1

@[fun_prop]
theorem HasAdjDiff.cdifferentiableAt (f : X → Y) (x) (hf : HasAdjDiff K f) :
    CDifferentiableAt K f x := (hf x).1

@[fun_prop]
theorem cderiv.arg_dx.hasSemiAdjointAt (f : X → Y) (x) (hf : HasAdjDiffAt K f x) :
    HasSemiAdjoint K (cderiv K f x) := hf.2

@[fun_prop]
theorem cderiv.arg_dx.hasSemiAdjoint (f : X → Y) (x) (hf : HasAdjDiff K f) :
    HasSemiAdjoint K (cderiv K f x) := by fun_prop

@[fun_prop]
theorem HasSemiAdjoint.hasAdjDiff (f : X → Y) (hf : HasSemiAdjoint K f) :
    HasAdjDiff K f := by
  intro x
  constructor

  · fun_prop
  · fun_trans; fun_prop


----------------------------------------------------------------------------------------------------
-- Lambda calculus rules ---------------------------------------------------------------------------

@[fun_prop]
theorem HasAdjDiffAt.id_rule (x) : HasAdjDiffAt K (fun x : X => x) x := by
  constructor
  · fun_prop
  · fun_trans; fun_prop

@[fun_prop]
theorem HasAdjDiff.id_rule : HasAdjDiff K (fun x : X => x) := by intro x; fun_prop

@[fun_prop]
theorem HasAdjDiffAt.const_rule (x) (y : Y) : HasAdjDiffAt K (fun _ : X => y) x := by
  constructor
  · fun_prop
  · fun_trans; apply HasSemiAdjoint.const_rule

@[fun_prop]
theorem HasAjdDiff.const_rule (y : Y) : HasAdjDiff K (fun _ : X => y) := by
  intro x; fun_prop

@[fun_prop]
theorem HasAdjDiffAt.apply_rule (x) (i : ι) :
    HasAdjDiffAt K (fun x : (i : ι) → E i => x i) x := by
  constructor
  · fun_prop
  · fun_trans; fun_prop

@[fun_prop]
theorem HasAdjDiff.apply_rule (i : ι) :
    HasAdjDiff K (fun x : (i : ι) → E i => x i) := by
  intro x; fun_prop

@[fun_prop]
theorem HasAdjDiffAt.comp_rule
    (f : Y → Z) (g : X → Y) (x) (hf : HasAdjDiffAt K f (g x)) (hg : HasAdjDiffAt K g x) :
    HasAdjDiffAt K (fun x => f (g x)) x := by
  constructor
  · fun_prop
  · fun_trans; fun_prop

@[fun_prop]
theorem HasAdjDiff.comp_rule
    (f : Y → Z) (g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    HasAdjDiff K (fun x => f (g x)) := by
  intro x; constructor
  · fun_prop
  · fun_trans; fun_prop

@[fun_prop]
theorem HasAdjDiffAt.pi_rule
    (f : X → (i : ι) → E i) (x) (hf : ∀ i, HasAdjDiffAt K (f · i) x) :
    HasAdjDiffAt K (fun x i => f x i) x := by
  have := fun i => (hf i).1
  constructor
  · fun_prop
  · rw[cderiv.pi_rule_at (hf:=by assumption)]
    fun_prop

@[fun_prop]
theorem HasAdjDiff.pi_rule
    (f : X → (i : ι) → E i) (hf : ∀ i, HasAdjDiff K (f · i)) :
    HasAdjDiff K (fun x i => f x i) := by
  intro x; apply HasAdjDiffAt.pi_rule; fun_prop


--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

variable
  (K : Type _) [RCLike K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]
  {ι : Type _} [IndexType ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]



-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Prod.mk --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.mk.arg_fstsnd.HasAdjDiffAt_rule (x : X)
    (g : X → Y) (hg : HasAdjDiffAt K g x)
    (f : X → Z) (hf : HasAdjDiffAt K f x) :
    HasAdjDiffAt K (fun x => (g x, f x)) x := by
  constructor; fun_prop; fun_trans; fun_prop


@[fun_prop]
theorem Prod.mk.arg_fstsnd.HasAdjDiff_rule
  (g : X → Y) (hg : HasAdjDiff K g)
  (f : X → Z) (hf : HasAdjDiff K f)
  : HasAdjDiff K (fun x => (g x, f x)) :=
by
  intros x; constructor; fun_prop; fun_trans; fun_prop


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.fst.arg_self.HasAdjDiffAt_rule (x : X)
    (f : X → Y×Z) (hf : HasAdjDiffAt K f x) :
    HasAdjDiffAt K (fun x => (f x).1) x := by
  constructor; fun_prop; fun_trans; fun_prop

@[fun_prop]
theorem Prod.fst.arg_self.HasAdjDiff_rule
    (f : X → Y×Z) (hf : HasAdjDiff K f) :
    HasAdjDiff K (fun x => (f x).1) := by
  intro x; fun_prop



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.snd.arg_self.HasAdjDiffAt_rule (x : X)
    (f : X → Y×Z) (hf : HasAdjDiffAt K f x) :
    HasAdjDiffAt K (fun x => (f x).2) x := by
  constructor; fun_prop; fun_trans; fun_prop

@[fun_prop]
theorem Prod.snd.arg_self.HasAdjDiff_rule
    (f : X → Y×Z) (hf : HasAdjDiff K f) :
    HasAdjDiff K (fun x => (f x).2) := by
  intro x; fun_prop


-- cderiv ----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem cderiv.arg_dx.HasSemiAdjoint_rule_at
    (f : Y → Z) (g : X → Y) (y : Y)
    (hf : HasAdjDiffAt K f y) (hg : HasSemiAdjoint K g) :
    HasSemiAdjoint K fun dx => cderiv K f y (g dx) := by
  apply HasSemiAdjoint.comp_rule K (cderiv K f y) g hf.2 hg

@[fun_prop]
theorem cderiv.arg_dx.HasSemiAdjoint_rule
    (f : Y → Z) (g : X → Y) (y : Y)
    (hf : HasAdjDiff K f) (hg : HasSemiAdjoint K g) :
    HasSemiAdjoint K fun dx => cderiv K f y (g dx) := by fun_prop


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Neg.neg.arg_a0.HasAdjDiffAt_rule (x : X)
    (f : X → Y) (hf : HasAdjDiffAt K f x) :
    HasAdjDiffAt K (fun x => - f x) x := by
  constructor; fun_prop; fun_trans; fun_prop

@[fun_prop]
theorem Neg.neg.arg_a0.HasAdjDiff_rule
    (f : X → Y) (hf : HasAdjDiff K f) :
    HasAdjDiff K (fun x => - f x) := by
  intro x; fun_prop


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.HasAdjDiffAt_rule (x : X)
    (f g : X → Y) (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x) :
    HasAdjDiffAt K (fun x => f x + g x) x := by
  constructor; fun_prop; fun_trans; fun_prop

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.HasAdjDiff_rule
    (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    HasAdjDiff K (fun x => f x + g x) := by
  intro x; fun_prop


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSub.hSub.arg_a0a1.HasAdjDiffAt_rule (x : X)
    (f g : X → Y) (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x) :
    HasAdjDiffAt K (fun x => f x - g x) x := by
  constructor; fun_prop; fun_trans; fun_prop

@[fun_prop]
theorem HSub.hSub.arg_a0a1.HasAdjDiff_rule
    (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    HasAdjDiff K (fun x => f x - g x) := by
  intro x; fun_prop


-- HMul.hMul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def HMul.hMul.arg_a0a1.HasAdjDiffAt_rule (x : X)
    (f g : X → K) (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x) :
    HasAdjDiffAt K (fun x => f x * g x) x := by
  constructor; fun_prop; fun_trans; fun_prop

@[fun_prop]
def HMul.hMul.arg_a0a1.HasAdjDiff_rule
    (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    HasAdjDiff K (fun x => f x * g x) := by
  intro x; fun_prop


-- SMul.sMul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSMul.hSMul.arg_a1.HasAdjDiffAt_rule
    (c : K) (g : X → Y) (x : X) (hg : HasAdjDiffAt K g x) :
    HasAdjDiffAt K (fun x => c • g x) x := by
  constructor; fun_prop; fun_trans; fun_prop

@[fun_prop]
theorem HSMul.hSMul.arg_a1.HasAdjDiff_rule
    (c : K) (g : X → Y) (hg : HasAdjDiff K g) :
    HasAdjDiff K (fun x => c • g x) := by
  intro x; fun_prop

@[fun_prop]
theorem HSMul.hSMul.arg_a0a1.HasAdjDiffAt_rule (x : X)
    {Y : Type _} [SemiHilbert K Y]
    (f : X → K) (g : X → Y)
    (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x) :
    HasAdjDiffAt K (fun x => f x • g x) x := by
  constructor; fun_prop; fun_trans; fun_prop

@[fun_prop]
theorem HSMul.hSMul.arg_a0a1.HasAdjDiff_rule
    {Y : Type _} [SemiHilbert K Y]
    (f : X → K) (g : X → Y)
    (hf : HasAdjDiff K f) (hg : HasAdjDiff K g ) :
    HasAdjDiff K (fun x => f x • g x) := by
  intro x; fun_prop


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def HDiv.hDiv.arg_a0a1.HasAdjDiffAt_rule (x : X)
    (f : X → K) (g : X → K)
    (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x) (hx : g x ≠ 0) :
    HasAdjDiffAt K (fun x => f x / g x) x := by
  set_option trace.Meta.Tactic.fun_trans true in
  -- constructor; fun_prop (disch:=assumption); fun_trans (disch:=assumption); fun_prop
  sorry_proof

@[fun_prop]
def HDiv.hDiv.arg_a0a1.HasAdjDiff_rule
    (f : X → K) (g : X → K)
    (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : ∀ x, g x ≠ 0) :
    HasAdjDiff K (fun x => f x / g x) := by
  intro x; fun_prop (disch:=aesop)


-- HPow.hPow -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def HPow.hPow.arg_a0.HasAdjDiffAt_rule (x : X)
    (n : Nat) (f : X → K) (hf : HasAdjDiffAt K f x) :
    HasAdjDiffAt K (fun x => f x ^ n) x := by
  constructor; fun_prop; fun_trans; fun_prop

@[fun_prop]
def HPow.hPow.arg_a0.HasAdjDiff_rule
    (n : Nat) (f : X → K) (hf : HasAdjDiff K f) :
    HasAdjDiff K (fun x => f x ^ n) := by
  intro x; fun_prop


-- IndexType.sum ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem IndexType.sum.arg_f.HasAdjDiffAt_rule (x : X)
    (f : X → ι → Y) (hf : ∀ i, HasAdjDiffAt K (f · i) x) :
    HasAdjDiffAt K (fun x => ∑ i, f x i) x := by
  constructor; fun_prop; fun_trans; fun_prop

@[fun_prop]
theorem IndexType.sum.arg_f.HasAdjDiff_rule
    (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (f · i)) :
    HasAdjDiff K (fun x => ∑ i, f x i) := by
  intro x; fun_prop


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem ite.arg_te.HasAdjDiffAt_rule (x : X)
    (c : Prop) [dec : Decidable c] (t e : X → Y)
    (ht : HasAdjDiffAt K t x) (he : HasAdjDiffAt K e x) :
    HasAdjDiffAt K (fun x => ite c (t x) (e x)) x := by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]

@[fun_prop]
theorem ite.arg_te.HasAdjDiff_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y)
    (ht : HasAdjDiff K t) (he : HasAdjDiff K e) :
    HasAdjDiff K (fun x => ite c (t x) (e x)) := by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]

@[fun_prop]
theorem dite.arg_te.HasAdjDiffAt_rule (x : X)
    (c : Prop) [dec : Decidable c]
    (t : c → X → Y) (e : ¬c → X → Y)
    (ht : ∀ h, HasAdjDiffAt K (t h) x) (he : ∀ h, HasAdjDiffAt K (e h) x) :
    HasAdjDiffAt K (fun x => dite c (t · x) (e · x)) x := by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]

@[fun_prop]
theorem dite.arg_te.HasAdjDiff_rule
    (c : Prop) [dec : Decidable c]
    (t : c → X → Y) (e : ¬c → X → Y)
    (ht : ∀ h, HasAdjDiff K (t h)) (he : ∀ h, HasAdjDiff K (e h)) :
    HasAdjDiff K (fun x => dite c (t · x) (e · x)) := by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]


--------------------------------------------------------------------------------

section InnerProductSpace

variable
  {R : Type _} [RealScalar R]
  {X : Type _} [SemiInnerProductSpace R X]
  {Y : Type _} [SemiHilbert R Y]

-- Inner -----------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate

@[fun_prop]
theorem Inner.inner.arg_a0a1.HasAdjDiffAt_rule (x : X)
    (f : X → Y) (g : X → Y)
    (hf : HasAdjDiffAt R f x) (hg : HasAdjDiffAt R g x) :
    HasAdjDiffAt R (fun x => ⟪f x, g x⟫[R]) x := by
  constructor; fun_prop; fun_trans; fun_prop

@[fun_prop]
theorem Inner.inner.arg_a0a1.HasAdjDiff_rule
    (f : X → Y) (g : X → Y)
    (hf : HasAdjDiff R f) (hg : HasAdjDiff R g) :
    HasAdjDiff R fun x => ⟪f x, g x⟫[R] := by
  intro x; fun_prop


@[fun_prop]
theorem Norm2.norm2.arg_a0.HasAdjDiffAt_rule (x : X)
    (f : X → Y) (hf : HasAdjDiffAt R f x) :
    HasAdjDiffAt R (fun x => ‖f x‖₂²[R]) x := by
  constructor; fun_prop; fun_trans; fun_prop

@[fun_prop]
theorem Norm2.norm2.arg_a0.HasAdjDiff_rule
    (f : X → Y) (hf : HasAdjDiff R f) :
    HasAdjDiff R fun x => ‖f x‖₂²[R] := by
  intro x; fun_prop

@[fun_prop]
theorem norm₂.arg_x.HasAdjDiffAt_rule (x : X)
    (f : X → Y) (hf : HasAdjDiffAt R f x) (hfz : f x ≠ 0) :
    HasAdjDiffAt R (fun x => ‖f x‖₂[R]) x := by
  constructor;
  fun_prop (disch:=assumption);
  sorry_proof --fun_trans (disch:=assumption); fun_prop (disch:=assumption)

@[fun_prop]
theorem norm₂.arg_x.HasAdjDiff_rule
    (f : X → Y) (hf : HasAdjDiff R f) (hfz : ∀ x, f x ≠ 0) :
    HasAdjDiff R fun x => ‖f x‖₂[R] := by
  intro x; fun_prop (disch:=aesop)

end InnerProductSpace


-- semiAdjoint -----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem semiAdjoint.arg_y.CDifferentiableAt_rule {W : Type _} [Vec K W] (w : W)
    (f : X → Y) (a0 : W → Y) (hf : CDifferentiable K f) (ha0 : CDifferentiableAt K a0 w) :
    CDifferentiableAt K (fun w => semiAdjoint K f (a0 w)) w := by fun_prop


@[fun_prop]
theorem semiAdjoint.arg_y.HasAdjDiffAt_rule (w : W)
    (f : X → Y) (a0 : W → Y) (hf : CDifferentiable K f) (ha0 : HasAdjDiffAt K a0 w) :
    HasAdjDiffAt K (fun w => semiAdjoint K f (a0 w)) w := by
  constructor
  fun_prop
  sorry_proof

@[fun_prop]
theorem semiAdjoint.arg_y.HasAdjDiff_rule
    (f : X → Y) (a0 : W → Y) (hf : CDifferentiable K f) (ha0 : HasAdjDiff K a0) :
    HasAdjDiff K (fun w => semiAdjoint K f (a0 w)) := by
  intro w; fun_prop
