import SciLean.Core.Objects.Vec
import SciLean.Core.Objects.SemiInnerProductSpace
import SciLean.Core.Objects.FinVec
import SciLean.Core.Objects.Scalar
import SciLean.Core.FunctionPropositions.CDifferentiable

import SciLean.Core.Meta.ToAnyPoint

set_option linter.unusedVariables false

open LeanColls

namespace SciLean

local notation "∞" => (⊤ : ℕ∞)

variable
  (K : Type _) [RCLike K] (n : ℕ∞)
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [IndexType ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]

/-- `CDifferentiableAt f x` - conveniently differentiable function `f` at point `x`. -/
@[irreducible, fun_prop]
def ContCDiffAt (f : X → Y) (x : X) : Prop :=
  ∀ (c : K → X),
      c 0 = x
      →
      Curve.ContDiffAt c 0 n
      →
      Curve.ContDiffAt (f∘c) 0 n


/-- `ContCDiff f` - conveniently differentiable function `f`.  -/
@[fun_prop]
def ContCDiff (f : X → Y) : Prop := ∀ x, ContCDiffAt K n f x

@[fun_prop, to_any_point]
theorem ContCDiffAt.id_rule (x : X) :
    ContCDiffAt K n (fun x : X => x) x := by sorry_proof

@[fun_prop, to_any_point]
theorem ContCDiffAt.const_rule (y : Y) (x : X) :
    ContCDiffAt K n (fun _ : X => y) x := by sorry_proof

@[fun_prop, to_any_point]
theorem ContCDiffAt.comp_rule (x : X)
    (f : Y → Z) (g : X → Y)
    (hf : ContCDiffAt K n f (g x)) (hg : ContCDiffAt K n g x) :
    ContCDiffAt K n (fun x => f (g x)) x := by sorry_proof

@[fun_prop, to_any_point]
theorem ContCDiffAt.apply_rule
    (i : ι) (x) : ContCDiffAt K n (fun x : (i : ι) → E i => x i) x := by sorry_proof

@[fun_prop, to_any_point]
theorem ContCDiffAt.pi_rule (x : X)
    (f : X → (i : ι) → E i)
    (hf : ∀ i, ContCDiffAt K n (f · i) x) :
    ContCDiffAt K n (fun x i => f x i) x := by sorry_proof

@[fun_prop, to_any_point]
theorem ContCDiffAt.le_rule (x : X) (f : X → Y) (hf : ContCDiffAt K m f x) (h : n ≤ m) :
    ContCDiffAt K n f x := sorry_proof

@[fun_prop, to_any_point]
theorem ContCDiff.le_rule (f : X → Y) (hf : ContCDiff K m f) (h : n ≤ m) :
    ContCDiff K n f := sorry_proof

@[fun_prop]
theorem ContCDiff.ContCDiffAt_rule (x : X) (f : X → Y) (hf : ContCDiff K n f) :
    ContCDiffAt K n f x := hf x

@[fun_prop]
theorem ContCDiff.id_rule :
    ContCDiff K n (fun x : X => x) := by intro x; fun_prop

@[fun_prop]
theorem ContCDiff.const_rule (y : Y) :
    ContCDiff K n (fun _ : X => y) := by intro x; fun_prop

@[fun_prop]
theorem ContCDiff.comp_rule
    (f : Y → Z) (g : X → Y)
    (hf : ContCDiff K n f) (hg : ContCDiff K n g) :
    ContCDiff K n (fun x => f (g x)) := by intro x; fun_prop

@[fun_prop]
theorem ContCDiff.apply_rule
    (i : ι) : ContCDiff K n (fun x : (i : ι) → E i => x i) := by intro x; fun_prop

@[fun_prop]
theorem ContCDiff.pi_rule (x : X)
    (f : X → (i : ι) → E i)
    (hf : ∀ i, ContCDiff K n (f · i)) :
    ContCDiff K n (fun x i => f x i) := by intro x; apply ContCDiffAt.pi_rule; fun_prop


----------------------------------------------------------------------------------------------------


-- transition rules to CDifferentiable

@[fun_prop]
theorem CDifferentaibleAt.ContCDiffAt_rule (x : X) (f : X → Y) (hf : ContCDiffAt K n f x) (h : 0 < n) :
    CDifferentiableAt K f x := sorry_proof

@[fun_prop]
theorem CDifferentaibleAt.ContCDiffAt_rule' (x : X) (f : X → Y) (hf : ContCDiffAt K ∞ f x) :
    CDifferentiableAt K f x := by fun_prop (disch:=aesop)

@[fun_prop]
theorem CDifferentaible.ContCDiff_rule (f : X → Y) (hf : ContCDiff K n f) (h : 0 < n) :
    CDifferentiable K f := by intro x; fun_prop (disch:=assumption)

@[fun_prop]
theorem CDifferentaible.ContCDiff_rule' (f : X → Y) (hf : ContCDiff K ∞ f) :
    CDifferentiable K f := by intro x; fun_prop


section NormedSpaces

variable
  {U} [NormedAddCommGroup U] [NormedSpace K U]
  {V} [NormedAddCommGroup V] [NormedSpace K V]

-- theorem Differentiable.ContCDiff_rule (f : U → V) (hf : Differentiable K f) :
--     ContCDiff K f := sorry_proof

-- theorem DifferentiableAt.ContCDiffAt_rule (f : U → V) (x : U) (hf : DifferentiableAt K f x) :
--     ContCDiffAt K f x := sorry_proof

end NormedSpaces

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

variable
  (K : Type _) [RCLike K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [IndexType ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]


-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Prod.mk --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop,to_any_point]
theorem Prod.mk.arg_fstsnd.ContCDiffAt_rule (x : X)
  (g : X → Y) (hg : ContCDiffAt K n g x)
  (f : X → Z) (hf : ContCDiffAt K n f x)
  : ContCDiffAt K n (fun x => (g x, f x)) x
  := by sorry_proof


@[fun_prop]
theorem Prod.mk.arg_fstsnd.ContCDiff_rule
  (g : X → Y) (hg : ContCDiff K n g)
  (f : X → Z) (hf : ContCDiff K n f)
  : ContCDiff K n (fun x => (g x, f x))
  := by intro x; fun_prop


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop,to_any_point]
theorem Prod.fst.arg_self.ContCDiffAt_rule (x : X)
    (f : X → Y×Z) (hf : ContCDiffAt K n f x) :
    ContCDiffAt K n (fun x => (f x).1) x := by sorry_proof


@[fun_prop]
theorem Prod.fst.arg_self.ContCDiff_rule
    (f : X → Y×Z) (hf : ContCDiff K n f) :
    ContCDiff K n (fun x => (f x).1):= by intro x; fun_prop


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop, to_any_point]
theorem Prod.snd.arg_self.ContCDiffAt_rule (x : X)
    (f : X → Y×Z) (hf : ContCDiffAt K n f x) :
    ContCDiffAt K n (fun x => (f x).2) x := by sorry_proof

@[fun_prop]
theorem Prod.snd.arg_self.ContCDiff_rule
    (f : X → Y×Z) (hf : ContCDiff K n f) :
    ContCDiff K n (fun x => (f x).2) := by sorry_proof


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop, to_any_point]
theorem Neg.neg.arg_a0.ContCDiffAt_rule
    (x : X) (f : X → Y) (hf : ContCDiffAt K n f x) :
    ContCDiffAt K n (fun x => - f x) x := by sorry_proof

@[fun_prop]
theorem Neg.neg.arg_a0.ContCDiff_rule
    (f : X → Y) (hf : ContCDiff K n f) :
    ContCDiff K n (fun x => - f x) := by sorry_proof


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop, to_any_point]
theorem HAdd.hAdd.arg_a0a1.ContCDiffAt_rule
    (x : X) (f g : X → Y) (hf : ContCDiffAt K n f x) (hg : ContCDiffAt K n g x) :
    ContCDiffAt K n (fun x => f x + g x) x := by sorry_proof

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.ContCDiff_rule
    (f g : X → Y) (hf : ContCDiff K n f) (hg : ContCDiff K n g) :
    ContCDiff K n (fun x => f x + g x) := by sorry_proof


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop, to_any_point]
theorem HSub.hSub.arg_a0a1.ContCDiffAt_rule
    (x : X) (f g : X → Y) (hf : ContCDiffAt K n f x) (hg : ContCDiffAt K n g x) :
    ContCDiffAt K n (fun x => f x - g x) x := by sorry_proof

@[fun_prop]
theorem HSub.hSub.arg_a0a1.ContCDiff_rule
    (f g : X → Y) (hf : ContCDiff K n f) (hg : ContCDiff K n g) :
    ContCDiff K n (fun x => f x - g x) := by sorry_proof


-- HMul.hMul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop, to_any_point]
def HMul.hMul.arg_a0a1.ContCDiffAt_rule
    (x : X) (f g : X → K) (hf : ContCDiffAt K n f x) (hg : ContCDiffAt K n g x) :
    ContCDiffAt K n (fun x => f x * g x) x := by sorry_proof

@[fun_prop]
def HMul.hMul.arg_a0a1.ContCDiff_rule
    (f g : X → K) (hf : ContCDiff K n f) (hg : ContCDiff K n g) :
    ContCDiff K n (fun x => f x * g x) := by sorry_proof


-- SMul.sMul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop,to_any_point]
def HSMul.hSMul.arg_a0a1.ContCDiffAt_rule
  (x : X) (f : X → K) (g : X → Y) (hf : ContCDiffAt K n f x) (hg : ContCDiffAt K n g x)
  : ContCDiffAt K n (fun x => f x • g x) x
  := by sorry_proof

@[fun_prop,to_any_point]
theorem HSMul.hSMul.arg_a1.ContCDiffAt_rule_nat
    (c : ℕ) (f : X → Y) (x) (hf : ContCDiffAt K n f x) :
    ContCDiffAt K n (fun x => c • f x) x := by sorry_proof

@[fun_prop,to_any_point]
theorem HSMul.hSMul.arg_a1.ContCDiffAt_rule_int
    (c : ℤ) (f : X → Y) (x) (hf : ContCDiffAt K n f x) :
    ContCDiffAt K n (fun x => c • f x) x := by sorry_proof


@[fun_prop]
def HSMul.hSMul.arg_a0a1.ContCDiff_rule
  (f : X → K) (g : X → Y) (hf : ContCDiff K n f) (hg : ContCDiff K n g)
  : ContCDiff K n (fun x => f x • g x)
  := by intro x; fun_prop

@[fun_prop]
theorem HSMul.hSMul.arg_a1.ContCDiff_rule_n
    (c : ℕ) (f : X → Y)  (hf : ContCDiff K n f) :
    ContCDiff K n (fun x => c • f x) := by intro x; fun_prop

@[fun_prop]
theorem HSMul.hSMul.arg_a1.ContCDiff_rule_int
    (c : ℤ) (f : X → Y) (hf : ContCDiff K n f) :
    ContCDiff K n (fun x => c • f x) := by intro x; fun_prop


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop,to_any_point]
def HDiv.hDiv.arg_a0a1.ContCDiffAt_rule (x : X)
    (f : X → K) (g : X → K)
    (hf : ContCDiffAt K n f x) (hg : ContCDiffAt K n g x) (hx : g x ≠ 0) :
    ContCDiffAt K n (fun x => f x / g x) x := by sorry_proof

@[fun_prop,to_any_point]
def HDiv.hDiv.arg_a0.ContCDiffAt_rule (x : X)
    (f : X → K) (r : K)
    (hf : ContCDiffAt K n f x) (hr : r ≠ 0) :
    ContCDiffAt K n (fun x => f x / r) x := by
  fun_prop (disch:=intros; assumption)


@[fun_prop]
def HDiv.hDiv.arg_a0a1.ContCDiff_rule
    (f : X → K) (g : X → K)
    (hf : ContCDiff K n f) (hg : ContCDiff K n g) (hx : ∀ x, g x ≠ 0) :
    ContCDiff K n (fun x => f x / g x) := by intro x; fun_prop (disch:=aesop)

@[fun_prop,to_any_point]
def HDiv.hDiv.arg_a0.ContCDiff_rule
    (f : X → K) (r : K)
    (hf : ContCDiff K n f) (hr : r ≠ 0) :
    ContCDiff K n (fun x => f x / r) := by
  fun_prop (disch:=intros; assumption)


-- HPow.hPow -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop,to_any_point]
def HPow.hPow.arg_a0.ContCDiffAt_rule
    (m : Nat) (x : X) (f : X → K) (hf : ContCDiffAt K n f x) :
    ContCDiffAt K n (fun x => f x ^ m) x := by sorry_proof

@[fun_prop]
def HPow.hPow.arg_a0.ContCDiff_rule
    (m : Nat)  (f : X → K) (hf : ContCDiff K n f) :
    ContCDiff K n (fun x => f x ^ m) := by intro x; fun_prop


-- IndexType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop,to_any_point]
theorem IndexType.sum.arg_f.ContCDiffAt_rule
  (f : X → ι → Y) (x : X) (hf : ∀ i, ContCDiffAt K n (fun x => f x i) x)
  : ContCDiffAt K n (fun x => ∑ i, f x i) x := by sorry_proof


@[fun_prop]
theorem IndexType.sum.arg_f.ContCDiff_rule
  (f : X → ι → Y) (hf : ∀ i, ContCDiff K n (fun x => f x i))
  : ContCDiff K n (fun x => ∑ i, f x i) := by intro x; fun_prop


--------------------------------------------------------------------------------

section InnerProductSpace

variable
  {R : Type _} [RealScalar R]
  {X : Type _} [Vec R X]
  {Y : Type _} [SemiHilbert R Y]

-- Inner -----------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate

@[fun_prop,to_any_point]
theorem Inner.inner.arg_a0a1.ContCDiffAt_rule
    (f : X → Y) (g : X → Y) (x : X)
    (hf : ContCDiffAt R n f x) (hg : ContCDiffAt R n g x) :
    ContCDiffAt R n (fun x => ⟪f x, g x⟫[R]) x := by sorry_proof

@[fun_prop]
theorem Inner.inner.arg_a0a1.ContCDiff_rule
    (f : X → Y) (g : X → Y)
    (hf : ContCDiff R n f) (hg : ContCDiff R n g) :
    ContCDiff R n (fun x => ⟪f x, g x⟫[R]) := by intro x; fun_prop

@[fun_prop,to_any_point]
theorem SciLean.Norm2.norm2.arg_a0.ContCDiffAt_rule
  (f : X → Y) (x : X) (hf : ContCDiffAt R n f x)
  : ContCDiffAt R n (fun x => ‖f x‖₂²[R]) x := by
  simp[← SemiInnerProductSpace.inner_norm2]
  fun_prop

@[fun_prop]
theorem SciLean.Norm2.norm2.arg_a0.ContCDiff_rule
  (f : X → Y) (hf : ContCDiff R n f)
  : ContCDiff R n (fun x => ‖f x‖₂²[R]) := by intro x; fun_prop

@[fun_prop,to_any_point]
theorem SciLean.norm₂.arg_x.ContCDiffAt_rule
    (f : X → Y) (x : X)
    (hf : ContCDiffAt R n f x) (hx : f x≠0) :
    ContCDiffAt R n (fun x => ‖f x‖₂[R]) x := by sorry_proof

@[fun_prop]
theorem SciLean.norm₂.arg_x.ContCDiff_rule
    (f : X → Y)
    (hf : ContCDiff R n f) (hx : ∀ x, f x≠0) :
    ContCDiff R n (fun x => ‖f x‖₂[R]) := by intro x; fun_prop (disch:=aesop)

end InnerProductSpace

namespace SciLean
section OnFinVec

variable
  {K : Type _} [RCLike K]
  {IX : Type} [IndexType IX] [LawfulIndexType IX] [DecidableEq IX] {X : Type _} [FinVec IX K X]
  {IY : Type} [IndexType IY] [LawfulIndexType IY] [DecidableEq IY] {Y : Type _} [FinVec IY K Y]
  {IZ : Type} [IndexType IZ] [LawfulIndexType IZ] [DecidableEq IZ] {Z : Type _} [FinVec IZ K Z]

@[fun_prop,to_any_point]
theorem Basis.proj.arg_x.ContCDiffAt_rule (i : IX) (x)
  : ContCDiffAt K n (fun x : X => ℼ i x) x := by sorry_proof

@[fun_prop,to_any_point]
theorem DualBasis.dualProj.arg_x.ContCDiffAt_rule (i : IX) (x)
  : ContCDiffAt K n (fun x : X => ℼ' i x) x := by sorry_proof

@[fun_prop,to_any_point]
theorem BasisDuality.toDual.arg_x.ContCDiffAt_rule (x)
  : ContCDiffAt K n (fun x : X => BasisDuality.toDual x) x := by sorry_proof

@[fun_prop,to_any_point]
theorem BasisDuality.fromDual.arg_x.ContCDiffAt_rule (x)
  : ContCDiffAt K n (fun x : X => BasisDuality.fromDual x) x := by sorry_proof

@[fun_prop]
theorem Basis.proj.arg_x.ContCDiff_rule (i : IX)
  : ContCDiff K n (fun x : X => ℼ i x) := by sorry_proof

@[fun_prop]
theorem DualBasis.dualProj.arg_x.ContCDiff_rule (i : IX)
  : ContCDiff K n (fun x : X => ℼ' i x) := by sorry_proof

@[fun_prop]
theorem BasisDuality.toDual.arg_x.ContCDiff_rule
  : ContCDiff K n (fun x : X => BasisDuality.toDual x) := by sorry_proof

@[fun_prop]
theorem BasisDuality.fromDual.arg_x.ContCDiff_rule
  : ContCDiff K n (fun x : X => BasisDuality.fromDual x) := by sorry_proof

end OnFinVec
end SciLean
