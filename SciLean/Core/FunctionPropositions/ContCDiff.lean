import SciLean.Core.Objects.Vec
import SciLean.Core.Objects.SemiInnerProductSpace
import SciLean.Core.Objects.FinVec
import SciLean.Core.Objects.Scalar

set_option linter.unusedVariables false

open LeanColls

namespace SciLean

local notation "∞" => (⊤ : ℕ∞)

variable
  (K : Type _) [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [IndexType ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]

/-- `CDifferentiableAt f x` - conveniently differentiable function `f` at point `x`. -/
@[irreducible, fun_prop]
def ContCDiffAt (n : ℕ∞) (f : X → Y) (x : X) : Prop :=
  ∀ (c : K → X),
      c 0 = x
      →
      Curve.ContDiffAt c 0 n
      →
      Curve.ContDiffAt (f∘c) 0 n

#exit
/-- `ContCDiff f` - conveniently differentiable function `f`.  -/
@[fun_prop]
def ContCDiff (f : X → Y) : Prop := ∀ x, ContCDiffAt K f x

variable (X)
@[fun_prop]
theorem ContCDiffAt.id_rule (x : X)
  : ContCDiffAt K (fun x : X => x) x
  := by sorry_proof

@[fun_prop]
theorem ContCDiff.id_rule
  : ContCDiff K (fun x : X => x)
  := by sorry_proof

@[fun_prop]
theorem ContCDiffAt.const_rule (y : Y) (x : X)
  : ContCDiffAt K (fun _ : X => y) x
  := by sorry_proof

@[fun_prop]
theorem ContCDiff.const_rule (y : Y)
  : ContCDiff K (fun _ : X => y)
  := by sorry_proof
variable {X}

@[fun_prop]
theorem ContCDiffAt.comp_rule
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : ContCDiffAt K f (g x)) (hg : ContCDiffAt K g x)
  : ContCDiffAt K (fun x => f (g x)) x
  := by sorry_proof

@[fun_prop]
theorem ContCDiff.comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : ContCDiff K f) (hg : ContCDiff K g)
  : ContCDiff K (fun x => f (g x))
  := by sorry_proof


variable (E)
@[fun_prop]
theorem ContCDiffAt.apply_rule
  (i : ι) (x)
  : ContCDiffAt K (fun x : (i : ι) → E i => x i) x :=
by sorry_proof

@[fun_prop]
theorem ContCDiff.apply_rule (i : ι)
  : ContCDiff K (fun x : (i : ι) → E i => x i) :=
by sorry_proof
variable {E}

@[fun_prop]
theorem ContCDiffAt.pi_rule
  (f : X → (i : ι) → E i) (x : X)
  (hf : ∀ i, ContCDiffAt K (f · i) x)
  : ContCDiffAt K (fun x i => f x i) x
  := by sorry_proof

@[fun_prop]
theorem ContCDiff.pi_rule
  (f : X → (i : ι) → E i)
  (hf : ∀ i, ContCDiff K (f · i))
  : ContCDiff K (fun x i => f x i)
  := by sorry_proof

@[fun_prop]
theorem ContCDiffAt.ContCDiff_rule (f : X → Y) (x : X) (hf : ContCDiff K f) :
    ContCDiffAt K f x := hf x


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
  (K : Type _) [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [IndexType ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]


-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Prod.mk --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.mk.arg_fstsnd.ContCDiffAt_rule
  (x : X)
  (g : X → Y) (hg : ContCDiffAt K g x)
  (f : X → Z) (hf : ContCDiffAt K f x)
  : ContCDiffAt K (fun x => (g x, f x)) x
  := by sorry_proof

@[fun_prop]
theorem Prod.mk.arg_fstsnd.ContCDiff_rule
  (g : X → Y) (hg : ContCDiff K g)
  (f : X → Z) (hf : ContCDiff K f)
  : ContCDiff K (fun x => (g x, f x))
  := by intro x; fun_prop


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.fst.arg_self.ContCDiff_rule
  (f : X → Y×Z) (hf : ContCDiff K f)
  : ContCDiff K (fun x => (f x).1)  := by sorry_proof

@[fun_prop]
theorem Prod.fst.arg_self.ContCDiffAt_rule
  (x : X)
  (f : X → Y×Z) (hf : ContCDiffAt K f x)
  : ContCDiffAt K (fun x => (f x).1) x
  := by fun_prop


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.snd.arg_self.ContCDiff_rule
  (f : X → Y×Z) (hf : ContCDiff K f)
  : ContCDiff K (fun x => (f x).2)  := by sorry_proof

@[fun_prop]
theorem Prod.snd.arg_self.ContCDiffAt_rule
  (x : X)
  (f : X → Y×Z) (hf : ContCDiffAt K f x)
  : ContCDiffAt K (fun x => (f x).2) x
  := by fun_prop


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Neg.neg.arg_a0.ContCDiff_rule
  (f : X → Y) (hf : ContCDiff K f)
  : ContCDiff K (fun x => - f x)  := by sorry_proof

@[fun_prop]
theorem Neg.neg.arg_a0.ContCDiffAt_rule
  (x : X) (f : X → Y) (hf : ContCDiffAt K f x)
  : ContCDiffAt K (fun x => - f x) x
  := by fun_prop


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.ContCDiff_rule
  (f g : X → Y) (hf : ContCDiff K f) (hg : ContCDiff K g)
  : ContCDiff K (fun x => f x + g x)  := by sorry_proof

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.ContCDiffAt_rule
  (x : X) (f g : X → Y) (hf : ContCDiffAt K f x) (hg : ContCDiffAt K g x)
  : ContCDiffAt K (fun x => f x + g x) x
  := by fun_prop


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSub.hSub.arg_a0a1.ContCDiff_rule
  (f g : X → Y) (hf : ContCDiff K f) (hg : ContCDiff K g)
  : ContCDiff K (fun x => f x - g x)  := by sorry_proof

@[fun_prop]
theorem HSub.hSub.arg_a0a1.ContCDiffAt_rule
  (x : X) (f g : X → Y) (hf : ContCDiffAt K f x) (hg : ContCDiffAt K g x)
  : ContCDiffAt K (fun x => f x - g x) x
  := by fun_prop


-- HMul.hMul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def HMul.hMul.arg_a0a1.ContCDiff_rule
  (f g : X → K) (hf : ContCDiff K f) (hg : ContCDiff K g)
  : ContCDiff K (fun x => f x * g x)  := by sorry_proof

@[fun_prop]
def HMul.hMul.arg_a0a1.ContCDiffAt_rule
  (x : X) (f g : X → K) (hf : ContCDiffAt K f x) (hg : ContCDiffAt K g x)
  : ContCDiffAt K (fun x => f x * g x) x
  := by fun_prop


-- SMul.sMul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def HSMul.hSMul.arg_a0a1.ContCDiff_rule
  (f : X → K) (g : X → Y) (hf : ContCDiff K f) (hg : ContCDiff K g)
  : ContCDiff K (fun x => f x • g x)
  := by sorry_proof

@[fun_prop]
def HSMul.hSMul.arg_a0a1.ContCDiffAt_rule
  (x : X) (f : X → K) (g : X → Y) (hf : ContCDiffAt K f x) (hg : ContCDiffAt K g x)
  : ContCDiffAt K (fun x => f x • g x) x
  := by fun_prop

@[fun_prop]
theorem HSMul.hSMul.arg_a1.ContCDiff_rule_nat
    (c : ℕ) (f : X → Y) (hf : ContCDiff K f) : ContCDiff K fun x => c • f x := by
  sorry_proof

@[fun_prop]
theorem HSMul.hSMul.arg_a1.ContCDiffAt_rule_nat
    (c : ℕ) (f : X → Y) (x) (hf : ContCDiffAt K f x) :
    ContCDiffAt K (fun x => c • f x) x := by
  fun_prop

@[fun_prop]
theorem HSMul.hSMul.arg_a1.ContCDiff_rule_int
    (c : ℤ) (f : X → Y) (hf : ContCDiff K f) : ContCDiff K fun x => c • f x := by
  sorry_proof

@[fun_prop]
theorem HSMul.hSMul.arg_a1.ContCDiffAt_rule_int
    (c : ℤ) (f : X → Y) (x) (hf : ContCDiffAt K f x) :
    ContCDiffAt K (fun x => c • f x) x := by
  fun_prop



-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def HDiv.hDiv.arg_a0a1.ContCDiffAt_rule
  (x : X) (f : X → K) (g : X → K)
  (hf : ContCDiffAt K f x) (hg : ContCDiffAt K g x) (hx : g x ≠ 0)
  : ContCDiffAt K (fun x => f x / g x) x
  := by sorry_proof

@[fun_prop]
def HDiv.hDiv.arg_a0a1.ContCDiff_rule
  (f : X → K) (g : X → K)
  (hf : ContCDiff K f) (hg : ContCDiff K g) (hx : ∀ x, g x ≠ 0)
  : ContCDiff K (fun x => f x / g x)
  := by intro x; fun_prop (disch:=apply hx)

@[fun_prop]
def HDiv.hDiv.arg_a0.ContCDiff_rule
  (f : X → K) (r : K)
  (hf : ContCDiff K f) (hr : r ≠ 0)
  : ContCDiff K (fun x => f x / r) :=
by
  fun_prop (disch:=intros; assumption)

@[fun_prop]
def HDiv.hDiv.arg_a0.ContCDiffAt_rule
  (x : X) (f : X → K) (r : K)
  (hf : ContCDiffAt K f x) (hr : r ≠ 0)
  : ContCDiffAt K (fun x => f x / r) x :=
by
  fun_prop (disch:=intros; assumption)



-- HPow.hPow -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def HPow.hPow.arg_a0.ContCDiff_rule
  (f : X → K) (hf : ContCDiff K f)
  : ContCDiff K (fun x => f x ^ n)
  := by sorry_proof

@[fun_prop]
def HPow.hPow.arg_a0.ContCDiffAt_rule
  (n : Nat) (x : X) (f : X → K) (hf : ContCDiffAt K f x)
  : ContCDiffAt K (fun x => f x ^ n) x
  := by fun_prop



-- EnumType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_prop]
theorem IndexType.sum.arg_f.ContCDiffAt_rule
  (f : X → ι → Y) (x : X) (hf : ∀ i, ContCDiffAt K (fun x => f x i) x)
  : ContCDiffAt K (fun x => ∑ i, f x i) x :=
by
  sorry_proof


@[fun_prop]
theorem IndexType.sum.arg_f.ContCDiff_rule
  (f : X → ι → Y) (x : X) (hf : ∀ i, ContCDiff K (fun x => f x i))
  : ContCDiff K (fun x => ∑ i, f x i) :=
by
  sorry_proof


--------------------------------------------------------------------------------

section InnerProductSpace

variable
  {R : Type _} [RealScalar R]
  {X : Type _} [Vec R X]
  {Y : Type _} [SemiHilbert R Y]

-- Inner -----------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate

@[fun_prop]
theorem Inner.inner.arg_a0a1.ContCDiff_rule
    (f : X → Y) (g : X → Y)
    (hf : ContCDiff R f) (hg : ContCDiff R g) :
    ContCDiff R (fun x => ⟪f x, g x⟫[R]) := by sorry_proof

@[fun_prop]
theorem Inner.inner.arg_a0a1.ContCDiffAt_rule
    (f : X → Y) (g : X → Y) (x : X)
    (hf : ContCDiffAt R f x) (hg : ContCDiffAt R g x) :
    ContCDiffAt R (fun x => ⟪f x, g x⟫[R]) x := by fun_prop


@[fun_prop]
theorem SciLean.Norm2.norm2.arg_a0.ContCDiff_rule
  (f : X → Y) (hf : ContCDiff R f)
  : ContCDiff R (fun x => ‖f x‖₂²[R]) :=
by
  simp[← SemiInnerProductSpace.inner_norm2]
  fun_prop


@[fun_prop]
theorem SciLean.Norm2.norm2.arg_a0.ContCDiffAt_rule
  (f : X → Y) (x : X) (hf : ContCDiffAt R f x)
  : ContCDiffAt R (fun x => ‖f x‖₂²[R]) x :=
by
  simp[← SemiInnerProductSpace.inner_norm2]
  fun_prop


@[fun_prop]
theorem SciLean.norm₂.arg_x.ContCDiff_rule
  (f : X → Y) (hf : ContCDiff R f) (hx : f x≠0)
  : ContCDiff R (fun x => ‖f x‖₂[R]) := by sorry_proof

@[fun_prop]
theorem SciLean.norm₂.arg_x.ContCDiffAt_rule
  (f : X → Y) (x : X)
  (hf : ContCDiffAt R f x) (hx : f x≠0)
  : ContCDiffAt R (fun x => ‖f x‖₂[R]) x := by fun_prop (disch:=assumption)



end InnerProductSpace


namespace SciLean
section OnFinVec


variable
  {K : Type _} [IsROrC K]
  {IX : Type} [IndexType IX] [LawfulIndexType IX] [DecidableEq IX] {X : Type _} [FinVec IX K X]
  {IY : Type} [IndexType IY] [LawfulIndexType IY] [DecidableEq IY] {Y : Type _} [FinVec IY K Y]
  {IZ : Type} [IndexType IZ] [LawfulIndexType IZ] [DecidableEq IZ] {Z : Type _} [FinVec IZ K Z]

@[fun_prop]
theorem Basis.proj.arg_x.ContCDiff_rule (i : IX)
  : ContCDiff K (fun x : X => ℼ i x) := by sorry_proof

@[fun_prop]
theorem Basis.proj.arg_x.ContCDiffAt_rule (i : IX) (x)
  : ContCDiffAt K (fun x : X => ℼ i x) x := by fun_prop

@[fun_prop]
theorem DualBasis.dualProj.arg_x.ContCDiff_rule (i : IX)
  : ContCDiff K (fun x : X => ℼ' i x) := by sorry_proof

@[fun_prop]
theorem DualBasis.dualProj.arg_x.ContCDiffAt_rule (i : IX) (x)
  : ContCDiffAt K (fun x : X => ℼ' i x) x := by fun_prop

@[fun_prop]
theorem BasisDuality.toDual.arg_x.ContCDiff_rule
  : ContCDiff K (fun x : X => BasisDuality.toDual x) := by sorry_proof

@[fun_prop]
theorem BasisDuality.toDual.arg_x.ContCDiffAt_rule (x)
  : ContCDiffAt K (fun x : X => BasisDuality.toDual x) x := by fun_prop

@[fun_prop]
theorem BasisDuality.fromDual.arg_x.ContCDiff_rule
  : ContCDiff K (fun x : X => BasisDuality.fromDual x) := by sorry_proof

@[fun_prop]
theorem BasisDuality.fromDual.arg_x.ContCDiffAt_rule (x)
  : ContCDiffAt K (fun x : X => BasisDuality.fromDual x) x := by fun_prop

end OnFinVec
end SciLean
