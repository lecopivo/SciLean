import SciLean.Analysis.Convenient.Vec
import SciLean.Analysis.Convenient.SemiInnerProductSpace
import SciLean.Analysis.Convenient.FinVec
import SciLean.Analysis.Scalar

set_option linter.unusedVariables false

namespace SciLean

set_option deprecated.oldSectionVars true

variable
  (K : Type _) [RCLike K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [IndexType ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]

/-- `CDifferentiableAt f x` - conveniently differentiable function `f` at point `x`. -/
@[irreducible, fun_prop]
def CDifferentiableAt (f : X → Y) (x : X) : Prop :=
  ∀ (c : K → X),
      c 0 = x
      →
      Curve.DifferentiableAt c 0
      →
      Curve.DifferentiableAt (f∘c) 0

/-- `CDifferentiable f` - conveniently differentiable function `f`.  -/
@[fun_prop]
def CDifferentiable (f : X → Y) : Prop := ∀ x, CDifferentiableAt K f x

variable (X)
@[fun_prop]
theorem CDifferentiableAt.id_rule (x : X)
  : CDifferentiableAt K (fun x : X => x) x
  := by sorry_proof

@[fun_prop]
theorem CDifferentiable.id_rule
  : CDifferentiable K (fun x : X => x)
  := by sorry_proof

@[fun_prop]
theorem CDifferentiableAt.const_rule (y : Y) (x : X)
  : CDifferentiableAt K (fun _ : X => y) x
  := by sorry_proof

@[fun_prop]
theorem CDifferentiable.const_rule (y : Y)
  : CDifferentiable K (fun _ : X => y)
  := by sorry_proof
variable {X}

@[fun_prop]
theorem CDifferentiableAt.comp_rule
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : CDifferentiableAt K f (g x)) (hg : CDifferentiableAt K g x)
  : CDifferentiableAt K (fun x => f (g x)) x
  := by sorry_proof

@[fun_prop]
theorem CDifferentiable.comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : CDifferentiable K f) (hg : CDifferentiable K g)
  : CDifferentiable K (fun x => f (g x))
  := by sorry_proof

variable (E)
@[fun_prop]
theorem CDifferentiableAt.apply_rule
  (i : ι) (x)
  : CDifferentiableAt K (fun x : (i : ι) → E i => x i) x :=
by sorry_proof

@[fun_prop]
theorem CDifferentiable.apply_rule (i : ι)
  : CDifferentiable K (fun x : (i : ι) → E i => x i) :=
by sorry_proof
variable {E}

@[fun_prop]
theorem CDifferentiableAt.pi_rule
  (f : X → (i : ι) → E i) (x : X)
  (hf : ∀ i, CDifferentiableAt K (f · i) x)
  : CDifferentiableAt K (fun x i => f x i) x
  := by sorry_proof

@[fun_prop]
theorem CDifferentiable.pi_rule
  (f : X → (i : ι) → E i)
  (hf : ∀ i, CDifferentiable K (f · i))
  : CDifferentiable K (fun x i => f x i)
  := by sorry_proof

@[fun_prop]
theorem CDifferentiableAt.cdifferentiable_rule (f : X → Y) (x : X) (hf : CDifferentiable K f) :
    CDifferentiableAt K f x := hf x


section NormedSpaces

variable
  {U} [NormedAddCommGroup U] [NormedSpace K U]
  {V} [NormedAddCommGroup V] [NormedSpace K V]

-- theorem Differentiable.cdifferentiable_rule (f : U → V) (hf : Differentiable K f) :
--     CDifferentiable K f := sorry_proof

-- theorem DifferentiableAt.cdifferentiableAt_rule (f : U → V) (x : U) (hf : DifferentiableAt K f x) :
--     CDifferentiableAt K f x := sorry_proof

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

@[fun_prop]
theorem Prod.mk.arg_fstsnd.CDifferentiableAt_rule
  (x : X)
  (g : X → Y) (hg : CDifferentiableAt K g x)
  (f : X → Z) (hf : CDifferentiableAt K f x)
  : CDifferentiableAt K (fun x => (g x, f x)) x
  := by sorry_proof

@[fun_prop]
theorem Prod.mk.arg_fstsnd.CDifferentiable_rule
  (g : X → Y) (hg : CDifferentiable K g)
  (f : X → Z) (hf : CDifferentiable K f)
  : CDifferentiable K (fun x => (g x, f x))
  := by intro x; fun_prop


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.fst.arg_self.CDifferentiable_rule
  (f : X → Y×Z) (hf : CDifferentiable K f)
  : CDifferentiable K (fun x => (f x).1)  := by sorry_proof

@[fun_prop]
theorem Prod.fst.arg_self.CDifferentiableAt_rule
  (x : X)
  (f : X → Y×Z) (hf : CDifferentiableAt K f x)
  : CDifferentiableAt K (fun x => (f x).1) x
  := by fun_prop


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.snd.arg_self.CDifferentiable_rule
  (f : X → Y×Z) (hf : CDifferentiable K f)
  : CDifferentiable K (fun x => (f x).2)  := by sorry_proof

@[fun_prop]
theorem Prod.snd.arg_self.CDifferentiableAt_rule
  (x : X)
  (f : X → Y×Z) (hf : CDifferentiableAt K f x)
  : CDifferentiableAt K (fun x => (f x).2) x
  := by fun_prop


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Neg.neg.arg_a0.CDifferentiable_rule
  (f : X → Y) (hf : CDifferentiable K f)
  : CDifferentiable K (fun x => - f x)  := by sorry_proof

@[fun_prop]
theorem Neg.neg.arg_a0.CDifferentiableAt_rule
  (x : X) (f : X → Y) (hf : CDifferentiableAt K f x)
  : CDifferentiableAt K (fun x => - f x) x
  := by fun_prop


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.CDifferentiable_rule
  (f g : X → Y) (hf : CDifferentiable K f) (hg : CDifferentiable K g)
  : CDifferentiable K (fun x => f x + g x)  := by sorry_proof

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.CDifferentiableAt_rule
  (x : X) (f g : X → Y) (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x)
  : CDifferentiableAt K (fun x => f x + g x) x
  := by fun_prop


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSub.hSub.arg_a0a1.CDifferentiable_rule
  (f g : X → Y) (hf : CDifferentiable K f) (hg : CDifferentiable K g)
  : CDifferentiable K (fun x => f x - g x)  := by sorry_proof

@[fun_prop]
theorem HSub.hSub.arg_a0a1.CDifferentiableAt_rule
  (x : X) (f g : X → Y) (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x)
  : CDifferentiableAt K (fun x => f x - g x) x
  := by fun_prop


-- HMul.hMul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def HMul.hMul.arg_a0a1.CDifferentiable_rule
  (f g : X → K) (hf : CDifferentiable K f) (hg : CDifferentiable K g)
  : CDifferentiable K (fun x => f x * g x)  := by sorry_proof

@[fun_prop]
def HMul.hMul.arg_a0a1.CDifferentiableAt_rule
  (x : X) (f g : X → K) (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x)
  : CDifferentiableAt K (fun x => f x * g x) x
  := by fun_prop


-- SMul.sMul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def HSMul.hSMul.arg_a0a1.CDifferentiable_rule
  (f : X → K) (g : X → Y) (hf : CDifferentiable K f) (hg : CDifferentiable K g)
  : CDifferentiable K (fun x => f x • g x)
  := by sorry_proof

@[fun_prop]
def HSMul.hSMul.arg_a0a1.CDifferentiableAt_rule
  (x : X) (f : X → K) (g : X → Y) (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x)
  : CDifferentiableAt K (fun x => f x • g x) x
  := by fun_prop

@[fun_prop]
theorem HSMul.hSMul.arg_a1.CDifferentiable_rule_nat
    (c : ℕ) (f : X → Y) (hf : CDifferentiable K f) : CDifferentiable K fun x => c • f x := by
  sorry_proof

@[fun_prop]
theorem HSMul.hSMul.arg_a1.CDifferentiableAt_rule_nat
    (c : ℕ) (f : X → Y) (x) (hf : CDifferentiableAt K f x) :
    CDifferentiableAt K (fun x => c • f x) x := by
  fun_prop

@[fun_prop]
theorem HSMul.hSMul.arg_a1.CDifferentiable_rule_int
    (c : ℤ) (f : X → Y) (hf : CDifferentiable K f) : CDifferentiable K fun x => c • f x := by
  sorry_proof

@[fun_prop]
theorem HSMul.hSMul.arg_a1.CDifferentiableAt_rule_int
    (c : ℤ) (f : X → Y) (x) (hf : CDifferentiableAt K f x) :
    CDifferentiableAt K (fun x => c • f x) x := by
  fun_prop


-- Inv.inv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def Inv.inv.arg_a0.CDifferentiableAt_rule (x : X) (f : X → K)
    (hf : CDifferentiableAt K f x) (hf' : f x ≠ 0) :
    CDifferentiableAt K (fun x => (f x)⁻¹) x := by
  sorry_proof

@[fun_prop]
def Inv.inv.arg_a0.CDifferentiable_rule (f : X → K)
    (hf : CDifferentiable K f) (hf' : ∀ x, f x ≠ 0) :
    CDifferentiable K (fun x => (f x)⁻¹) := by
  sorry_proof


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def HDiv.hDiv.arg_a0a1.CDifferentiableAt_rule
  (x : X) (f : X → K) (g : X → K)
  (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) (hx : g x ≠ 0)
  : CDifferentiableAt K (fun x => f x / g x) x
  := by sorry_proof

@[fun_prop]
def HDiv.hDiv.arg_a0a1.CDifferentiable_rule
  (f : X → K) (g : X → K)
  (hf : CDifferentiable K f) (hg : CDifferentiable K g) (hx : ∀ x, g x ≠ 0)
  : CDifferentiable K (fun x => f x / g x)
  := by intro x; fun_prop (disch:=apply hx)

@[fun_prop]
def HDiv.hDiv.arg_a0.CDifferentiable_rule
  (f : X → K) (r : K)
  (hf : CDifferentiable K f) (hr : r ≠ 0)
  : CDifferentiable K (fun x => f x / r) :=
by
  fun_prop (disch:=intros; assumption)

@[fun_prop]
def HDiv.hDiv.arg_a0.CDifferentiableAt_rule
  (x : X) (f : X → K) (r : K)
  (hf : CDifferentiableAt K f x) (hr : r ≠ 0)
  : CDifferentiableAt K (fun x => f x / r) x :=
by
  fun_prop (disch:=intros; assumption)



-- HPow.hPow -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def HPow.hPow.arg_a0.CDifferentiable_rule
  (f : X → K) (hf : CDifferentiable K f)
  : CDifferentiable K (fun x => f x ^ n)
  := by sorry_proof

@[fun_prop]
def HPow.hPow.arg_a0.CDifferentiableAt_rule
  (n : Nat) (x : X) (f : X → K) (hf : CDifferentiableAt K f x)
  : CDifferentiableAt K (fun x => f x ^ n) x
  := by fun_prop



-- sum ----------------------------------------------------------------
---------------------------------------------------------------------------------


@[fun_prop]
theorem sum.arg_f.CDifferentiableAt_rule
  (f : X → ι → Y) (x : X) (hf : ∀ i, CDifferentiableAt K (fun x => f x i) x)
  : CDifferentiableAt K (fun x => ∑ i, f x i) x :=
by
  sorry_proof


@[fun_prop]
theorem sum.arg_f.CDifferentiable_rule
  (f : X → ι → Y) (hf : ∀ i, CDifferentiable K (fun x => f x i))
  : CDifferentiable K (fun x => ∑ i, f x i) :=
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
theorem Inner.inner.arg_a0a1.CDifferentiable_rule
    (f : X → Y) (g : X → Y)
    (hf : CDifferentiable R f) (hg : CDifferentiable R g) :
    CDifferentiable R (fun x => ⟪f x, g x⟫[R]) := by sorry_proof

@[fun_prop]
theorem Inner.inner.arg_a0a1.CDifferentiableAt_rule
    (f : X → Y) (g : X → Y) (x : X)
    (hf : CDifferentiableAt R f x) (hg : CDifferentiableAt R g x) :
    CDifferentiableAt R (fun x => ⟪f x, g x⟫[R]) x := by fun_prop


@[fun_prop]
theorem Norm2.norm2.arg_a0.CDifferentiable_rule
  (f : X → Y) (hf : CDifferentiable R f)
  : CDifferentiable R (fun x => ‖f x‖₂²[R]) :=
by
  simp_rw[norm2_def]
  fun_prop


@[fun_prop]
theorem Norm2.norm2.arg_a0.CDifferentiableAt_rule
  (f : X → Y) (x : X) (hf : CDifferentiableAt R f x)
  : CDifferentiableAt R (fun x => ‖f x‖₂²[R]) x :=
by
  simp_rw[norm2_def]
  fun_prop


@[fun_prop]
theorem norm₂.arg_x.CDifferentiable_rule
  (f : X → Y) (hf : CDifferentiable R f) (hx : f x≠0)
  : CDifferentiable R (fun x => ‖f x‖₂[R]) := by sorry_proof

@[fun_prop]
theorem norm₂.arg_x.CDifferentiableAt_rule
  (f : X → Y) (x : X)
  (hf : CDifferentiableAt R f x) (hx : f x≠0)
  : CDifferentiableAt R (fun x => ‖f x‖₂[R]) x := by fun_prop (disch:=assumption)



end InnerProductSpace


-- section OnFinVec

-- variable
--   {K : Type _} [RCLike K]
--   {IX : Type _} [IndexType IX] [DecidableEq IX] {X : Type _} [FinVec IX K X]
--   {IY : Type _} [IndexType IY] [DecidableEq IY] {Y : Type _} [FinVec IY K Y]
--   {IZ : Type _} [IndexType IZ] [DecidableEq IZ] {Z : Type _} [FinVec IZ K Z]

-- @[fun_prop]
-- theorem Basis.proj.arg_x.CDifferentiable_rule (i : IX)
--   : CDifferentiable K (fun x : X => ℼ i x) := by sorry_proof

-- @[fun_prop]
-- theorem Basis.proj.arg_x.CDifferentiableAt_rule (i : IX) (x)
--   : CDifferentiableAt K (fun x : X => ℼ i x) x := by fun_prop

-- @[fun_prop]
-- theorem DualBasis.dualProj.arg_x.CDifferentiable_rule (i : IX)
--   : CDifferentiable K (fun x : X => ℼ' i x) := by sorry_proof

-- @[fun_prop]
-- theorem DualBasis.dualProj.arg_x.CDifferentiableAt_rule (i : IX) (x)
--   : CDifferentiableAt K (fun x : X => ℼ' i x) x := by fun_prop

-- @[fun_prop]
-- theorem BasisDuality.toDual.arg_x.CDifferentiable_rule
--   : CDifferentiable K (fun x : X => BasisDuality.toDual x) := by sorry_proof

-- @[fun_prop]
-- theorem BasisDuality.toDual.arg_x.CDifferentiableAt_rule (x)
--   : CDifferentiableAt K (fun x : X => BasisDuality.toDual x) x := by fun_prop

-- @[fun_prop]
-- theorem BasisDuality.fromDual.arg_x.CDifferentiable_rule
--   : CDifferentiable K (fun x : X => BasisDuality.fromDual x) := by sorry_proof

-- @[fun_prop]
-- theorem BasisDuality.fromDual.arg_x.CDifferentiableAt_rule (x)
--   : CDifferentiableAt K (fun x : X => BasisDuality.fromDual x) x := by fun_prop

-- end OnFinVec
-- end SciLean
