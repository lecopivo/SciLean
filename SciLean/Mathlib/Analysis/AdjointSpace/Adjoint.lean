import SciLean.Mathlib.Analysis.AdjointSpace.Basic

import SciLean.Core.FunctionPropositions.IsContinuousLinearMap
import SciLean.Core.Objects.SemiInnerProductSpace

import SciLean.Tactic.FunTrans.Elab
import SciLean.Tactic.FunTrans.Attr

set_option linter.unusedVariables false

open RCLike

open scoped ComplexConjugate

variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [AdjointSpace 𝕜 E] [AdjointSpace 𝕜 F] [AdjointSpace 𝕜 G]

set_default_scalar 𝕜

/-! ### Adjoint operator -/

open AdjointSpace SciLean

variable [CompleteSpace E] [CompleteSpace G]


variable (𝕜)
open Classical in
/-- The adjoint of a bounded operator from Hilbert space `E` to Hilbert space `F`. -/
@[fun_trans]
noncomputable
def adjoint (f : E → F) : F → E :=
  if h : ∃ g : F → E, ∀ x y, ⟪f x, y⟫ = ⟪x, g y⟫ then
    choose h
  else
    0
variable {𝕜}


postfix:1000 "†" => adjoint defaultScalar%


theorem adjoint_ex (A : E → F) (hA : IsContinuousLinearMap 𝕜 A) :
    ∀ x y, ⟪A x, y⟫ = ⟪x, (A†) y⟫ := sorry_proof

theorem adjoint_clm {A : E → F} (hA : IsContinuousLinearMap 𝕜 A) : IsContinuousLinearMap 𝕜 (A†) :=
    sorry_proof


/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_left (A : E → F) (hA : IsContinuousLinearMap 𝕜 A) (x : E) (y : F) :
    ⟪(A†) y, x⟫ = ⟪y, A x⟫ := by
  rw[← AdjointSpace.conj_symm]
  rw[← adjoint_ex _ hA]
  rw[AdjointSpace.conj_symm]


/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_right (A : E → F) (hA : IsContinuousLinearMap 𝕜 A) (x : E) (y : F) :
    ⟪x, (A†) y⟫ = ⟪A x, y⟫ := by
  rw[← adjoint_ex _ hA]

/-- The adjoint is involutive. -/
@[simp]
theorem adjoint_adjoint (A : E → F) (hA : IsContinuousLinearMap 𝕜 A) : A†† = A := by
  funext u
  apply AdjointSpace.ext_inner_left 𝕜
  intro v
  rw[← adjoint_ex _ (adjoint_clm hA)]
  apply adjoint_inner_left _ hA


/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
theorem adjoint_comp (A : F → G) (B : E → F)
    (hA : IsContinuousLinearMap 𝕜 A) (hB : IsContinuousLinearMap 𝕜 B) :
    (A ∘ B)† = B† ∘ A† := by
  funext u
  apply AdjointSpace.ext_inner_left 𝕜
  intro v; dsimp
  rw[← adjoint_ex _ (by fun_prop), ← adjoint_ex _ hB,← adjoint_ex _ hA]
  rfl

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all `x` and `y`. -/
theorem eq_adjoint_iff (A : E → F) (B : F → E) (hB : IsContinuousLinearMap 𝕜 B) :
    A = B† ↔ ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫ := by
  constructor
  . intro h x y; rw[h,adjoint_inner_left _ hB]
  . intro h; funext u
    apply AdjointSpace.ext_inner_right 𝕜
    intro v
    rw[adjoint_inner_left _ hB]
    apply h u v



----------------------------------------------------------------------------------------------------

namespace adjoint


variable
  {K : Type _} [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [AdjointSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, AdjointSpace K (E i)] [∀ i, CompleteSpace (E i)]

set_default_scalar K

@[fun_trans]
theorem adjoint_id :
    (fun x : X => x)† = fun x => x := by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  intros; rfl


@[fun_trans]
theorem const_rule :
    (fun (x : X) =>L[K] (0 : Y))† = fun x =>L[K] 0 := by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  simp

@[fun_trans]
theorem proj_rule [DecidableEq ι]
    (i : ι) :
    (fun (f : (i' : ι) → E i') => f i)†
    =
    fun x => (fun j => if h : i=j then h ▸ x else 0) := by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  intro x y
  simp[Inner.inner]
  sorry_proof

@[fun_trans]
theorem prod_rule
    (f : X → Y) (g : X → Z)
    (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g) :
    (fun x => (f x, g x))†
    =
    fun yz =>
      let x₁ := (f†) yz.1
      let x₂ := (g†) yz.2
      x₁ + x₂ :=
by
  sorry_proof

@[fun_trans]
theorem comp_rule
    (f : Y → Z) (g : X → Y)
    (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g) :
    (fun x => f (g x))†
    =
    fun z =>
      let y := (f†) z
      let x := (g†) y
      x := by
  funext u
  apply AdjointSpace.ext_inner_left K
  intro v; dsimp
  rw[← adjoint_ex _ (by fun_prop), adjoint_ex _ hf,← adjoint_ex _ hg]


@[fun_trans]
theorem let_rule
    (f : X → Y → Z) (g : X → Y)
    (hf : IsContinuousLinearMap K (fun xy : X×Y => f xy.1 xy.2)) (hg : IsContinuousLinearMap K g) :
    (fun x => let y := g x; f x y)†
    =
    fun z =>
      let xy := ((fun (x,y) => f x y)†) z
      let x' := (g†) xy.2
      xy.1 + x' :=
by
  have h : (fun x => let y := g x; f x y)†
           =
           (fun x => (x, g x))† ∘ (fun (x,y) => f x y)†
         := comp_rule (K:=K) (f:=_) (g:=(fun x => (x, g x))) (hf:=hf) (hg:=by fun_prop)
  rw[h]
  fun_trans
  rfl


@[fun_trans]
theorem pi_rule
    (f : X → (i : ι) → E i) (hf : ∀ i, IsContinuousLinearMap K (f · i)) :
    (fun (x : X) (i : ι) => f x i)†
    =
    (fun x' => Finset.sum Finset.univ fun i => ((f · i)†) (x' i)) := by

  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  intro x y
  rw[AdjointSpace.sum_inner]
  simp (disch:=fun_prop) [adjoint_inner_left]
  rfl




--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

variable
  {K : Type _} [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [AdjointSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, AdjointSpace K (E i)] [∀ i, CompleteSpace (E i)]

open SciLean

set_default_scalar K


-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.fst.arg_self.adjoint_rule
  (f : X → Y×Z) (hf : SciLean.IsContinuousLinearMap K f)
  : (fun x => (f x).1)†
    =
    fun y => (f†) (y,0) :=
by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  simp (disch:=fun_prop) [adjoint_inner_left]
  sorry_proof -- todo some lemma about inner product on product spaces

@[fun_trans]
theorem Prod.snd.arg_self.adjoint_rule
  (f : X → Y×Z) (hf : SciLean.IsContinuousLinearMap K f)
  : (fun x => (f x).2)†
    =
    fun z => (f†) (0,z) :=
by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  simp (disch:=fun_prop) [adjoint_inner_left]
  sorry_proof -- todo some lemma about inner product on product spaces


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.adjoint_rule
    (f g : X → Y) (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g) :
    (fun x => f x + g x)†
    =
    fun y =>
      let x₁ := (f†) y
      let x₂ := (g†) y
      x₁ + x₂ := by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  simp (disch:=fun_prop) [adjoint_inner_left,AdjointSpace.inner_add_left,AdjointSpace.inner_add_right]



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSub.hSub.arg_a0a1.adjoint_rule
    (f g : X → Y) (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g) :
    (fun x => f x - g x)†
    =
    fun y =>
      let x₁ := (f†) y
      let x₂ := (g†) y
      x₁ - x₂ := by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  simp (disch:=fun_prop) [adjoint_inner_left,AdjointSpace.inner_sub_left,AdjointSpace.inner_sub_right]


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.adjoint_rule
  (f : X → Y) (hf : IsContinuousLinearMap K f)
  : (fun x => - f x)†
    =
    fun y => - (f†) y :=
by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  simp (disch:=fun_prop) [adjoint_inner_left,AdjointSpace.inner_neg_left,AdjointSpace.inner_neg_right]


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[fun_trans]
theorem HMul.hMul.arg_a0.adjoint_rule
  (c : K) (f : X → K) (hf : IsContinuousLinearMap K f)
  : (fun x => f x * c)†
    =
    fun y => conj c • (f†) y :=
by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  simp (disch:=fun_prop)
    [adjoint_inner_left,AdjointSpace.inner_smul_left,AdjointSpace.inner_smul_right]
  intros; ac_rfl

open ComplexConjugate in
@[fun_trans]
theorem HMul.hMul.arg_a1.adjoint_rule
  (c : K) (f : X → K) (hf : IsContinuousLinearMap K f)
  : (fun x => c * f x)†
    =
    fun y => conj c • (f†) y :=
by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  simp (disch:=fun_prop)
    [adjoint_inner_left,AdjointSpace.inner_smul_left,AdjointSpace.inner_smul_right]
  intros; ac_rfl


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[fun_trans]
theorem HSMul.hSMul.arg_a0.adjoint_rule
  (x' : X) (f : X → K) (hf : IsContinuousLinearMap K f)
  : (fun x => f x • x')†
    =
    fun y => ⟪x', y⟫ • ((fun x =>L[K] f x)†) 1 :=
by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  simp (disch:=fun_prop)
    [adjoint_inner_left,AdjointSpace.inner_smul_left,AdjointSpace.inner_smul_right]
  intros; ac_rfl

open ComplexConjugate in
@[fun_trans]
theorem HSMul.hSMul.arg_a1.adjoint_rule
  (c : K) (g : X → Y) (hg : IsContinuousLinearMap K g)
  : (fun x => c • g x)†
    =
    fun y => (conj c) • ((fun x =>L[K] g x)†) y :=
by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  simp (disch:=fun_prop)
    [adjoint_inner_left,AdjointSpace.inner_smul_left,AdjointSpace.inner_smul_right]


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[fun_trans]
theorem HDiv.hDiv.arg_a0.adjoint_rule
  (f : X → K) (c : K)
  (hf : IsContinuousLinearMap K f)
  : (fun x => f x / c)†
    =
    fun y => (conj c)⁻¹ • (fun x =>L[K] f x)† y :=
by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  simp (disch:=fun_prop)
    [adjoint_inner_left,AdjointSpace.inner_smul_left,AdjointSpace.inner_smul_right]
  simp [div_eq_mul_inv]
  intros; ac_rfl



-- Finset.sum ------------------------------------------------------------------
--------------------------------------------------------------------------------

open BigOperators in
@[fun_trans]
theorem Finset.sum.arg_f.adjoint_rule
  (f : X → ι → Y) (hf : ∀ i, IsContinuousLinearMap K (f · i)) (A : Finset ι)
  : (fun x => Finset.sum Finset.univ fun i => f x i)†
    =
    (fun y => Finset.sum Finset.univ fun i => ((f · i)†) y) :=
by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  simp (disch:=fun_prop) [adjoint_inner_left,AdjointSpace.sum_inner,AdjointSpace.inner_sum]


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem ite.arg_te.adjoint_rule
  (c : Prop) [dec : Decidable c]
  (t e : X → Y) (ht : IsContinuousLinearMap K t) (he : IsContinuousLinearMap K e)
  : (fun x => if c then t x else e x)†
    =
    fun y =>
      if c then (t†) y else (e†) y :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]

@[fun_trans]
theorem dite.arg_te.adjoint_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (ht : ∀ p, IsContinuousLinearMap K (t p))
  (e : ¬c → X → Y) (he : ∀ p, IsContinuousLinearMap K (e p))
  : (fun x => if h : c then t h x else e h x)†
    =
    fun y =>
      if h : c then ((t h ·)†) y else ((e h ·)†) y :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]



-- Inner -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Inner.inner.arg_a1.adjoint_rule
  (f : X → Y) (hf : IsContinuousLinearMap K f) (y : Y)
  : (fun x => ⟪y, f x⟫)†
    =
    fun z => z • (f†) y :=
by
  rw[← (eq_adjoint_iff _ _ (by sorry_proof)).2]
  simp (disch:=fun_prop)
    [adjoint_inner_left,AdjointSpace.inner_smul_left,AdjointSpace.conj_symm]


section OnRealSpace

variable
  {R : Type _} [RealScalar R]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]

open SciLean

set_default_scalar R

-- inner product is not ℂ-linear in its first argument thus it can't have an adjoint
open ComplexConjugate in
@[fun_trans]
theorem Inner.inner.arg_a0.adjoint_rule
  (f : X → Y) (hf : IsContinuousLinearMap R f) (y : Y)
  : (fun x => ⟪f x, y⟫)†
    =
    fun z => (conj z) • (f†) y :=
by
  rw[← (eq_adjoint_iff _ _ (by sorry_proof)).2]
  simp (disch:=fun_prop)
    [adjoint_inner_left,AdjointSpace.inner_smul_left,AdjointSpace.conj_symm]
  intros
  rw[← AdjointSpace.conj_symm]; simp


end OnRealSpace
