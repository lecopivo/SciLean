import SciLean.Analysis.AdjointSpace.Basic

import SciLean.Analysis.Normed.IsContinuousLinearMap
import SciLean.Analysis.Normed.Norm2

import SciLean.Tactic.FunTrans.Elab
import SciLean.Tactic.FunTrans.Attr

set_option linter.unusedVariables false

open RCLike

open scoped ComplexConjugate

set_option deprecated.oldSectionVars true

variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [AdjointSpace 𝕜 E] [AdjointSpace 𝕜 F] [AdjointSpace 𝕜 G]

set_default_scalar 𝕜

/-! ### Adjoint operator -/

open AdjointSpace SciLean

variable [CompleteSpace E] [CompleteSpace G] [CompleteSpace F]


variable (𝕜)
open Classical in
/-- The adjoint of a bounded operator from Hilbert space `E` to Hilbert space `F`. -/
@[fun_trans]
noncomputable
def adjoint (f : E → F) (y : F) : E :=
  if h : ∃ g : F → E, ∀ x y, ⟪f x, y⟫ = ⟪x, g y⟫ then
    choose h y
  else
    0
variable {𝕜}


postfix:1000 "†" => adjoint defaultScalar%


theorem adjoint_ex [CompleteSpace E] [CompleteSpace F] (A : E → F) (hA : IsContinuousLinearMap 𝕜 A) :
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


theorem adjoint.arg_y.IsLinearMap (A : E → F) : IsLinearMap 𝕜 (fun y => adjoint 𝕜 A y) := by
  constructor
  · sorry_proof
  · intros r x
    apply AdjointSpace.ext_inner_right 𝕜; intro v
    rw[AdjointSpace.inner_smul_left]
    if hA : IsContinuousLinearMap 𝕜 A then
      simp[adjoint_inner_left (hA:=hA)]
      rw[AdjointSpace.inner_smul_left]
    else
      sorry_proof


set_option linter.hashCommand false in
#generate_linear_map_simps adjoint.arg_y.IsLinearMap

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
  · intro h x y; rw[h,adjoint_inner_left _ hB]
  · intro h; funext u
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
  {ι : Type _} {n} [IndexType ι n] [Fold ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, AdjointSpace K (E i)] [∀ i, CompleteSpace (E i)]

set_default_scalar K

@[fun_trans]
theorem adjoint_id :
    (fun x : X => x)† = fun x => x := by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  intros; rfl


@[fun_trans]
theorem const_rule :
    (fun (x : X) => (0 : Y))† = fun x => 0 := by
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
  rw[inner_forall_split]
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
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  intro (y,z) x
  rw[AdjointSpace.inner_add_left]
  simp (disch:=fun_prop) [adjoint_inner_left]
  rfl

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
    (fun x' => ∑ᴵ i, ((f · i)†) (x' i)) := by

  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  intro x y
  sorry_proof
  -- rw[AdjointSpace.sum_inner]
  -- simp (disch:=fun_prop) [adjoint_inner_left]
  -- rfl


end adjoint


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


theorem SciLean.adjoint_wrt_prod
    {f : X → Y → Z} (hf : IsContinuousLinearMap K ↿f := by fun_prop) :
    adjoint K (fun xy : X×Y => f xy.1 xy.2)
    =
    fun (z : Z) =>
      let x := adjoint K (f · 0) z
      let y := adjoint K (f 0 ·) z
      (x,y) := sorry_proof


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
  simp (disch:=fun_prop) [adjoint_inner_left,inner_prod_split]

@[fun_trans]
theorem Prod.snd.arg_self.adjoint_rule
  (f : X → Y×Z) (hf : SciLean.IsContinuousLinearMap K f)
  : (fun x => (f x).2)†
    =
    fun z => (f†) (0,z) :=
by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  simp (disch:=fun_prop) [adjoint_inner_left,inner_prod_split]


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
  (y : Y) (f : X → K) (hf : IsContinuousLinearMap K f)
  : (fun x => f x • y)†
    =
    fun y' => ⟪y, y'⟫ • (f†) 1 :=
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
    fun y => (conj c) • (g†) y :=
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
    fun y => (conj c)⁻¹ • (f†) y :=
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
  : (fun x => Finset.sum A fun i => f x i)†
    =
    (fun y => Finset.sum A fun i => ((f · i)†) y) :=
by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  simp (disch:=fun_prop) [adjoint_inner_left,AdjointSpace.sum_inner,AdjointSpace.inner_sum]


-- @[fun_trans]
-- theorem sum.arg_f.adjoint_rule {ι} [IndexType ι]
--   (f : X → ι → Y) (hf : ∀ i, IsContinuousLinearMap K (f · i))
--   : (fun x => sum fun i => f x i)†
--     =
--     (fun y => sum fun i => ((f · i)†) y) :=
-- by
--   rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
--   sorry_proof

@[fun_trans]
theorem SciLean.IndexType.sum.arg_f.adjoint_rule {ι n} [IndexType ι n] [Fold ι]
  (f : X → ι → Y) (hf : ∀ i, IsContinuousLinearMap K (f · i))
  : (fun x => ∑ᴵ i, f x i)†
    =
    (fun y => ∑ᴵ i, ((f · i)†) y) :=
by
  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  sorry_proof
  -- simp (disch:=fun_prop) [adjoint_inner_left,AdjointSpace.sum_inner,AdjointSpace.inner_sum]


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
    [adjoint_inner_left,AdjointSpace.inner_smul_left,AdjointSpace.conj_symm,mul_comm]


section OnRealSpace

variable
  {R K : Type*} [RealScalar R] [Scalar R K] [ScalarSMul R K] [ScalarInner R K]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X] [AdjointSpace K X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace R Y] [AdjointSpace K Y] [CompleteSpace Y]
  -- maybe [IsScalarTower R K X] [IsScalarTower R K Y] ?
  -- This should be done properly with proofs to make sure it is correct
open SciLean

@[fun_trans]
theorem Inner.inner.arg_a1.adjoint_rule_real
  (f : X → Y) (hf : IsContinuousLinearMap R f) (y : Y)
  : adjoint R (fun x => ⟪y, f x⟫[K])
    =
    fun z => z • (adjoint R f) y :=
by
  rw[← (eq_adjoint_iff _ _ (by sorry_proof)).2]
  sorry_proof

open ComplexConjugate in
@[fun_trans]
theorem Inner.inner.arg_a0.adjoint_rule
  (f : X → Y) (hf : IsContinuousLinearMap R f) (y : Y)
  : adjoint R (fun x => ⟪f x, y⟫[K])
    =
    fun z => (conj z) • (adjoint R f) y :=
by
  rw[← (eq_adjoint_iff _ _ (by sorry_proof)).2]
  sorry_proof


end OnRealSpace



--------------------------------------------------------------------------------

section IsContinuousLinearMap

variable
  {R K : Type*} [RealScalar R] [Scalar R K] [ScalarSMul R K]
  {X : Type*} [TopologicalSpace X] [AddCommMonoid X] [Module R X] [Module K X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace R Y] [AdjointSpace K Y] [CompleteSpace Y]

-- set_default_scalar R

-- Inner -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Inner.inner.arg_a0.IsContinuousLinearMap_rule
  (f : X → Y) (hf : IsContinuousLinearMap R f) (y : Y)
  : IsContinuousLinearMap R fun x => ⟪f x, y⟫[K] :=
by
  constructor
  · constructor
    · intros
      rw[hf.linear.map_add]
      rw[AdjointSpace.inner_add_left]
    · intro c x
      rw[hf.linear.map_smul]
      calc _ = ⟪(c • (1:K)) • f x, y⟫[K] := by simp
           _ = (conj (c • (1:K))) * ⟪f x, y⟫[K] := by rw[AdjointSpace.inner_smul_left]
           _ = c • ⟪f x, y⟫[K] := by simp[ScalarSMul.smul_eq_mul_make]; sorry_proof
  · sorry_proof

@[fun_prop]
theorem Inner.inner.arg_a1.IsContinuousLinearMap_rule
  {K : Type*} [RCLike K]
  {X : Type*} [TopologicalSpace X] [AddCommMonoid X] [Module K X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace K Y]
  (f : X → Y) (hf : IsContinuousLinearMap K f) (y : Y)
  : IsContinuousLinearMap K fun x => ⟪y, f x⟫[K] :=
by
  constructor
  · constructor
    · intros
      rw[hf.linear.map_add]
      rw[AdjointSpace.inner_add_right]
    · intros
      rw[hf.linear.map_smul]
      simp only [AdjointSpace.inner_smul_right]
      rfl
  · sorry_proof


@[fun_prop]
theorem Inner.inner.arg_a1.IsContinuousLinearMap_rule_real
  (f : X → Y) (hf : IsContinuousLinearMap R f) (y : Y)
  : IsContinuousLinearMap R fun x => ⟪y, f x⟫[K] :=
by
  constructor
  · constructor
    · intros
      rw[hf.linear.map_add]
      rw[AdjointSpace.inner_add_right]
    · intro c x
      calc _ = ⟪y, (c • (1:K)) • f x⟫[K] := by simp[hf.linear.map_smul]
           _ = ((c • (1:K))) * ⟪y, f x⟫[K] := by rw[AdjointSpace.inner_smul_right]
           _ = c • ⟪y, f x⟫[K] := by simp[ScalarSMul.smul_eq_mul_make]
  · sorry_proof


end IsContinuousLinearMap
