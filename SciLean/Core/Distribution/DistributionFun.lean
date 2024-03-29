import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Decomposition.Lebesgue
-- import Mathlib.LinearAlgebra.TensorProduct

import SciLean.Core.FunctionPropositions
import SciLean.Core.FunctionSpaces
import SciLean.Core.Integral.CIntegral
import SciLean.Core.Distribution.TestFunction
import SciLean.Core.Distribution.SimpAttr
import SciLean.Util.SorryProof
import SciLean.Util.Limit

open MeasureTheory ENNReal Classical

namespace SciLean

variable
  {R} [RealScalar R]
  {W} [Vec R W] [Module ℝ W]
  {X} [TopologicalSpace X] [space : TCOr (Vec R X) (DiscreteTopology X)]
  {Y} [Vec R Y] [Module ℝ Y]
  {Z} [Vec R Z]

set_default_scalar R

variable (R X Y)
structure DistributionFun where
  action : (𝒟 X) ⊸ Y
variable {R X Y}

namespace DistributionFun
scoped notation "⟪" f' ", " φ "⟫" => DistributionFun.action f' φ
end DistributionFun

open DistributionFun

notation "𝒟'" "(" X ", " Y ")" => DistributionFun defaultScalar% X Y

notation "𝒟'" X => DistributionFun defaultScalar% X defaultScalar%

@[app_unexpander DistributionFun] def unexpandDistributionFun : Lean.PrettyPrinter.Unexpander
  | `($(_) $_ $X $Y) => `(𝒟' ($X, $Y))
  | _ => throw ()

@[simp, ftrans_simp]
theorem action_mk_apply (f : (𝒟 X) ⊸ Y) (φ : 𝒟 X) :
    ⟪DistributionFun.mk (R:=R) f, φ⟫ = f φ := by rfl

@[ext]
theorem DistributionFun.ext (x y : DistributionFun R X Y) :
    (∀ (φ : 𝒟 X), ⟪x,φ⟫ = ⟪y,φ⟫)
    →
    x = y := by

  induction x; induction y; simp only [action_mk_apply, mk.injEq]; aesop


----------------------------------------------------------------------------------------------------
-- Algebra -----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance : Zero (𝒟'(X,Y)) := ⟨⟨fun _φ ⊸ 0⟩⟩
instance : Add (𝒟'(X,Y)) := ⟨fun f g => ⟨fun φ ⊸ ⟪f, φ⟫ + ⟪g, φ⟫⟩⟩
instance : Sub (𝒟'(X,Y)) := ⟨fun f g => ⟨fun φ ⊸ ⟪f, φ⟫ - ⟪g, φ⟫⟩⟩
instance : Neg (𝒟'(X,Y)) := ⟨fun f => ⟨fun φ ⊸ -⟪f, φ⟫⟩⟩
instance : SMul R (𝒟'(X,Y)) := ⟨fun r f => ⟨fun φ ⊸ r • ⟪f, φ⟫⟩⟩

-- not sure what exact the topology is supposed to be here
instance : UniformSpace (𝒟'(X,Y)) := sorry
instance : Vec R (𝒟'(X,Y)) := Vec.mkSorryProofs


----------------------------------------------------------------------------------------------------
-- Extended action ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open Notation in
@[pp_dot]
noncomputable
def DistributionFun.extAction (T : 𝒟'(X,Y)) (φ : X → R) : Y := limit n → ∞, ⟪T, testFunApprox n φ⟫

@[pp_dot]
noncomputable
def DistributionFun.extAction' (T : 𝒟'(X,Y)) (φ : X → Z) (L : Y → Z → W) : W := sorry -- limit n → ∞, ⟪T, testFunApprox n φ⟫
  -- write φ as ∑ i, φᵢ • zᵢ
  -- and ⟪T, φ⟫[L] = ∑ i, L ⟪T, φᵢ⟫ zᵢ

-- Lean usually fails to unify this theorem, thus we have a custom simproc to apply it
theorem DistributionFun.mk_extAction (T : (X → R) → Y) (hT : IsSmoothLinearMap R (fun φ : 𝒟 X => T φ)) (φ : X → R) :
   (DistributionFun.mk (⟨fun φ => T φ,hT⟩)).extAction φ = T φ := sorry_proof


-- #check Function.
-- theorem DistributionFun.mk_restrict (T : (X → R) → R) (hT : IsSmoothLinearMap R (fun φ : 𝒟 X => T φ)) (φ : X → R) (A : Set X) :
--    ((DistributionFun.mk (⟨fun φ => T φ,hT⟩)).restrict A).extAction φ = T φ  := sorry_proof


open Lean Meta in
/-- Simproc to apply `DistributionFun.mk_extAction` theorem -/
simproc_decl DistributionFun.mk_extAction_simproc (DistributionFun.extAction (DistributionFun.mk (SmoothLinearMap.mk _ _)) _) := fun e => do

  let φ := e.appArg!
  let T := e.appFn!.appArg!

  let .lam xName xType xBody xBi := T.appArg!.appFn!.appArg!
    | return .continue
  let hT := T.appArg!.appArg!

  withLocalDecl xName xBi xType fun x => do
  let R := xType.getArg! 0
  let X := xType.getArg! 2
  withLocalDecl `φ' xBi (← mkArrow X R) fun φ' => do
    let b := xBody.instantiate1 x
    let b := b.replace (fun e' =>
      if e'.isAppOf ``DFunLike.coe &&
         5 ≤ e'.getAppNumArgs &&
         e'.getArg! 4 == x then
          .some (mkAppN φ' e'.getAppArgs[5:])
      else
        .none)

    if b.containsFVar x.fvarId! then
      return .continue

    let T ← mkLambdaFVars #[φ'] b
    let prf ← mkAppM ``DistributionFun.mk_extAction #[T, hT, φ]
    return .visit {expr := T.beta #[φ], proof? := prf}


----------------------------------------------------------------------------------------------------
-- Post Composition --------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

noncomputable
def DistributionFun.postComp (T : 𝒟'(X,Y)) (f : Y → Z) : 𝒟'(X,Z) :=
  if h : IsSmoothLinearMap R f then
    ⟨fun φ ⊸ f ⟪T,φ⟫⟩
  else
    0

noncomputable
abbrev DistributionFun.postExtAction (T : 𝒟'(X,𝒟'(Y,Z))) (φ : Y → R) : 𝒟'(X,Z) :=
  T.postComp (fun u => u.extAction φ)


----------------------------------------------------------------------------------------------------
-- Monadic structure -------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- def dirac (x : X) : DistributionFun X := fun φ => φ x

-- instance : Monad (DistributionFun R) where
--   pure := fun x => ⟨fun φ => φ x⟩
--   bind := fun x f => ⟨fun φ => ⟪x, fun x' => ⟪(f x'), φ⟫⟫⟩

-- instance : LawfulMonad (DistributionFun R) where
--   bind_pure_comp := by intros; rfl
--   bind_map       := by intros; rfl
--   pure_bind      := by intros; rfl
--   bind_assoc     := by intros; rfl
--   map_const      := by intros; rfl
--   id_map         := by intros; rfl
--   seqLeft_eq     := by intros; rfl
--   seqRight_eq    := by intros; rfl
--   pure_seq       := by intros; rfl

def vecDirac (x : X) (y : Y) : 𝒟'(X,Y) := ⟨fun φ ⊸ φ x • y⟩

open Notation
noncomputable
def DistributionFun.bind (x' : 𝒟'(X,Z)) (f : X → 𝒟'(Y,R)) : 𝒟'(Y,Z) :=
  limit (n : ℕ) → ∞, ⟨⟨fun φ => ⟪x', testFunApprox n fun x => ⟪f x, φ⟫⟫, sorry_proof⟩⟩


----------------------------------------------------------------------------------------------------
-- Basic identities --------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[simp, ftrans_simp]
theorem action_vecDirac (x : X) (y : Y) (φ : 𝒟 X) : ⟪((vecDirac x y) : 𝒟'(X,Y)), φ⟫ = φ x • y := by rfl

@[simp, ftrans_simp]
theorem action_bind (x : 𝒟'(X,Z)) (f : X → 𝒟'(Y,R)) (φ : 𝒟 Y) :
    ⟪x.bind f, φ⟫ = x.extAction (fun x' => ⟪f x', φ⟫) := by
  simp[DistributionFun.bind]
  sorry_proof


----------------------------------------------------------------------------------------------------
-- Arithmetics -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[simp, ftrans_simp, action_push]
theorem DistributionFun.zero_action (φ : 𝒟 X) : ⟪(0 : 𝒟'(X,Y)), φ⟫ = 0 := by rfl

@[action_push]
theorem DistributionFun.add_action (T T' : 𝒟'(X,Y)) (φ : 𝒟 X) : ⟪T + T', φ⟫ = ⟪T,φ⟫ + ⟪T',φ⟫ := by rfl

@[action_push]
theorem DistributionFun.sub_action (T T' : 𝒟'(X,Y)) (φ : 𝒟 X) : ⟪T - T', φ⟫ = ⟪T,φ⟫ - ⟪T',φ⟫ := by rfl

@[action_push]
theorem DistributionFun.smul_action (r : R) (T : 𝒟'(X,Y)) (φ : 𝒟 X) : ⟪r • T, φ⟫ = r • ⟪T,φ⟫ := by rfl

@[action_push]
theorem DistributionFun.neg_action (T : 𝒟'(X,Y)) (φ : 𝒟 X) : ⟪- T, φ⟫ = - ⟪T,φ⟫ := by rfl

open BigOperators in
@[action_push]
theorem DistributionFun.fintype_sum_action {I} [Fintype I] (T : I → 𝒟'(X,Y)) (φ : 𝒟 X) :
    ⟪∑ i, T i, φ⟫ = ∑ i, ⟪T i, φ⟫ := by sorry_proof

@[action_push]
theorem DistributionFun.indextype_sum_action {I} [IndexType I] (T : I → 𝒟'(X,Y)) (φ : 𝒟 X) :
    ⟪∑ i, T i, φ⟫ = ∑ i, ⟪T i, φ⟫ := by sorry_proof

@[simp, ftrans_simp, action_push]
theorem DistributionFun.zero_extAction (φ : X → R) : (0 : 𝒟'(X,Y)).extAction φ = 0 := by sorry_proof

-- todo: this needs some integrability condition
@[action_push]
theorem DistributionFun.add_extAction (T T' : 𝒟'(X,Y)) (φ : X → R) :
    (T + T').extAction φ = T.extAction φ + T'.extAction φ := by sorry_proof

@[action_push]
theorem DistributionFun.sub_extAction (T T' : 𝒟'(X,Y)) (φ : X → R) :
    (T - T').extAction φ = T.extAction φ - T'.extAction φ := by sorry_proof

@[action_push]
theorem DistributionFun.smul_extAction (r : R) (T : 𝒟'(X,Y)) (φ : X → R) :
    (r • T).extAction φ = r • T.extAction φ := by sorry_proof

@[action_push]
theorem DistributionFun.neg_extAction (T : 𝒟'(X,Y)) (φ : X → R) :
    (- T).extAction φ = - T.extAction φ := by sorry_proof

open BigOperators in
@[action_push]
theorem DistributionFun.fintype_sum_extAction {I} [Fintype I] (T : I → 𝒟'(X,Y)) (φ : X → R) :
    (∑ i, T i).extAction φ = ∑ i, (T i).extAction φ := by sorry_proof

@[action_push]
theorem DistributionFun.indextype_sum_extAction {I} [IndexType I] (T : I → 𝒟'(X,Y)) (φ : X → R) :
    (∑ i, T i).extAction φ = ∑ i, (T i).extAction φ := by sorry_proof


----------------------------------------------------------------------------------------------------
-- DistributionFunal if statement ---------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable [MeasureSpace X]

open Classical Notation in
noncomputable
def iteD (A : Set X) (t e : 𝒟'(X,Y)) : 𝒟'(X,Y) :=
  ⟨⟨fun φ =>
    t.extAction (fun x => if x ∈ A then φ x else 0) +
    e.extAction (fun x => if x ∈ A then 0 else φ x), sorry_proof⟩⟩

open Lean.Parser Term in
syntax withPosition("ifD " term " then "
    ppDedent(ppLine ppSpace ppSpace) term ppDedent(ppLine)
  "else"
    ppDedent(ppLine ppSpace ppSpace) term) : term

macro_rules
  | `(ifD $A then $t else $e) => `(iteD $A $t $e)

open Lean Parser in
@[app_unexpander iteD]
def unexpandIteD : Lean.PrettyPrinter.Unexpander
  | `($(_) $A $t $e) => `(ifD $A then $t else $e)
  | _ => throw ()

@[action_push]
theorem DistributionFun.action_iteD (A : Set X) (t e : 𝒟'(X,Y)) (φ : 𝒟 X) :
    ⟪iteD A t e, φ⟫ =
        t.extAction (fun x => if x ∈ A then φ x else 0) +
        e.extAction (fun x => if x ∉ A then φ x else 0) := by sorry_proof

@[action_push]
theorem DistributionFun.extAction_iteD (A : Set X) (t e : 𝒟'(X,Y)) (φ : X → R) :
    (iteD A t e).extAction φ =
        t.extAction (fun x => if x ∈ A then φ x else 0) +
        e.extAction (fun x => if x ∉ A then φ x else 0) := by sorry_proof


----------------------------------------------------------------------------------------------------
-- Set restriction ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[pp_dot]
noncomputable
def DistributionFun.restrict (T : 𝒟'(X,Y)) (A : Set X) : 𝒟'(X,Y) :=
  ifD A then T else 0

@[simp,ftrans_simp]
theorem restrict_univ (T : 𝒟'(X,Y))  :
    T.restrict Set.univ = T := sorry_proof

@[simp,ftrans_simp]
theorem zero_restrict (A : Set X) :
    (0 : 𝒟'(X,Y)).restrict A = 0 := sorry_proof

@[simp,ftrans_simp]
theorem add_restrict (T S : 𝒟'(X,Y)) (A : Set X) :
    (T + S).restrict A = T.restrict A + S.restrict A := sorry_proof

@[simp,ftrans_simp]
theorem sub_restrict (T S : 𝒟'(X,Y)) (A : Set X) :
    (T - S).restrict A = T.restrict A - S.restrict A := sorry_proof

@[simp,ftrans_simp]
theorem smul_restrict (r : R) (T : 𝒟'(X,Y)) (A : Set X) :
    (r • T).restrict A = r • (T.restrict A) := sorry_proof

@[simp,ftrans_simp]
theorem neg_restrict (T : 𝒟'(X,Y)) (A : Set X) :
    (- T).restrict A = - (T.restrict A) := sorry_proof

open BigOperators in
@[simp,ftrans_simp]
theorem finset_sum_restrict {I} [Fintype I] (T : I → 𝒟'(X,Y)) (A : Set X) :
    (∑ i, T i).restrict A = ∑ i, (T i).restrict A := sorry_proof

@[simp,ftrans_simp]
theorem indextype_sum_restrict {I} [IndexType I] (T : I → 𝒟'(X,Y)) (A : Set X) :
    (∑ i, T i).restrict A = ∑ i, (T i).restrict A := sorry_proof

@[simp,ftrans_simp]
theorem iteD_restrict (T : 𝒟'(X,Y)) (A : Set X) :
    (ifD A then T else 0) = T.restrict A := by rfl

@[simp,ftrans_simp]
theorem iteD_restrict' (T : 𝒟'(X,Y)) (A : Set X) :
    (ifD A then 0 else T) = T.restrict Aᶜ := sorry_proof


----------------------------------------------------------------------------------------------------
-- DistributionFuna product  --------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable {X₁} [Vec R X₁] {X₂} [Vec R X₂]

noncomputable
def DistributionFun.prod' (p : X₁ → X₂ → X) (T : 𝒟'(X₁,Y)) (S : X₁ → 𝒟'(X₂,R)) : 𝒟'(X,Y) :=
  ⟨⟨fun φ => T.extAction (fun x₁ => (S x₁).extAction fun x₂ => φ (p x₁ x₂)), sorry_proof⟩⟩

noncomputable
abbrev DistributionFun.prod (T : 𝒟'(X₁,Y)) (S : 𝒟'(X₂,R)) : 𝒟' (X₁×X₂) := prod' Prod.mk T (fun _ => S)

@[simp, ftrans_simp]
theorem DistributionFun.prod'_restrict (p : X₁ → X₂ → X) (T : 𝒟' X₁) (S : X₁ → 𝒟' X₂) (A : Set X) :
    (prod' p T S).restrict A = prod' p (T.restrict (A.preimage1 p)) (fun x₁ => (S x₁).restrict (p x₁ ⁻¹' A)) := sorry_proof

@[action_push]
theorem DistributionFun.prod'_extAction (p : X₁ → X₂ → X) (T : 𝒟' X₁) (S : X₁ → 𝒟' X₂) (φ : X → R) :
    (prod' p T S).extAction φ = T.extAction (fun x₁ => (S x₁).extAction fun x₂ => φ (p x₁ x₂)) := sorry_proof


----------------------------------------------------------------------------------------------------
-- Functions as DistributionFuns ----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[coe]
noncomputable
def _root_.Function.toDistributionFun (f : X → Y) : 𝒟'(X,Y) :=
  ⟨fun φ ⊸ ∫' x, φ x • f x⟩

def DistributionFun.IsFunction (T : 𝒟'(X,Y)) : Prop :=
  ∃ (f : X → Y), ∀ (φ : 𝒟 X),
      ⟪T, φ⟫ = ∫' x, φ x • f x

noncomputable
def DistributionFun.toFunction (T : 𝒟'(X,Y)) : X → Y :=
  if h : T.IsFunction then
    choose h
  else
    0

@[action_push]
theorem Function.toDistributionFun_action (f : X → Y) (φ : 𝒟 X) :
    ⟪f.toDistributionFun, φ⟫ = ∫' x, φ x • f x := by rfl

@[action_push]
theorem Function.toDistributionFun_extAction (f : X → Y) (φ : X → R) :
    f.toDistributionFun.extAction φ
    =
    ∫' x, φ x • f x := sorry_proof

@[simp, ftrans_simp]
theorem Function.toDistributionFun_zero  :
    Function.toDistributionFun (fun (_ : X) => 0) = (0 : 𝒟'(X,Y)) := by sorry_proof


----------------------------------------------------------------------------------------------------
-- Measures as DistributionFuns -----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- open Classical in
variable [MeasurableSpace X]
@[coe]
noncomputable
def _root_.MeasureTheory.Measure.toDistributionFun
    (μ : Measure X) : 𝒟'(X,R) :=
  ⟨fun φ ⊸ ∫' x, φ x ∂μ⟩

noncomputable
instance : Coe (Measure X) (𝒟'(X,R)) := ⟨fun μ => μ.toDistributionFun⟩

def DistributionFun.IsMeasure (f : 𝒟'(X,R)) : Prop :=
  ∃ (μ : Measure X), ∀ (φ : 𝒟 X),
      ⟪f, φ⟫ = ∫' x, φ x ∂μ

open Classical
noncomputable
def DistributionFun.toMeasure (f' : 𝒟'(X,R)) : Measure X :=
  if h : f'.IsMeasure then
    choose h
  else
    0

-- @[simp]
-- theorem apply_measure_as_DistributionFun  {X} [MeasurableSpace X]  (μ : Measure X) (φ : X → Y) :
--      ⟪μ.toDistributionFun, φ⟫ = ∫ x, φ x ∂μ := by rfl

/- under what conditions is this true??? -/
-- theorem action_is_integral  {X} [MeasurableSpace X] {Y} [MeasurableSpace Y]
--     (x : Measure X) (f : X → Measure Y)
--     (φ : Y → Z) (hφ : ∀ x, Integrable φ (f x)) :
--     ⟪x.toDistributionFun >>= (fun x => (f x).toDistributionFun), φ⟫
--     =
--     ∫ y, φ y ∂(@Measure.bind _ _ _ _ x f) := by
--   sorry_proof

-- def DistributionFun.densitvy {X} [MeasurableSpace X] (x y : 𝒟' X) : X → ℝ≥0∞ :=
--   x.toMeasure.rnDeriv y.toMeasure
