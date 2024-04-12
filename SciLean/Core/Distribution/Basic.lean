import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Constructions.Prod.Basic

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
  {X} [Vec R X] -- [TopologicalSpace X] [space : TCOr (Vec R X) (DiscreteTopology X)]
  {Y} [Vec R Y] [Module ℝ Y]
  {Z} [Vec R Z]
  {U} [Vec R U]
  {V} [Vec R V]

set_default_scalar R

variable (R X Y)
abbrev Distribution := (𝒟 X) ⊸[R] Y
variable {R X Y}


notation "𝒟'" X => Distribution defaultScalar% X defaultScalar%
notation "𝒟'" "(" X ", " Y ")" => Distribution defaultScalar% X Y

@[app_unexpander Distribution] def unexpandDistribution : Lean.PrettyPrinter.Unexpander
  | `($(_) $_ $X $Y) => `(𝒟'($X,$Y))
  | _ => throw ()


@[ext]
theorem Distribution.ext (x y : 𝒟'(X,Y)) :
    (∀ (φ : 𝒟 X), x φ = y φ)
    →
    x = y := by

  apply SmoothLinearMap.ext


----------------------------------------------------------------------------------------------------
-- Algebra -----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- instance : Zero (𝒟'(X,Y)) := by unfold Distribution; infer_instance
-- instance : Add (𝒟'(X,Y)) := by unfold Distribution; infer_instance
-- instance : Sub (𝒟'(X,Y)) := by unfold Distribution; infer_instance
-- instance : Neg (𝒟'(X,Y)) := by unfold Distribution; infer_instance
-- instance : SMul R (𝒟'(X,Y)) := by unfold Distribution; infer_instance
instance [Module ℝ Y] : SMul ℝ (𝒟'(X,Y)) := ⟨fun r f => ⟨fun φ => r • (f φ), sorry_proof⟩⟩

-- instance : UniformSpace (𝒟'(X,Y)) :=  by unfold Distribution; infer_instance
-- instance : Vec R (𝒟'(X,Y)) := by unfold Distribution; infer_instance
instance [Module ℝ Y] : Module ℝ (𝒟'(X,Y)) := Module.mkSorryProofs


----------------------------------------------------------------------------------------------------
-- Extended action ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open BigOperators in
@[pp_dot]
noncomputable
def Distribution.extAction (T : 𝒟'(X,Y)) (φ : X → Z) (L : Y ⊸ Z ⊸ W) : W :=
  if h : ∃ (zₙ : ℕ → Z) (φₙ : ℕ → 𝒟 X), ∀ x, ∑' i, φₙ i x • zₙ i = φ x then
    let zₙ := Classical.choose h
    let φₙ := (Classical.choose_spec h).choose
    ∑' i, L (T (φₙ i)) (zₙ i)
  else
    0

namespace Distribution
scoped notation "⟪" T ", " φ "⟫[" L "]" => Distribution.extAction T φ L
end Distribution


noncomputable
abbrev Distribution.extAction' (T : 𝒟'(X,Y)) (φ : X → R) : Y := T.extAction φ (fun y ⊸ fun r ⊸ r • y)

noncomputable
abbrev Distribution.integrate (T : 𝒟'(X,Y)) : Y := T.extAction' (fun _ => 1)

@[fun_prop]
theorem TestFunction.apply_IsSmoothLinearMap : IsSmoothLinearMap R fun (φ : 𝒟 X) => (φ : X → R) := sorry_proof

theorem Distribution.mk_extAction (T : (X → R) → Y) (hT : IsSmoothLinearMap R (fun φ : 𝒟 X => T φ)) (φ : X → R) :
    Distribution.extAction (SmoothLinearMap.mk' R (fun (φ : 𝒟 X) => T φ) hT : Distribution _ _ _) φ (fun y ⊸ fun r ⊸ r • y) = T φ := sorry_proof


-- This is definitely not true as stated, what kind of condistions do we need on `φ` and `T`?
@[fun_prop]
theorem Distribution.extAction.arg_φ.IsSmoothLinearMap (T : 𝒟'(X,U)) (φ : W → X → V) (L : U ⊸ V ⊸ Z)
    (hφ : IsSmoothLinearMap R φ) :
    IsSmoothLinearMap R (fun w => T.extAction (φ w) L) := sorry_proof

@[fun_prop]
theorem Distribution.extAction.arg_T.IsSmoothLinearMap (T : W → 𝒟'(X,U)) (φ : X → V) (L : U ⊸ V ⊸ Z)
    (hT : IsSmoothLinearMap R T) :
    IsSmoothLinearMap R (fun w => (T w).extAction φ L) := sorry_proof


-- open Lean Meta in
-- /-- Simproc to apply `Distribution.mk_extAction` theorem -/
-- simproc_decl Distribution.mk_extAction_simproc (Distribution.extAction (Distribution.mk (SmoothLinearMap.mk _ _)) _) := fun e => do

--   let φ := e.appArg!
--   let T := e.appFn!.appArg!

--   let .lam xName xType xBody xBi := T.appArg!.appFn!.appArg!
--     | return .continue
--   let hT := T.appArg!.appArg!

--   withLocalDecl xName xBi xType fun x => do
--   let R := xType.getArg! 0
--   let X := xType.getArg! 2
--   withLocalDecl `φ' xBi (← mkArrow X R) fun φ' => do
--     let b := xBody.instantiate1 x
--     let b := b.replace (fun e' =>
--       if e'.isAppOf ``DFunLike.coe &&
--          5 ≤ e'.getAppNumArgs &&
--          e'.getArg! 4 == x then
--           .some (mkAppN φ' e'.getAppArgs[5:])
--       else
--         .none)

--     if b.containsFVar x.fvarId! then
--       return .continue

--     let T ← mkLambdaFVars #[φ'] b
--     let prf ← mkAppM ``Distribution.mk_extAction #[T, hT, φ]
--     return .visit {expr := T.beta #[φ], proof? := prf}



----------------------------------------------------------------------------------------------------
-- Monadic structure -------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- def dirac (x : X) : Distribution X := fun φ => φ x

-- instance : Monad (Distribution R) where
--   pure := fun x => ⟨fun φ => φ x⟩
--   bind := fun x f => ⟨fun φ => ⟪x, fun x' => ⟪(f x'), φ⟫⟫⟩

-- instance : LawfulMonad (Distribution R) where
--   bind_pure_comp := by intros; rfl
--   bind_map       := by intros; rfl
--   pure_bind      := by intros; rfl
--   bind_assoc     := by intros; rfl
--   map_const      := by intros; rfl
--   id_map         := by intros; rfl
--   seqLeft_eq     := by intros; rfl
--   seqRight_eq    := by intros; rfl
--   pure_seq       := by intros; rfl

def dirac (x : X) : 𝒟' X := fun φ ⊸ φ x

open Notation
noncomputable
def Distribution.bind (x' : 𝒟'(X,U)) (f : X → 𝒟'(Y,V)) (L : U ⊸ V ⊸ W) : 𝒟'(Y,W) :=
  fun φ ⊸ x'.extAction (fun x => (f x).extAction φ (fun v ⊸ fun r ⊸ r • v)) L


----------------------------------------------------------------------------------------------------
-- Basic identities --------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[simp, ftrans_simp]
theorem action_dirac (x : X) (φ : 𝒟 X) : dirac x φ = φ x := by simp[dirac]

@[simp, ftrans_simp]
theorem action_bind (x : 𝒟'(X,U)) (f : X → 𝒟'(Y,V)) (L : U ⊸ V ⊸ W) (φ : 𝒟 Y) :
    x.bind f L φ = x.extAction (fun x' => (f x').extAction' φ) L := by
  simp[Distribution.bind]


-- @[simp, ftrans_simp]
-- theorem extAction_bind (x : 𝒟'(X,U)) (f : X → 𝒟'(Y,V)) (L : U ⊸ V ⊸ W) (φ : Y → Z) (K : W ⊸ Z ⊸ W') :
--     (x.bind f L).extAction φ K = x.extAction (fun x' => (f x').extAction φ (sorry : V ⊸ Z ⊸ V⊗Z)) (sorry : U ⊸ (V⊗Z) ⊸ W') := by
--   simp [Distribution.bind]


----------------------------------------------------------------------------------------------------
-- Arithmetics -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section Arithmetics

@[simp, ftrans_simp, action_push]
theorem Distribution.zero_extAction (φ : X → V) (L : U ⊸ V ⊸ W) : (0 : 𝒟'(X,U)).extAction φ L = 0 := by
  unfold extAction; simp


-- todo: this needs some integrability condition
@[action_push]
theorem Distribution.add_extAction (T T' : 𝒟'(X,U)) (φ : X → V) (L : U ⊸ V ⊸ W) :
    ((T + T') : 𝒟'(X,U)).extAction φ L = T.extAction φ L + T'.extAction φ L := by sorry_proof

@[action_push]
theorem Distribution.sub_extAction (T T' : 𝒟'(X,U)) (φ : X → V) (L : U ⊸ V ⊸ W) :
    (T - T').extAction φ L = T.extAction φ L - T'.extAction φ L := by sorry_proof

@[action_push]
theorem Distribution.smul_extAction (r : R) (T : 𝒟'(X,U)) (φ : X → V) (L : U ⊸ V ⊸ W)  :
    (r • T).extAction φ L = r • T.extAction φ L := by sorry_proof

@[action_push]
theorem Distribution.neg_extAction (T : 𝒟'(X,U)) (φ : X → V) (L : U ⊸ V ⊸ W) :
    (- T).extAction φ L = - T.extAction φ L := by sorry_proof

open BigOperators in
@[action_push]
theorem Distribution.fintype_sum_extAction {I} [Fintype I] (T : I → 𝒟'(X,U)) (φ : X → V) (L : U ⊸ V ⊸ W) :
    (∑ i, T i).extAction φ L = ∑ i, (T i).extAction φ L := by sorry_proof

@[action_push]
theorem Distribution.indextype_sum_extAction {I} [IndexType I] (T : I → 𝒟'(X,U)) (φ : X → V) (L : U ⊸ V ⊸ W) :
    (∑ i, T i).extAction φ L = ∑ i, (T i).extAction φ L := by sorry_proof

end Arithmetics


----------------------------------------------------------------------------------------------------
-- Distributional if statement ---------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable [MeasureSpace X]

open Classical Notation in
noncomputable
def iteD (A : Set X) (t e : 𝒟'(X,Y)) : 𝒟'(X,Y) :=
  fun φ ⊸
    t.extAction (fun x => if x ∈ A then φ x else 0) (fun y ⊸ fun r ⊸ r • y) +
    e.extAction (fun x => if x ∈ A then 0 else φ x) (fun y ⊸ fun r ⊸ r • y)

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
theorem Distribution.action_iteD (A : Set X) (t e : 𝒟'(X,Y)) (φ : 𝒟 X) :
   iteD A t e φ =
        t.extAction (fun x => if x ∈ A then φ x else 0) (fun y ⊸ fun r ⊸ r • y) +
        e.extAction (fun x => if x ∉ A then φ x else 0) (fun y ⊸ fun r ⊸ r • y) := by sorry_proof

@[simp, ftrans_simp]
theorem Distribution.iteD_same (A : Set X) (u : 𝒟'(X,Y)) :
   iteD A u u = u := by sorry_proof

@[action_push]
theorem Distribution.extAction_iteD (A : Set X) (t e : 𝒟'(X,U)) (φ : X → V) (L : U ⊸ V ⊸ W) :
    (iteD A t e).extAction φ L =
        t.extAction (fun x => if x ∈ A then φ x else 0) L +
        e.extAction (fun x => if x ∉ A then φ x else 0) L := by sorry_proof

@[fun_prop]
theorem iteD.arg_te.IsSmoothLinearMap_rule (A : Set X) (t e : W → 𝒟'(X,Y))
    (ht : IsSmoothLinearMap R t) (he : IsSmoothLinearMap R e) :
    IsSmoothLinearMap R (fun w => iteD A (t w) (e w)) := sorry_proof


----------------------------------------------------------------------------------------------------
-- Set restriction ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[pp_dot]
noncomputable
def Distribution.restrict (T : 𝒟'(X,Y)) (A : Set X) : 𝒟'(X,Y) :=
  ifD A then T else 0

@[simp,ftrans_simp]
theorem restrict_univ (T : 𝒟'(X,Y))  :
    T.restrict Set.univ = T := sorry_proof

@[simp,ftrans_simp]
theorem zero_restrict (A : Set X) :
    (0 : 𝒟'(X,Y)).restrict A = 0 := sorry_proof

@[restrict_push]
theorem add_restrict (T S : 𝒟'(X,Y)) (A : Set X) :
    (T + S).restrict A = T.restrict A + S.restrict A := sorry_proof

@[restrict_pull]
theorem add_restrict' (T S : 𝒟'(X,Y)) (A : Set X) :
    T.restrict A + S.restrict A = (T + S).restrict A := sorry_proof

@[restrict_push]
theorem sub_restrict (T S : 𝒟'(X,Y)) (A : Set X) :
    (T - S).restrict A = T.restrict A - S.restrict A := sorry_proof

@[restrict_pull]
theorem sub_restrict' (T S : 𝒟'(X,Y)) (A : Set X) :
    T.restrict A - S.restrict A = (T - S).restrict A := sorry_proof

@[restrict_push]
theorem smul_restrict (r : R) (T : 𝒟'(X,Y)) (A : Set X) :
    (r • T).restrict A = r • (T.restrict A) := sorry_proof

@[restrict_pull]
theorem smul_restrict' (r : R) (T : 𝒟'(X,Y)) (A : Set X) :
    r • (T.restrict A) = (r • T).restrict A := sorry_proof

@[restrict_push]
theorem neg_restrict (T : 𝒟'(X,Y)) (A : Set X) :
    (- T).restrict A = - (T.restrict A) := sorry_proof

@[restrict_pull]
theorem neg_restrict' (T : 𝒟'(X,Y)) (A : Set X) :
    - (T.restrict A) = (- T).restrict A := sorry_proof

open BigOperators in
@[restrict_push]
theorem finset_sum_restrict {I} [Fintype I] (T : I → 𝒟'(X,Y)) (A : Set X) :
    (∑ i, T i).restrict A = ∑ i, (T i).restrict A := sorry_proof

open BigOperators in
@[restrict_pull]
theorem finset_sum_restrict' {I} [Fintype I] (T : I → 𝒟'(X,Y)) (A : Set X) :
    ∑ i, (T i).restrict A = (∑ i, T i).restrict A := sorry_proof

@[restrict_push]
theorem indextype_sum_restrict {I} [IndexType I] (T : I → 𝒟' X) (A : Set X) :
    (∑ i, T i).restrict A = ∑ i, (T i).restrict A := sorry_proof

@[restrict_pull]
theorem indextype_sum_restrict' {I} [IndexType I] (T : I → 𝒟' X) (A : Set X) :
    ∑ i, (T i).restrict A = (∑ i, T i).restrict A := sorry_proof

@[simp,ftrans_simp]
theorem iteD_restrict (T : 𝒟'(X,Y)) (A : Set X) :
    (ifD A then T else 0) = T.restrict A := by rfl

@[simp,ftrans_simp]
theorem iteD_restrict' (T : 𝒟'(X,Y)) (A : Set X) :
    (ifD A then 0 else T) = T.restrict Aᶜ := sorry_proof


@[action_push]
theorem Distribution.extAction_iteD' (A B : Set X) (t e : 𝒟'(X,U)) (φ : X → V) (L : U ⊸ V ⊸ W) :
    ((iteD A t e).restrict B).extAction φ L =
        (t.restrict B).extAction (fun x => if x ∈ A then φ x else 0) L +
        (e.restrict B).extAction (fun x => if x ∉ A then φ x else 0) L := by sorry_proof



----------------------------------------------------------------------------------------------------
-- Distributiona product  --------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable {X₁} [Vec R X₁] {X₂} [Vec R X₂] {Y₁} [Vec R Y₁] {Y₂} [Vec R Y₂]

-- can we extended to vector valued distributions?
noncomputable
def Distribution.prod (p : X₁ → X₂ → X) (T : 𝒟' (X₁,Y₁)) (S : X₁ → 𝒟'(X₂,Y₂)) (L : Y₁ ⊸ Y₂ ⊸ Z) : 𝒟'(X,Z) :=
 ⟨fun φ => T.extAction (fun x₁ => S x₁ ⟨fun x₂ => φ (p x₁ x₂), sorry_proof⟩) L, sorry_proof⟩

@[simp, ftrans_simp]
theorem Distribution.prod_restrict (p : X₁ → X₂ → X) (T : 𝒟'(X₁,Y₁)) (S : X₁ → 𝒟'(X₂,Y₂)) (L : Y₁ ⊸ Y₂ ⊸ Z) (A : Set X) :
    (prod p T S L).restrict A = prod p (T.restrict (A.preimage1 p)) (fun x₁ => (S x₁).restrict (p x₁ ⁻¹' A)) L := sorry_proof

@[action_push]
theorem Distribution.prod'_extAction (p : X₁ → X₂ → X) (T : 𝒟'(X₁,Y₁)) (S : X₁ → 𝒟'(X₂,Y₂)) (L : Y₁ ⊸ Y₂ ⊸ Z) (K : Z ⊸ R ⊸ Z) (φ : X → R) :
    (prod p T S L).extAction φ K
    =
    T.extAction (fun x₁ => (S x₁).extAction (fun x₂ => φ (p x₁ x₂)) (fun y₂ ⊸ fun r ⊸ r • y₂)) (fun y₁ ⊸ fun y₂ ⊸ K (L y₁ y₂) 1) := sorry_proof

-- @[action_push]
-- theorem Distribution.prod'_extAction' (p : X₁ → X₂ → X) (T : 𝒟'(X₁,Y₁)) (S : X₁ → 𝒟'(X₂,Y₂)) (L : Y₁ ⊸ Y₂ ⊸ U) (φ : X → V) (K : U ⊸ V ⊸ W) :
--     (prod p T S L).extAction φ K
--     =
--     T.extAction (fun x₁ => (S x₁).extAction (fun x₂ => φ (p x₁ x₂)) (sorry : Y₂ ⊸ V ⊸ Y₂⊗V)) (fun y₁ ⊸ fun yv ⊸ ) := sorry_proof


----------------------------------------------------------------------------------------------------
-- Post Composition --------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

noncomputable
def Distribution.postComp (T : 𝒟'(X,Y)) (f : Y ⊸ Z) : 𝒟'(X,Z) := fun φ ⊸ f (T φ)

-- @[pp_dot]
-- noncomputable
-- abbrev Distribution.postExtAction (T : 𝒟'(X,𝒟'(Y,U))) (φ : Y → V) (L : U ⊸ V ⊸ W) : 𝒟'(X,W) :=
--   T.postComp (fun u ⊸ u.extAction φ L)

@[fun_prop]
theorem Distribution.postComp.arg_T.IsSmoothLinarMap_rule (T : W → 𝒟'(X,Y)) (f : Y ⊸ Z)
    (hT : IsSmoothLinearMap R T) :
    IsSmoothLinearMap R (fun w => (T w).postComp f) := by unfold postComp; sorry_proof

@[simp, ftrans_simp]
theorem postComp_id (u : 𝒟'(X,Y)) :
    (u.postComp (fun y ⊸ y)) = u := sorry_proof

@[simp, ftrans_simp]
theorem postComp_comp (x : 𝒟'(X,U)) (g : U ⊸ V) (f : V ⊸ W) :
    (x.postComp g).postComp f
    =
    x.postComp (fun u ⊸ f (g u)) := sorry_proof

@[simp, ftrans_simp]
theorem postComp_assoc (x : 𝒟'(X,U)) (y : U ⊸ 𝒟'(Y,V)) (f : V ⊸ W) (φ : Y → R) :
    (x.postComp y).postComp (fun T ⊸ T.postComp f)
    =
    (x.postComp (fun u ⊸ (y u).postComp f)) := sorry_proof

@[action_push]
theorem postComp_extAction (x : 𝒟'(X,U)) (f : U ⊸ V) (φ : X → W) (L : V ⊸ W ⊸ Z) :
    (x.postComp y).extAction φ L
    =
    (x.extAction φ (fun u ⊸ fun w ⊸ L (f u) w)) := sorry_proof

@[action_push]
theorem postComp_restrict_extAction (x : 𝒟'(X,U)) (f : U ⊸ V) (A : Set X) (φ : X → W) (L : V ⊸ W ⊸ Z) :
    ((x.postComp f).restrict A).extAction φ L
    =
    ((x.restrict A).extAction φ (fun u ⊸ fun w ⊸ (L (f u) w))) := sorry_proof


-- @[simp, ftrans_simp, action_push]
-- theorem Distribution.zero_postExtAction (φ : Y → R) : (0 : 𝒟'(X,𝒟'(Y,Z))).postExtAction φ = 0 := by sorry_proof

-- -- todo: this needs some integrability condition
-- @[action_push]
-- theorem Distribution.add_postExtAction (T T' : 𝒟'(X,𝒟'(Y,Z))) (φ : Y → R) :
--     (T + T').postExtAction φ = T.postExtAction φ + T'.postExtAction φ := by sorry_proof

-- @[action_push]
-- theorem Distribution.sub_postExtAction (T T' : 𝒟'(X,𝒟'(Y,Z))) (φ : Y → R) :
--     (T - T').postExtAction φ = T.postExtAction φ - T'.postExtAction φ := by sorry_proof

-- @[action_push]
-- theorem Distribution.smul_postExtAction (r : R) (T : 𝒟'(X,𝒟'(Y,Z))) (φ : Y → R) :
--     (r • T).postExtAction φ = r • T.postExtAction φ := by sorry_proof

-- @[action_push]
-- theorem Distribution.neg_postExtAction (T : 𝒟'(X,𝒟'(Y,Z))) (φ : Y → R) :
--     (- T).postExtAction φ = - T.postExtAction φ := by sorry_proof

-- open BigOperators in
-- @[action_push]
-- theorem Distribution.fintype_sum_postExtAction {I} [Fintype I] (T : I → 𝒟'(X,𝒟'(Y,Z))) (φ : Y → R) :
--     (∑ i, T i).postExtAction φ = ∑ i, (T i).postExtAction φ := by sorry_proof


-- @[action_push]
-- theorem Distribution.ifD_postExtAction (T T' : 𝒟'(X,𝒟'(Y,Z))) (A : Set X) (φ : Y → R) :
--     (ifD A then T else T').postExtAction φ = ifD A then T.postExtAction φ else T'.postExtAction φ := by sorry_proof


-- -- @[action_push]
-- -- theorem Distribution.indextype_sum_postExtAction {I} [IndexType I] (T : I → 𝒟'(X,𝒟'(Y,Z))) (φ : Y → R) :
-- --     (∑ i, T i).postExtAction φ = ∑ i, (T i).postExtAction φ := by sorry_proof


----------------------------------------------------------------------------------------------------
-- Functions as distributions ----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[coe, fun_trans]
noncomputable
def _root_.Function.toDistribution (f : X → Y) : 𝒟'(X,Y) :=
  fun φ ⊸ ∫' x, φ x • f x

def Distribution.IsFunction (T : 𝒟'(X,Y)) : Prop :=
  ∃ (f : X → Y), ∀ (φ : 𝒟 X),
      T φ = ∫' x, φ x • f x

noncomputable
def Distribution.toFunction (T : 𝒟'(X,Y)) : X → Y :=
  if h : T.IsFunction then
    choose h
  else
    0

@[action_push]
theorem Function.toDistribution_action (f : X → Y) (φ : 𝒟 X) :
    f.toDistribution φ = ∫' x, φ x • f x := by rfl

@[action_push]
theorem Function.toDistribution_extAction (f : X → Y) (φ : X → R) :
    f.toDistribution.extAction φ (fun y ⊸ fun r ⊸ r • y)
    =
    ∫' x, φ x • f x := sorry_proof

@[simp, ftrans_simp]
theorem Function.toDistribution_zero  :
    Function.toDistribution (fun (_ : X) => 0) = (0 : 𝒟'(X,Y)) := by sorry_proof


@[fun_trans,toDistrib_push]
theorem HAdd.hAdd.arg_a0a1.toDistribution_rule (f g : X → Y) :
    (fun x => f x + g x).toDistribution (R:=R)
    =
    f.toDistribution + g.toDistribution := sorry_proof

@[toDistrib_pull]
theorem HAdd.hAdd.arg_a0a1.toDistribution_rule' (f g : X → Y) :
    f.toDistribution + g.toDistribution
    =
    (fun x => f x + g x).toDistribution (R:=R) := sorry_proof

@[fun_trans,toDistrib_push]
theorem HSub.hSub.arg_a0a1.toDistribution_rule (f g : X → Y) :
    (fun x => f x - g x).toDistribution (R:=R)
    =
    f.toDistribution - g.toDistribution := sorry_proof

@[toDistrib_pull]
theorem HSub.hSub.arg_a0a1.toDistribution_rule' (f g : X → Y) :
    f.toDistribution - g.toDistribution
    =
    (fun x => f x - g x).toDistribution (R:=R) := sorry_proof


@[fun_trans,toDistrib_push]
theorem HSMul.hSMul.arg_a0a1.toDistribution_rule (r : R) (f : X → Y) :
    (fun x => r • f x).toDistribution (R:=R)
    =
    r • f.toDistribution := sorry_proof

@[toDistrib_pull]
theorem HSMul.hSMul.arg_a0a1.toDistribution_rule' (r : R) (f : X → Y) :
    r • f.toDistribution
    =
    (fun x => r • f x).toDistribution (R:=R) := sorry_proof


@[fun_trans,toDistrib_push]
theorem HMul.hMul.arg_a0.toDistribution_rule (r : R) (f : X → R) :
    (fun x => f x * r).toDistribution (R:=R)
    =
    r • f.toDistribution := sorry_proof


@[toDistrib_pull]
theorem HMul.hMul.arg_a0.toDistribution_rule' (r : R) (f : X → R) :
    r • f.toDistribution
    =
    (fun x => f x * r).toDistribution (R:=R) := sorry_proof


@[fun_trans,toDistrib_push]
theorem HMul.hMul.arg_a1.toDistribution_rule (r : R) (f : X → R) :
    (fun x => r • f x).toDistribution (R:=R)
    =
    r • f.toDistribution := sorry_proof

@[toDistrib_pull]
theorem HMul.hMul.arg_a1.toDistribution_rule' (r : R) (f : X → R) :
    r • f.toDistribution
    =
    (fun x => r • f x).toDistribution (R:=R) := sorry_proof

-- @[fun_trans]
-- theorem ite.arg_cte.toDistribution_rule (c : X → Prop) [∀ x, Decidable (c x)] (t e : X → Y) :
--   (fun x => if c x then t x else e x).toDistribution (R:=R)
--   =
--   ifD {x | c x} then
--     t.toDistribution
--   else
--     e.toDistribution := sorry_proof

@[toDistrib_pull]
theorem iteD.arg_cte.toDistribution_rule (s : Set X) (t e : X → Y) :
    (ifD s then
      t.toDistribution
    else
      e.toDistribution)
    =
    (fun x => if x ∈ s then t x else e x).toDistribution (R:=R) := sorry_proof


variable [MeasureSpace Y] [Module ℝ Z]



----------------------------------------------------------------------------------------------------
-- Measures as distributions -----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- open Classical in
variable [MeasurableSpace X]
@[coe]
noncomputable
def _root_.MeasureTheory.Measure.toDistribution
    (μ : Measure X) : 𝒟' X :=
  fun φ ⊸ ∫' x, φ x ∂μ

noncomputable
instance : Coe (Measure X) (𝒟' X) := ⟨fun μ => μ.toDistribution⟩

def Distribution.IsMeasure (f : 𝒟' X) : Prop :=
  ∃ (μ : Measure X), ∀ (φ : 𝒟 X),
      f φ = ∫' x, φ x ∂μ

open Classical
noncomputable
def Distribution.toMeasure (f' : 𝒟' X) : Measure X :=
  if h : f'.IsMeasure then
    choose h
  else
    0

-- @[simp]
-- theorem apply_measure_as_distribution  {X} [MeasurableSpace X]  (μ : Measure X) (φ : X → Y) :
--      ⟪μ.toDistribution, φ⟫ = ∫ x, φ x ∂μ := by rfl

/- under what conditions is this true??? -/
-- theorem action_is_integral  {X} [MeasurableSpace X] {Y} [MeasurableSpace Y]
--     (x : Measure X) (f : X → Measure Y)
--     (φ : Y → Z) (hφ : ∀ x, Integrable φ (f x)) :
--     ⟪x.toDistribution >>= (fun x => (f x).toDistribution), φ⟫
--     =
--     ∫ y, φ y ∂(@Measure.bind _ _ _ _ x f) := by
--   sorry_proof

-- def Distribution.densitvy {X} [MeasurableSpace X] (x y : 𝒟' X) : X → ℝ≥0∞ :=
--   x.toMeasure.rnDeriv y.toMeasure


----------------------------------------------------------------------------------------------------
-- Semi Inner Product Structure on Distributions  --------------------------------------------------
----------------------------------------------------------------------------------------------------

noncomputable
instance [SemiInnerProductSpace R Y] [Module ℝ Y] : Inner R (𝒟'(X,Y)) where
  inner u v := u.extAction (v.toFunction) ⟨fun y => ⟨fun y' => ⟪y,y'⟫, sorry_proof⟩, sorry_proof⟩

noncomputable
instance [SemiInnerProductSpace R Y] [Module ℝ Y] : TestFunctions (𝒟'(X,Y)) where
  TestFunction u := ∃ (φ : 𝒟 X) (y : Y), u = (fun x => φ x • y).toDistribution

noncomputable
instance [SemiInnerProductSpace R Y] [Module ℝ Y] : SemiInnerProductSpace R (𝒟'(X,Y)) := SemiInnerProductSpace.mkSorryProofs
