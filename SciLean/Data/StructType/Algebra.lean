import SciLean.Core.Objects.SemiInnerProductSpace
import SciLean.Core.Objects.FinVec
import SciLean.Core.FunctionPropositions.IsSmoothLinearMap
import SciLean.Core.Simp
import SciLean.Core.Meta.GenerateLinearMapSimp
import SciLean.Data.StructType.Basic

import SciLean.Tactic.AnalyzeConstLambda

set_option linter.unusedVariables false

namespace SciLean

variable
  (K : Type _) [IsROrC K]
  {ι κ : Type _} [EnumType ι] [EnumType κ]
  {E I : Type _} {EI : I → Type _}
  [StructType E I EI]
  {F J : Type _} {FJ : J → Type _}
  [StructType F J FJ]


--------------------------------------------------------------------------------
-- Algebra instances for Sum.rec ------------------------------------------
--------------------------------------------------------------------------------
-- There are some issues with defEq 

@[reducible]
instance [∀ i, Zero (EI i)] [∀ j, Zero (FJ j)] (i : I ⊕ J) : Zero (Sum.rec EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

@[reducible]
instance [∀ i, Add (EI i)] [∀ j, Add (FJ j)] (i : I ⊕ J) : Add (Sum.rec EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

@[reducible]
instance [∀ i, SMul K (EI i)] [∀ j, SMul K (FJ j)] (i : I ⊕ J) : SMul K (Sum.rec EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

@[reducible]
instance [∀ i, Neg (EI i)] [∀ j, Neg (FJ j)] (i : I ⊕ J) : Neg (Sum.rec EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

@[reducible]
instance [∀ i, Sub (EI i)] [∀ j, Sub (FJ j)] (i : I ⊕ J) : Sub (Sum.rec EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

@[reducible]
instance [∀ i, TopologicalSpace (EI i)] [∀ j, TopologicalSpace (FJ j)] (i : I ⊕ J) : TopologicalSpace (Sum.rec EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

@[reducible]
instance [∀ i, Vec K (EI i)] [∀ j, Vec K (FJ j)] (i : I ⊕ J) : Vec K (Sum.rec EI FJ i) := Vec.mkSorryProofs
-- all the proofs should be solvable `by induction i <;> infer_instance`

@[reducible]
instance [∀ i, Inner K (EI i)] [∀ j, Inner K (FJ j)] (i : I ⊕ J) : Inner K (Sum.rec EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

@[reducible]
instance [∀ i, TestFunctions (EI i)] [∀ j, TestFunctions (FJ j)] (i : I ⊕ J) : TestFunctions (Sum.rec EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

@[reducible]
instance [∀ i, SemiInnerProductSpace K (EI i)] [∀ j, SemiInnerProductSpace K (FJ j)] (i : I ⊕ J) 
  : SemiInnerProductSpace K (Sum.rec EI FJ i) := SemiInnerProductSpace.mkSorryProofs

@[reducible]
instance [∀ i, SemiHilbert K (EI i)] [∀ j, SemiHilbert K (FJ j)] (i : I ⊕ J) 
  : SemiHilbert K (Sum.rec EI FJ i) where
  test_functions_true := by induction i <;> apply SemiHilbert.test_functions_true

-- instance [∀ i, FinVec ι K (EI i)] [∀ j, FinVec ι K (FJ j)] (i : I ⊕ J) 
--   : FinVec ι K (Sum.rec EI FJ i) := 
--   match i with
--   | .inl _ => by infer_instance
--   | .inr _ => by infer_instance

--------------------------------------------------------------------------------
-- Algebraic struct classes ----------------------------------------------------
--------------------------------------------------------------------------------

class ZeroStruct (X I XI) [StructType X I XI] [Zero X] [∀ i, Zero (XI i)] : Prop where
  structProj_zero : ∀ (i : I), structProj (0 : X) i = 0

class AddStruct (X I XI) [StructType X I XI] [Add X] [∀ i, Add (XI i)] : Prop where
  structProj_add : ∀ (i : I) (x x' : X), structProj (x + x') i = structProj x i + structProj x' i

class SMulStruct (K X I XI) [StructType X I XI] [SMul K X] [∀ i, SMul K (XI i)] : Prop where
  structProj_smul : ∀ (i : I) (k : K) (x : X), structProj (k • x) i = k • structProj x i

class VecStruct (K X I XI) [StructType X I XI] [IsROrC K] [Vec K X] [∀ i, Vec K (XI i)] 
  extends ZeroStruct X I XI, AddStruct X I XI, SMulStruct K X I XI : Prop 
  where
    structProj_continuous : Continuous (fun (x : X) (i : I) =>  structProj x i)
    structMake_continuous : Continuous (fun (f : (i : I) → XI i) => structMake (X:=X) f)

--------------------------------------------------------------------------------
-- ZeroStruct instances ---------------------------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low) instZeroStructDefault 
  {X} [Zero X] : ZeroStruct X Unit (fun _ => X) where
  structProj_zero := by simp[structProj]

instance instZeroStructProd
  [Zero E] [Zero F] [∀ i, Zero (EI i)] [∀ j, Zero (FJ j)] 
  [ZeroStruct E I EI] [ZeroStruct F J FJ]
  : ZeroStruct (E×F) (I⊕J) (Sum.rec EI FJ) where
  structProj_zero := by simp[structProj, ZeroStruct.structProj_zero]


--------------------------------------------------------------------------------
-- AddStruct instances ---------------------------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low) instAddStructDefault 
  {X} [Add X] : AddStruct X Unit (fun _ => X) where
  structProj_add := by simp[structProj]

instance instAddStructProd
  [Add E] [Add F] [∀ i, Add (EI i)] [∀ j, Add (FJ j)] 
  [AddStruct E I EI] [AddStruct F J FJ]
  : AddStruct (E×F) (I⊕J) (Sum.rec EI FJ) where
  structProj_add := by simp[structProj, AddStruct.structProj_add]


--------------------------------------------------------------------------------
-- SMulStruct instances ---------------------------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low) instSMulStructDefault 
  {X} [SMul K X] : SMulStruct K X Unit (fun _ => X) where
  structProj_smul := by simp[structProj]

instance instSMulStructProd
  [SMul K E] [SMul K F] [∀ i, SMul K (EI i)] [∀ j, SMul K (FJ j)] 
  [SMulStruct K E I EI] [SMulStruct K F J FJ]
  : SMulStruct K (E×F) (I⊕J) (Sum.rec EI FJ) where
  structProj_smul := by simp[structProj, SMulStruct.structProj_smul]


--------------------------------------------------------------------------------
-- VecStruct instances ---------------------------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low) instVecStructDefault 
  {X} [Vec K X] : VecStruct K X Unit (fun _ => X) where
  structProj_zero := by simp[structProj]
  structProj_add := by simp[structProj]
  structProj_smul := by simp[structProj]
  structProj_continuous := sorry_proof
  structMake_continuous := sorry_proof

instance instVecStructProd
  [Vec K E] [Vec K F] [∀ i, Vec K (EI i)] [∀ j, Vec K (FJ j)]
  [VecStruct K E I EI] [VecStruct K F J FJ]
  : VecStruct K (E×F) (I⊕J) (Sum.rec EI FJ) where
  structProj_continuous := sorry_proof
  structMake_continuous := sorry_proof


--------------------------------------------------------------------------------
-- VecStruct simps -------------------------------------------------------------
--------------------------------------------------------------------------------

section VecStruct 
open StructType

variable 
  {X XI} [StructType X I XI] [DecidableEq I] [∀ i, Vec K (XI i)] [Vec K X] [VecStruct K X I XI]
  {W} [Vec K W]


namespace StructType

-- structProj ------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem structProj.arg_x.IsLinearMap_rule_simple (i : I)
  : IsLinearMap K fun (x : X) => structProj x i := sorry_proof

#generate_linear_map_simps SciLean.StructType.structProj.arg_x.IsLinearMap_rule_simple

attribute [simp, ftrans_simp] 
  structProj.arg_x.add_pull 
  structProj.arg_x.sub_pull 
  structProj.arg_x.neg_pull 
  structProj.arg_x.smul_pull
  
@[fprop]
theorem structProj.arg_x.IsLinearMap_rule
  (x : W → X) (i : I) (hx : IsLinearMap K x)
  : IsLinearMap K fun w => structProj (x w) i := sorry_proof

@[fprop]
theorem structProj.arg_x.IsDifferentiable_rule
  (x : W → X) (i : I) (hx : IsDifferentiable K x)
  : IsDifferentiable K fun w => structProj (x w) i := sorry_proof


-- structMake ------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem structMake.arg_f.IsLinearMap_rule_simple 
  : IsLinearMap K fun (f : (i : I) → XI i) => structMake (X:=X) f := sorry_proof

#generate_linear_map_simps SciLean.StructType.structMake.arg_f.IsLinearMap_rule_simple

attribute [simp, ftrans_simp]
  structMake.arg_f.add_push 
  structMake.arg_f.sub_push 
  structMake.arg_f.neg_push 
  structMake.arg_f.smul_push
  
@[fprop]
theorem structMake.arg_f.IsLinearMap_rule
  (f : W →  (i : I) → XI i) (hf : IsLinearMap K f)
  : IsLinearMap K fun w => structMake (X:=X) (f w) := sorry_proof

@[fprop]
theorem structMake.arg_f.IsDifferentiable_rule
  (f : W →  (i : I) → XI i) (hf : IsDifferentiable K f)
  : IsDifferentiable K fun w => structMake (X:=X) (f w) := sorry_proof

@[simp, ftrans_simp]
theorem structMake_zero
  : structMake (X:=X) (fun _ : I => 0) = 0 :=
by
  apply structExt (I:=I); simp

end StructType


-- oneHot ------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem oneHot.arg_xi.IsLinearMap_rule_simple (i : I)
  : IsLinearMap K fun (xi : XI i) => oneHot (X:=X) i xi := sorry_proof

#generate_linear_map_simps SciLean.oneHot.arg_xi.IsLinearMap_rule_simple
  
@[fprop]
theorem oneHot.arg_xi.IsLinearMap_rule
  (i : I) (xi : W → XI i) (hxi : IsLinearMap K xi)
  : IsLinearMap K fun w => oneHot (X:=X) i (xi w) := sorry_proof

@[fprop]
theorem oneHot.arg_xi.IsDifferentiable_rule
  (i : I) (xi : W → XI i) (hxi : IsDifferentiable K xi)
  : IsDifferentiable K fun w => oneHot (X:=X) i (xi w) := sorry_proof

@[simp]
theorem add_oneHot_eq_structModify (i : I) (xi : XI i) (x : X)
  : x + oneHot (X:=X) i xi = structModify i (fun xi' => xi' + xi) x := 
by
  apply structExt (I:=I); simp
  intro j
  if h:i=j then
    subst h; simp
  else
    simp[h]

@[simp]
theorem add_oneHot_eq_structModify' (i : I) (xi : XI i) (x : X)
  : oneHot (X:=X) i xi + x = structModify i (fun xi' => xi + xi') x := 
by
  simp[add_comm]

end VecStruct 


--------------------------------------------------------------------------------
-- SemiInnerProductSpaceStruct -------------------------------------------------
--------------------------------------------------------------------------------

open StructType in
class SemiInnerProductSpaceStruct (K X I XI) [StructType X I XI] [IsROrC K] [EnumType I] [SemiInnerProductSpace K X] [∀ i, SemiInnerProductSpace K (XI i)] extends VecStruct K X I XI : Prop where
  inner_structProj : ∀ (x x' : X), ⟪x,x'⟫[K] = ∑ (i : I), ⟪structProj x i, structProj x' i⟫[K]
  testFun_structProj : ∀ (x : X), TestFunction x ↔ (∀ i : I, TestFunction (structProj x i))


--------------------------------------------------------------------------------
-- SemiInnerProductSpaceStruct instances ---------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low) {X} [SemiInnerProductSpace K X] : SemiInnerProductSpaceStruct K X Unit (fun _ => X) where
  inner_structProj := sorry_proof
  testFun_structProj := sorry_proof


instance 
  [SemiInnerProductSpace K E] [SemiInnerProductSpace K F] 
  [∀ i, SemiInnerProductSpace K (EI i)] [∀ j, SemiInnerProductSpace K (FJ j)] 
  [EnumType I] [EnumType J]
  [SemiInnerProductSpaceStruct K E I EI] [SemiInnerProductSpaceStruct K F J FJ]
  : SemiInnerProductSpaceStruct K (E×F) (I⊕J) (Sum.rec EI FJ) := sorry_proof
  -- inner_structProj := sorry_proof
  -- testFun_structProj := sorry_proof


@[simp, ftrans_simp]
theorem inner_oneHot_eq_inner_structProj [StructType X I XI] [EnumType I] [∀ i, SemiInnerProductSpace K (XI i)] [SemiInnerProductSpace K X] [SemiInnerProductSpaceStruct K X I XI] (i : I) (xi : XI i) (x : X)
  : ⟪x, oneHot i xi⟫[K] = ⟪structProj x i, xi⟫[K] := sorry_proof

@[simp, ftrans_simp]
theorem inner_oneHot_eq_inner_proj' [StructType X I XI] [EnumType I] [∀ i, SemiInnerProductSpace K (XI i)] [SemiInnerProductSpace K X] [SemiInnerProductSpaceStruct K X I XI] (i : I) (xi : XI i) (x : X)
  : ⟪oneHot i xi, x⟫[K] = ⟪xi, structProj x i⟫[K] := sorry_proof



--------------------------------------------------------------------------------
-- Prod simp lemmas
-- TODO: move somewhere else
--------------------------------------------------------------------------------

section OneHotSimp

variable   
  [Zero E] [∀ i, Zero (EI i)] [ZeroStruct E I EI]
  [Zero F] [∀ j, Zero (FJ j)] [ZeroStruct F J FJ]
  [DecidableEq I] [DecidableEq J]

@[simp, ftrans_simp]
theorem oneHot_inl (i : I) (xi : EI i)
  : (oneHot (X:=E×F) (I:=I⊕J) (.inl i) xi)
    =
    (oneHot i xi, 0) := 
by 
  simp[oneHot, structMake]
  constructor
  . congr; funext; congr; funext h; subst h; rfl
  . apply structExt (I:=J); simp [ZeroStruct.structProj_zero]

@[simp, ftrans_simp]
theorem oneHot_inr (j : J) (xj : FJ j)
  : (oneHot (X:=E×F) (I:=I⊕J) (.inr j) xj)
    =
    (0, oneHot j xj) := 
by 
  simp[oneHot, structMake]
  constructor
  . apply structExt (I:=I); simp [ZeroStruct.structProj_zero]
  . congr; funext; congr; funext h; subst h; rfl

end OneHotSimp

