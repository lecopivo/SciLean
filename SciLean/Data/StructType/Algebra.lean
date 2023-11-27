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


open StructType in
class VecStruct (K X I XI) [StructType X I XI] [IsROrC K] [Vec K X] [∀ i, Vec K (XI i)] : Prop where
  structProj_add : ∀ i (x x' : X), structProj (x + x') i = structProj x i + structProj x' i
  structProj_smul : ∀ i (k : K) (x : X), structProj (k • x) i = k • structProj x i
  structProj_continuous : Continuous (fun (x : X) i =>  structProj x i)
  structMake_continuous : Continuous (fun f => structMake (X:=X) f)


--------------------------------------------------------------------------------
-- VecStruct instances ---------------------------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low) instVecStructDefault 
  {X} [Vec K X] : VecStruct K X Unit (fun _ => X) where
  structProj_add := by simp[structProj]
  structProj_smul := by simp[structProj]
  structProj_continuous := sorry_proof
  structMake_continuous := sorry_proof

@[reducible]
instance [∀ i, Vec K (EI i)] [∀ j, Vec K (FJ j)] (i : I ⊕ J) : Vec K (Prod.TypeFun EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

instance instVecStructProd
  [Vec K E] [Vec K F] [∀ i, Vec K (EI i)] [∀ j, Vec K (FJ j)] 
  [VecStruct K E I EI] [VecStruct K F J FJ]
  : VecStruct K (E×F) (I⊕J) (Prod.TypeFun EI FJ) where
  structProj_add := by simp[structProj, VecStruct.structProj_add]
  structProj_smul := by simp[structProj, VecStruct.structProj_smul]
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
  (x : W → X) (hx : IsLinearMap K x)
  : IsLinearMap K fun w => structProj (x w) i := sorry_proof

@[fprop]
theorem structProj.arg_x.IsDifferentiable_rule
  (x : W → X) (hx : IsDifferentiable K x)
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
  : structMake (X:=X) (fun _ => 0) = 0 :=
by
  apply structExt; simp

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
  apply structExt; simp
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
  testFun_structProj : ∀ (x : X), TestFunction x ↔ (∀ i, TestFunction (structProj x i))


--------------------------------------------------------------------------------
-- SemiInnerProductSpaceStruct instances ---------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low) {X} [SemiInnerProductSpace K X] : SemiInnerProductSpaceStruct K X Unit (fun _ => X) where
  inner_structProj := sorry_proof
  testFun_structProj := sorry_proof


instance [∀ i, SemiInnerProductSpace K (EI i)] [∀ j, SemiInnerProductSpace K (FJ j)] (i : I ⊕ J) 
  : SemiInnerProductSpace K (Prod.TypeFun EI FJ i) :=
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance


instance 
  [SemiInnerProductSpace K E] [SemiInnerProductSpace K F] 
  [∀ i, SemiInnerProductSpace K (EI i)] [∀ j, SemiInnerProductSpace K (FJ j)] 
  [EnumType I] [EnumType J]
  [SemiInnerProductSpaceStruct K E I EI] [SemiInnerProductSpaceStruct K F J FJ]
  : SemiInnerProductSpaceStruct K (E×F) (I⊕J) (Prod.TypeFun EI FJ) := sorry_proof
  -- inner_structProj := sorry_proof
  -- testFun_structProj := sorry_proof


instance [∀ i, FinVec ι K (EI i)] [∀ j, FinVec ι K (FJ j)] (i : I ⊕ J) 
  : FinVec ι K (Prod.TypeFun EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

@[simp, ftrans_simp]
theorem inner_oneHot_eq_inner_structProj [StructType X I XI] [EnumType I] [∀ i, SemiInnerProductSpace K (XI i)] [SemiInnerProductSpace K X] [SemiInnerProductSpaceStruct K X I XI] (i : I) (xi : XI i) (x : X)
  : ⟪x, oneHot i xi⟫[K] = ⟪structProj x i, xi⟫[K] := sorry_proof

@[simp, ftrans_simp]
theorem inner_oneHot_eq_inner_proj' [StructType X I XI] [EnumType I] [∀ i, SemiInnerProductSpace K (XI i)] [SemiInnerProductSpace K X] [SemiInnerProductSpaceStruct K X I XI] (i : I) (xi : XI i) (x : X)
  : ⟪oneHot i xi, x⟫[K] = ⟪xi, structProj x i⟫[K] := sorry_proof



