import SciLean.Analysis.Convenient.IsSmoothLinearMap
import SciLean.Analysis.Normed.IsContinuousLinearMap
import SciLean.Algebra.IsAffineMap
import SciLean.Topology.Continuous

import SciLean.Data.StructType.Basic

import SciLean.Tactic.AnalyzeConstLambda
import SciLean.Meta.GenerateFunProp

set_option linter.unusedVariables false
set_option linter.hashCommand false

open LeanColls

namespace SciLean

variable
  (K : Type _) [RCLike K]
  {ι κ : Type _}
  [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  [IndexType κ] [LawfulIndexType κ] [DecidableEq κ]
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
instance [∀ i, One (EI i)] [∀ j, One (FJ j)] (i : I ⊕ J) : One (Sum.rec EI FJ i) :=
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
instance [∀ i, TopologicalSpace (EI i)] [∀ j, TopologicalSpace (FJ j)] (i : I ⊕ J) :
    TopologicalSpace (Sum.rec EI FJ i) :=
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

@[reducible]
instance [∀ i, UniformSpace (EI i)] [∀ j, UniformSpace (FJ j)] (i : I ⊕ J) :
    UniformSpace (Sum.rec EI FJ i) where
  uniformity := match i with
                | .inl _ => UniformSpace.uniformity
                | .inr _ => UniformSpace.uniformity
  symm := sorry_proof
  comp := sorry_proof
  nhds_eq_comap_uniformity := sorry_proof

@[reducible]
instance [∀ i, AddCommGroup (EI i)] [∀ j, AddCommGroup (FJ j)] (i : I ⊕ J) :
    AddCommGroup (Sum.rec EI FJ i) := AddCommGroup.mkSorryProofs

@[reducible]
instance
    [∀ i, AddCommGroup (EI i)] [∀ i, Module K (EI i)]
    [∀ j, AddCommGroup (FJ j)] [∀ j, Module K (FJ j)] (i : I ⊕ J) :
    Module K (Sum.rec EI FJ i) := Module.mkSorryProofs

@[reducible]
instance [∀ i, Vec K (EI i)] [∀ j, Vec K (FJ j)] (i : I ⊕ J) : Vec K (Sum.rec EI FJ i) :=
  Vec.mkSorryProofs
-- all the proofs should be solvable `by induction i <;> infer_instance`

@[reducible]
instance [∀ i, Inner K (EI i)] [∀ j, Inner K (FJ j)] (i : I ⊕ J) : Inner K (Sum.rec EI FJ i) :=
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

@[reducible]
instance [∀ i, TestFunctions (EI i)] [∀ j, TestFunctions (FJ j)] (i : I ⊕ J) :
    TestFunctions (Sum.rec EI FJ i) :=
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

-- instance [∀ i, FinVec ι K (EI i)] [∀ j, FinVec ι K (FJ j)] (i : I ⊕ J) :
--     FinVec ι K (Sum.rec EI FJ i) :=
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

class ModuleStruct (K X I XI) [StructType X I XI] [RCLike K] [AddCommGroup X] [Module K X] [∀ i, AddCommGroup (XI i)] [∀ i, Module K (XI i)]
  extends ZeroStruct X I XI, AddStruct X I XI, SMulStruct K X I XI : Prop where
  hoh : True := True.intro

class TopologicalStruct (X I XI) [StructType X I XI] [TopologicalSpace X] [∀ i, TopologicalSpace (XI i)] : Prop
  where
    -- todo: maybe it should say `Continuous (fun (x : X) (i : I) => structProj x i)`
    structProj_continuous : ∀ (i : I), Continuous (fun (x : X) => structProj x i)
    structMake_continuous : Continuous (fun (f : (i : I) → XI i) => structMake (X:=X) f)

class VecStruct (K X I XI) [StructType X I XI] [RCLike K]
    [AddCommGroup X] [Module K X] [TopologicalSpace X]
    [∀ i, AddCommGroup (XI i)] [∀ i, Module K (XI i)] [∀ i, TopologicalSpace (XI i)]
  extends TopologicalStruct X I XI, ModuleStruct K X I XI : Prop


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
-- TopologicalStruct instances -------------------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low) instTopologicalStructDefault
  {X} [TopologicalSpace X] : TopologicalStruct X Unit (fun _ => X) where
  structProj_continuous := sorry_proof
  structMake_continuous := sorry_proof

instance instTopologicalStructProd
  [TopologicalSpace E] [TopologicalSpace F] [∀ i, TopologicalSpace (EI i)] [∀ j, TopologicalSpace (FJ j)]
  [TopologicalStruct E I EI] [TopologicalStruct F J FJ]
  : TopologicalStruct (E×F) (I⊕J) (Sum.rec EI FJ) where
  structProj_continuous := sorry_proof
  structMake_continuous := sorry_proof


--------------------------------------------------------------------------------
-- ModuleStruct instances ---------------------------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low) instModuleStructDefault
  {X} [AddCommGroup X] [Module K X] : ModuleStruct K X Unit (fun _ => X) where

instance instModuleStructProd
  [AddCommGroup E] [Module K E] [∀ i, AddCommGroup (EI i)] [∀ i, Module K (EI i)] [ModuleStruct K E I EI]
  [AddCommGroup F] [Module K F] [∀ j, AddCommGroup (FJ j)] [∀ j, Module K (FJ j)] [ModuleStruct K F J FJ]
  : ModuleStruct K (E×F) (I⊕J) (Sum.rec EI FJ) where


--------------------------------------------------------------------------------
-- VecStruct instances ---------------------------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low) instVecStructDefault
  {X} [AddCommGroup X] [Module K X] [TopologicalSpace X] : VecStruct K X Unit (fun _ => X) where

instance instVecStructProd
  [AddCommGroup E] [Module K E] [TopologicalSpace E]
  [∀ i, AddCommGroup (EI i)] [∀ i, Module K (EI i)] [∀ i, TopologicalSpace (EI i)] [VecStruct K E I EI]
  [AddCommGroup F] [Module K F] [TopologicalSpace F]
  [∀ j, AddCommGroup (FJ j)] [∀ j, Module K (FJ j)] [∀ j, TopologicalSpace (FJ j)] [VecStruct K F J FJ]
  : VecStruct K (E×F) (I⊕J) (Sum.rec EI FJ) where


--------------------------------------------------------------------------------
-- VecStruct simps -------------------------------------------------------------
--------------------------------------------------------------------------------

section VecStruct
open StructType

variable [DecidableEq I]

namespace StructType


----------------------------------------------------------------------------------------------------
-- Function properties of structProj, structMake, oneHot -------------------------------------------
----------------------------------------------------------------------------------------------------

section OnModule
variable
  {X : Type _} [AddCommGroup X] [Module K X]
  {XI : I → Type _} [∀ i, AddCommGroup (XI i)] [∀ i, Module K (XI i)]
  [StructType X I XI] [ModuleStruct K X I XI]

  def_fun_prop with_transitive (i : I) : IsLinearMap K fun (x : X) => structProj x i by
    constructor
    · apply AddStruct.structProj_add
    · apply SMulStruct.structProj_smul

  def_fun_prop with_transitive : IsLinearMap K fun (f : (i : I) → XI i) => structMake (X:=X) f by
    constructor
    · intros; apply structExt (I:=I) (XI:=XI); intro i; rw[AddStruct.structProj_add]; simp
    · intros; apply structExt (I:=I) (XI:=XI); intro i; rw[SMulStruct.structProj_smul]; simp

  def_fun_prop with_transitive (i : I) : IsLinearMap K fun (xi : XI i) => oneHot (X:=X) i xi by
    constructor
    · intros; apply structExt (I:=I) (XI:=XI); intro i; rw[AddStruct.structProj_add]; simp[oneHot]; aesop
    · intros; apply structExt (I:=I) (XI:=XI); intro i; rw[SMulStruct.structProj_smul]; simp[oneHot]; aesop

  -- TODO: most of the generated theorems are useless as they can't infer the field `K`
  --       There should be command `#generate_add_hom_simps` and `#generate_zero_hom_simps`
  --       or `#generate_add_group_hom_simps`
  #generate_linear_map_simps structProj.arg_x.IsLinearMap_rule
  #generate_linear_map_simps structMake.arg_f.IsLinearMap_rule
  #generate_linear_map_simps oneHot.arg_xi.IsLinearMap_rule

  attribute [simp, simp_core]
    structProj.arg_x.add_pull
    structProj.arg_x.sub_pull
    structProj.arg_x.neg_pull
    structProj.arg_x.smul_pull

  attribute [simp, simp_core]
    structMake.arg_f.add_push
    structMake.arg_f.sub_push
    structMake.arg_f.neg_push
    structMake.arg_f.smul_push

end OnModule


section OnTopologicalSpace
variable
  {X : Type _} [TopologicalSpace X]
  {XI : I → Type _} [∀ i, TopologicalSpace (XI i)]
  [StructType X I XI] [TopologicalStruct X I XI] [∀ i, Zero (XI i)]

  def_fun_prop with_transitive (i : I) : Continuous fun (x : X) => structProj x i by
    apply TopologicalStruct.structProj_continuous

  def_fun_prop with_transitive : Continuous fun (f : (i : I) → XI i) => structMake (X:=X) f by
    apply TopologicalStruct.structMake_continuous

  def_fun_prop with_transitive (i : I) : Continuous fun (xi : XI i) => oneHot (X:=X) i xi by
    simp[oneHot, autoParam]
    fun_prop

end OnTopologicalSpace


section OnTopologicalVectorSpace
variable
  {X : Type _} [AddCommGroup X] [Module K X] [TopologicalSpace X]
  {XI : I → Type _} [∀ i, AddCommGroup (XI i)] [∀ i, Module K (XI i)] [∀ i, TopologicalSpace (XI i)]
  [StructType X I XI] [ModuleStruct K X I XI] [TopologicalStruct X I XI]

  def_fun_prop with_transitive (i : I) : IsContinuousLinearMap K fun (x : X) => structProj x i by
    constructor
    · fun_prop
    · simp[autoParam]; apply TopologicalStruct.structProj_continuous

  def_fun_prop with_transitive : IsContinuousLinearMap K fun (f : (i : I) → XI i) => structMake (X:=X) f by
    constructor
    · fun_prop
    · apply TopologicalStruct.structMake_continuous

  def_fun_prop with_transitive (i : I) : IsContinuousLinearMap K fun (xi : XI i) => oneHot (X:=X) i xi by
    constructor
    · fun_prop
    · simp[oneHot, autoParam]; fun_prop

end OnTopologicalVectorSpace

section OnNormedSpace
variable
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {XI : I → Type _} [∀ i, NormedAddCommGroup (XI i)] [∀ i, NormedSpace K (XI i)]
  [StructType X I XI] [VecStruct K X I XI]
  [Fintype I]

  def_fun_prop with_transitive (i : I) : Differentiable K fun (x : X) => structProj x i by fun_prop
  def_fun_prop with_transitive : Differentiable K fun (f : (i : I) → XI i) => structMake (X:=X) f by fun_prop
  def_fun_prop with_transitive (i : I) : Differentiable K fun (xi : XI i) => oneHot (X:=X) i xi by fun_prop

end OnNormedSpace

section OnConvenientSpace
variable
  {X : Type _} [Vec K X]
  {XI : I → Type _} [∀ i, Vec K (XI i)]
  [StructType X I XI] [VecStruct K X I XI]

  def_fun_prop with_transitive (i : I) : IsSmoothLinearMap K fun (x : X) => structProj x i by sorry_proof
  def_fun_prop with_transitive : IsSmoothLinearMap K fun (f : (i : I) → XI i) => structMake (X:=X) f by sorry_proof
  def_fun_prop with_transitive (i : I) : IsSmoothLinearMap K fun (xi : XI i) => oneHot (X:=X) i xi by sorry_proof

end OnConvenientSpace

end StructType


-- oneHot ------------------------------------------------------------------
--------------------------------------------------------------------------------

variable
  {X XI} [StructType X I XI] [DecidableEq I] [∀ i, Vec K (XI i)] [Vec K X] [VecStruct K X I XI]
  {W} [Vec K W]


@[simp, simp_core]
theorem add_oneHot_eq_structModify (i : I) (xi : XI i) (x : X)
  : x + oneHot (X:=X) i xi = structModify i (fun xi' => xi' + xi) x :=
by
  apply structExt (I:=I);
  sorry_proof
  -- todo: fix generated simp thereom about structProj
  -- simp
  -- intro j
  -- if h:i=j then
  --   subst h; simp
  -- else
  --   simp[h]

@[simp, simp_core]
theorem add_oneHot_eq_structModify' (i : I) (xi : XI i) (x : X)
  : oneHot (X:=X) i xi + x = structModify i (fun xi' => xi + xi') x :=
by
  simp[add_comm]

end VecStruct


--------------------------------------------------------------------------------
-- SemiInnerProductSpaceStruct -------------------------------------------------
--------------------------------------------------------------------------------

open StructType in
class SemiInnerProductSpaceStruct (K X I XI) [StructType X I XI] [RCLike K] [IndexType I]
  [LawfulIndexType I] [SemiInnerProductSpace K X] [∀ i, SemiInnerProductSpace K (XI i)]
  extends
    VecStruct K X I XI : Prop
  where
    inner_structProj : ∀ (x x' : X), ⟪x,x'⟫[K] = ∑ (i : I), ⟪structProj x i, structProj x' i⟫[K]
    testFun_structProj : ∀ (x : X), TestFunction x ↔ (∀ i : I, TestFunction (structProj x i))


--------------------------------------------------------------------------------
-- SemiInnerProductSpaceStruct instances ---------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low) {X} [SemiInnerProductSpace K X] :
    SemiInnerProductSpaceStruct K X Unit (fun _ => X) where
  inner_structProj := sorry_proof
  testFun_structProj := sorry_proof


instance
  [SemiInnerProductSpace K E] [SemiInnerProductSpace K F]
  [∀ i, SemiInnerProductSpace K (EI i)] [∀ j, SemiInnerProductSpace K (FJ j)]
  [IndexType I] [LawfulIndexType I] [IndexType J] [LawfulIndexType J]
  [SemiInnerProductSpaceStruct K E I EI] [SemiInnerProductSpaceStruct K F J FJ] :
  SemiInnerProductSpaceStruct K (E×F) (I⊕J) (Sum.rec EI FJ) := sorry_proof
  -- inner_structProj := sorry_proof
  -- testFun_structProj := sorry_proof


@[simp, simp_core]
theorem inner_oneHot_eq_inner_structProj [StructType X I XI] [IndexType I] [LawfulIndexType I]
    [DecidableEq I] [∀ i, SemiInnerProductSpace K (XI i)] [SemiInnerProductSpace K X]
    [SemiInnerProductSpaceStruct K X I XI] (i : I) (xi : XI i) (x : X) :
    ⟪x, oneHot i xi⟫[K] = ⟪structProj x i, xi⟫[K] := sorry_proof

@[simp, simp_core]
theorem inner_oneHot_eq_inner_proj' [StructType X I XI] [IndexType I] [LawfulIndexType I]
    [DecidableEq I] [∀ i, SemiInnerProductSpace K (XI i)] [SemiInnerProductSpace K X]
    [SemiInnerProductSpaceStruct K X I XI] (i : I) (xi : XI i) (x : X) :
    ⟪oneHot i xi, x⟫[K] = ⟪xi, structProj x i⟫[K] := sorry_proof



--------------------------------------------------------------------------------
-- Prod simp lemmas
-- TODO: move somewhere else
--------------------------------------------------------------------------------

section OneHotSimp

variable
  [Zero E] [∀ i, Zero (EI i)] [ZeroStruct E I EI]
  [Zero F] [∀ j, Zero (FJ j)] [ZeroStruct F J FJ]
  [DecidableEq I] [DecidableEq J]

@[simp, simp_core]
theorem oneHot_inl (i : I) (xi : EI i)
  : (oneHot (X:=E×F) (I:=I⊕J) (.inl i) xi)
    =
    (oneHot i xi, 0) :=
by
  simp[oneHot, structMake]
  constructor
  · congr; funext; congr; funext h; subst h; rfl
  · apply structExt (I:=J); simp [ZeroStruct.structProj_zero]

@[simp, simp_core]
theorem oneHot_inr (j : J) (xj : FJ j)
  : (oneHot (X:=E×F) (I:=I⊕J) (.inr j) xj)
    =
    (0, oneHot j xj) :=
by
  simp[oneHot, structMake]
  constructor
  · apply structExt (I:=I); simp [ZeroStruct.structProj_zero]
  · congr; funext; congr; funext h; subst h; rfl

end OneHotSimp
