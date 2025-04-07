import SciLean.Analysis.Normed.IsContinuousLinearMap
import SciLean.Algebra.IsAffineMap
import SciLean.Topology.Continuous
import SciLean.Analysis.Sorry

import SciLean.Data.StructType.Basic

import SciLean.Tactic.AnalyzeConstLambda
import SciLean.Meta.GenerateFunProp
import SciLean.Meta.GenerateAddGroupHomSimp

set_option linter.unusedVariables false
set_option linter.hashCommand false

namespace SciLean

variable
  (K : Type _) [RCLike K]
  {ι κ : Type _} {nι nκ : ℕ}
  [IndexType ι nι] [DecidableEq ι]
  [IndexType κ nκ] [DecidableEq κ]
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
instance [∀ i, Norm (EI i)] [∀ j, Norm (FJ j)] (i : I ⊕ J) : Norm (Sum.rec EI FJ i) :=
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

@[reducible]
instance [∀ i, Dist (EI i)] [∀ j, Dist (FJ j)] (i : I ⊕ J) : Dist (Sum.rec EI FJ i) :=
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

@[reducible]
instance [∀ i, EDist (EI i)] [∀ j, EDist (FJ j)] (i : I ⊕ J) : EDist (Sum.rec EI FJ i) :=
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
instance [∀ i, MetricSpace (EI i)] [∀ j, MetricSpace (FJ j)] (i : I ⊕ J) :
    MetricSpace (Sum.rec EI FJ i) where
  dist_self := sorry_proof
  dist_comm := sorry_proof
  dist_triangle := sorry_proof
  edist :=
    match i with
    | .inl _ => edist
    | .inr _ => edist
  edist_dist := sorry_proof
  toUniformSpace := by infer_instance
  uniformity_dist := sorry_proof
  toBornology :=
    match i with
    | .inl _ => by infer_instance
    | .inr _ => by infer_instance
  cobounded_sets := sorry_proof
  eq_of_dist_eq_zero := sorry_proof

@[reducible]
instance [∀ i, AddCommGroup (EI i)] [∀ j, AddCommGroup (FJ j)] (i : I ⊕ J) :
    AddCommGroup (Sum.rec EI FJ i) := AddCommGroup.mkSorryProofs

@[reducible]
instance [∀ i, NormedAddCommGroup (EI i)] [∀ j, NormedAddCommGroup (FJ j)] (i : I ⊕ J) :
    NormedAddCommGroup (Sum.rec EI FJ i) where
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by sorry_proof


@[reducible]
instance
    [∀ i, AddCommGroup (EI i)] [∀ i, Module K (EI i)]
    [∀ j, AddCommGroup (FJ j)] [∀ j, Module K (FJ j)] (i : I ⊕ J) :
    Module K (Sum.rec EI FJ i) := Module.mkSorryProofs


@[reducible]
instance [∀ i, Inner K (EI i)] [∀ j, Inner K (FJ j)] (i : I ⊕ J) : Inner K (Sum.rec EI FJ i) :=
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance


@[reducible]
instance [∀ i, NormedAddCommGroup (EI i)] [∀ i, AdjointSpace K (EI i)]
         [∀ j, NormedAddCommGroup (FJ j)] [∀ j, AdjointSpace K (FJ j)] (i : I ⊕ J)
  : AdjointSpace K (Sum.rec EI FJ i) where
  norm_smul_le := sorry_proof
  inner_top_equiv_norm := sorry_proof
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof


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

class NegStruct (X I XI) [StructType X I XI] [Neg X] [∀ i, Neg (XI i)] : Prop where
  structProj_neg : ∀ (i : I) (x : X), structProj (-x) i = - structProj x i

class SMulStruct (K X I XI) [StructType X I XI] [SMul K X] [∀ i, SMul K (XI i)] : Prop where
  structProj_smul : ∀ (i : I) (k : K) (x : X), structProj (k • x) i = k • structProj x i

class ModuleStruct (K X I XI) [StructType X I XI] [RCLike K] [AddCommGroup X] [Module K X] [∀ i, AddCommGroup (XI i)] [∀ i, Module K (XI i)] : Prop
  extends ZeroStruct X I XI, AddStruct X I XI, NegStruct X I XI, SMulStruct K X I XI where
    structProj_neg := sorry_proof -- todo: infer this from `structProj_add` and `structProj_smul`

class TopologicalStruct (X I XI) [StructType X I XI] [TopologicalSpace X] [∀ i, TopologicalSpace (XI i)] : Prop
  where
    -- todo: maybe it should say `Continuous (fun (x : X) (i : I) => structProj x i)`
    structProj_continuous : ∀ (i : I), Continuous (fun (x : X) => structProj x i)
    structMake_continuous : Continuous (fun (f : (i : I) → XI i) => structMake (X:=X) f)

class VecStruct (K X I XI) [StructType X I XI] [RCLike K]
    [AddCommGroup X] [Module K X] [TopologicalSpace X]
    [∀ i, AddCommGroup (XI i)] [∀ i, Module K (XI i)] [∀ i, TopologicalSpace (XI i)] : Prop
  extends TopologicalStruct X I XI, ModuleStruct K X I XI


--------------------------------------------------------------------------------
-- ZeroStruct instances ---------------------------------------------------------
--------------------------------------------------------------------------------

instance instZeroStructDefault
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

instance instAddStructDefault
  {X} [Add X] : AddStruct X Unit (fun _ => X) where
  structProj_add := by simp[structProj]

instance instAddStructProd
  [Add E] [Add F] [∀ i, Add (EI i)] [∀ j, Add (FJ j)]
  [AddStruct E I EI] [AddStruct F J FJ]
  : AddStruct (E×F) (I⊕J) (Sum.rec EI FJ) where
  structProj_add := by simp[structProj, AddStruct.structProj_add]


--------------------------------------------------------------------------------
-- NegStruct instances ---------------------------------------------------------
--------------------------------------------------------------------------------

instance instNegStructDefault
  {X} [Neg X] : NegStruct X Unit (fun _ => X) where
  structProj_neg := by simp[structProj]

instance instNegStructProd
  [Neg E] [Neg F] [∀ i, Neg (EI i)] [∀ j, Neg (FJ j)]
  [NegStruct E I EI] [NegStruct F J FJ]
  : NegStruct (E×F) (I⊕J) (Sum.rec EI FJ) where
  structProj_neg := by simp[structProj, NegStruct.structProj_neg]


--------------------------------------------------------------------------------
-- SMulStruct instances ---------------------------------------------------------
--------------------------------------------------------------------------------

instance instSMulStructDefault
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

instance instTopologicalStructDefault
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

instance instModuleStructDefault
  {X} [AddCommGroup X] [Module K X] : ModuleStruct K X Unit (fun _ => X) where

instance instModuleStructProd
  [AddCommGroup E] [Module K E] [∀ i, AddCommGroup (EI i)] [∀ i, Module K (EI i)] [ModuleStruct K E I EI]
  [AddCommGroup F] [Module K F] [∀ j, AddCommGroup (FJ j)] [∀ j, Module K (FJ j)] [ModuleStruct K F J FJ]
  : ModuleStruct K (E×F) (I⊕J) (Sum.rec EI FJ) where


--------------------------------------------------------------------------------
-- VecStruct instances ---------------------------------------------------------
--------------------------------------------------------------------------------

instance instVecStructDefault
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

section OnGroup

set_option deprecated.oldSectionVars true

variable
  {X : Type _} [AddCommGroup X]
  {XI : I → Type _} [∀ i, AddCommGroup (XI i)]
  [StructType X I XI] [addInst : AddStruct X I XI] [negInst : NegStruct X I XI]

  def_fun_prop with_transitive (i : I) : IsAddGroupHom fun (x : X) => structProj x i by
    constructor
    · apply AddStruct.structProj_add
    · apply NegStruct.structProj_neg

  def_fun_prop with_transitive : IsAddGroupHom fun (f : (i : I) → XI i) => structMake (X:=X) f by
    constructor
    · intros; apply structExt (I:=I) (XI:=XI); intro i; rw[AddStruct.structProj_add (self:=addInst)]; simp
    · intros; apply structExt (I:=I) (XI:=XI); intro i; rw[NegStruct.structProj_neg (self:=negInst)]; simp

  def_fun_prop with_transitive (i : I) : IsAddGroupHom fun (xi : XI i) => oneHot (X:=X) i xi by
    constructor
    · intros; apply structExt (I:=I) (XI:=XI); intro i; rw[AddStruct.structProj_add (self:=addInst)]; simp[oneHot]; aesop
    · intros; apply structExt (I:=I) (XI:=XI); intro i; rw[NegStruct.structProj_neg (self:=negInst)]; simp[oneHot]; aesop

  #generate_add_group_hom_simps structProj.arg_x.IsAddGroupHom_rule
  #generate_add_group_hom_simps structMake.arg_f.IsAddGroupHom_rule
  #generate_add_group_hom_simps oneHot.arg_xi.IsAddGroupHom_rule

  attribute [simp, simp_core]
    structProj.arg_x.add_pull
    structProj.arg_x.sub_pull
    structProj.arg_x.neg_pull

  attribute [simp, simp_core]
    structMake.arg_f.add_push
    structMake.arg_f.sub_push
    structMake.arg_f.neg_push

  @[simp, simp_core]
  theorem structMake.arg_f.app_zero' :
      structMake (X:=X) (fun i : I => 0) = 0 := structMake.arg_f.app_zero

  attribute [simp, simp_core]
    oneHot.arg_xi.add_push
    oneHot.arg_xi.sub_push
    oneHot.arg_xi.neg_push

end OnGroup


section OnModule
variable
  {X : Type _} [AddCommGroup X] [Module K X]
  {XI : I → Type _} [∀ i, AddCommGroup (XI i)] [∀ i, Module K (XI i)]
  [StructType X I XI] [inst : ModuleStruct K X I XI]

  def_fun_prop with_transitive (i : I) : IsLinearMap K fun (x : X) => structProj x i by
    constructor
    · apply AddStruct.structProj_add
    · apply SMulStruct.structProj_smul

  def_fun_prop with_transitive : IsLinearMap K fun (f : (i : I) → XI i) => structMake (X:=X) f by
    constructor
    · intros; apply structExt (I:=I) (XI:=XI); intro i; rw[AddStruct.structProj_add (self:=inst.toAddStruct)]; simp
    · intros; apply structExt (I:=I) (XI:=XI); intro i; rw[SMulStruct.structProj_smul (self:=inst.toSMulStruct)]; simp

  def_fun_prop with_transitive (i : I) : IsLinearMap K fun (xi : XI i) => oneHot (X:=X) i xi by
    constructor
    · intros; apply structExt (I:=I) (XI:=XI); intro i; rw[AddStruct.structProj_add (self:=inst.toAddStruct)]; simp[oneHot]; aesop
    · intros; apply structExt (I:=I) (XI:=XI); intro i; rw[SMulStruct.structProj_smul (self:=inst.toSMulStruct)]; simp[oneHot]; aesop

  #generate_linear_map_simps structProj.arg_x.IsLinearMap_rule
  #generate_linear_map_simps structMake.arg_f.IsLinearMap_rule
  #generate_linear_map_simps oneHot.arg_xi.IsLinearMap_rule

  attribute [simp, simp_core]
    structProj.arg_x.smul_pull

  attribute [simp, simp_core]
    structMake.arg_f.smul_push

  attribute [simp, simp_core]
    oneHot.arg_xi.smul_push

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
    · apply TopologicalStruct.structProj_continuous

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


end StructType




--------------------------------------------------------------------------------
-- AdjointSpaceStruct -------------------------------------------------
--------------------------------------------------------------------------------

open StructType in
class AdjointSpaceStruct (K X I XI) [StructType X I XI] [RCLike K] [IndexType I NI]
    [NormedAddCommGroup X] [AdjointSpace K X] [∀ i, NormedAddCommGroup (XI i)] [∀ i, AdjointSpace K (XI i)] : Prop
  extends
    VecStruct K X I XI
  where
    inner_structProj : ∀ (x x' : X), ⟪x,x'⟫[K] = ∑ (i : I), ⟪structProj x i, structProj x' i⟫[K]


--------------------------------------------------------------------------------
-- AdjointSpaceStruct instances ---------------------------------------
--------------------------------------------------------------------------------

instance {X} [NormedAddCommGroup X] [AdjointSpace K X] :
    AdjointSpaceStruct K X Unit (fun _ => X) where
  inner_structProj := sorry_proof


instance
  [NormedAddCommGroup E] [AdjointSpace K E] [NormedAddCommGroup F] [AdjointSpace K F]
  [∀ i, NormedAddCommGroup (EI i)] [∀ j, NormedAddCommGroup (FJ j)] [∀ i, AdjointSpace K (EI i)] [∀ j, AdjointSpace K (FJ j)]
  [IndexType I NI] [IndexType J NJ]
  [AdjointSpaceStruct K E I EI] [AdjointSpaceStruct K F J FJ] :
  AdjointSpaceStruct K (E×F) (I⊕J) (Sum.rec EI FJ) := sorry_proof
  -- inner_structProj := sorry_proof
  -- testFun_structProj := sorry_proof

omit [DecidableEq I] in
@[simp, simp_core]
theorem inner_oneHot_eq_inner_structProj'' [StructType X I XI] [IndexType I NI] [DecidableEq I]
    [∀ i, NormedAddCommGroup (XI i)] [∀ i, AdjointSpace K (XI i)] [NormedAddCommGroup X] [AdjointSpace K X]
    [AdjointSpaceStruct K X I XI] (i : I) (xi : XI i) (x : X) :
    ⟪x, oneHot i xi⟫[K] = ⟪structProj x i, xi⟫[K] := sorry_proof


omit [DecidableEq I] in
@[simp, simp_core]
theorem inner_oneHot_eq_inner_proj''' [StructType X I XI] [IndexType I NI] [DecidableEq I]
    [∀ i, NormedAddCommGroup (XI i)] [∀ i, AdjointSpace K (XI i)] [NormedAddCommGroup X] [AdjointSpace K X]
    [AdjointSpaceStruct K X I XI] (i : I) (xi : XI i) (x : X) :
    ⟪oneHot i xi, x⟫[K] = ⟪xi, structProj x i⟫[K] := sorry_proof



--------------------------------------------------------------------------------
-- Prod simp lemmas
-- TODO: move somewhere else
--------------------------------------------------------------------------------

section OneHotSimp

set_option deprecated.oldSectionVars true

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
