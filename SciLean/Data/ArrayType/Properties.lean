-- import SciLean.Core.FunctionPropositions
-- import SciLean.Core.FunctionTransformations
import SciLean.Data.ArrayType.Algebra
import SciLean.Analysis.Convenient.HasAdjDiff
import SciLean.Analysis.AdjointSpace.Adjoint
import SciLean.Analysis.Calculus.RevFDerivProj

import SciLean.Meta.GenerateAddGroupHomSimp

namespace SciLean

set_option linter.unusedVariables false
set_option linter.hashCommand false


section GenericArrayType

set_option deprecated.oldSectionVars true

variable
  {K : Type} [RCLike K]
  {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam}
  [ArrayType Cont Idx Elem] [IndexType Idx] [DecidableEq Idx]


-- Indexed.get -----------------------------------------------------------------
--------------------------------------------------------------------------------

section OnModule
open ArrayType

variable {R : Type} [CommSemiring R] [AddCommGroup Elem] [Module R Elem]
  {W : Type} [AddCommGroup W] [Module R W]

def_fun_prop with_transitive (i : Idx) : IsAddGroupHom (fun xs : Cont => ArrayType.get xs i) by
  constructor <;> simp

def_fun_prop with_transitive : IsAddGroupHom (fun f : Idx → Elem => ArrayType.ofFn (Cont:=Cont) f) by
  constructor <;> (intros; apply ArrayType.ext (Idx:=Idx); simp)

def_fun_prop with_transitive (i : Idx) :
    IsAddGroupHom (fun (x : Cont×Elem) => ArrayType.set x.1 i x.2) by
  constructor
  · intros; apply ArrayType.ext (Idx:=Idx); intro j; simp
    if h : i = j then simp[h,ArrayType.get_set_eq] else simp[h,ArrayType.get_set_neq]
  · intros; apply ArrayType.ext (Idx:=Idx); intro j; simp
    if h : i = j then simp[h,ArrayType.get_set_eq] else simp[h,ArrayType.get_set_neq]


#generate_add_group_hom_simps ArrayType.get.arg_cont.IsAddGroupHom_rule
#generate_add_group_hom_simps ArrayType.ofFn.arg_f.IsAddGroupHom_rule
-- todo: there is some unification issue here
-- #generate_add_group_hom_simps ArrayType.set.arg_contxi.IsAddGroupHom_rule

@[fun_prop]
theorem ArrayType.modify.arg_contf.IsAddGroupHom_rule
    (cont : W → Cont) (hcont : IsAddGroupHom cont) (i : Idx)
    (f : W → Elem → Elem) (hf : IsAddGroupHom (fun (w,x) => f w x)) :
    IsAddGroupHom (fun w => ArrayType.modify (cont w) i (f w)) := by
  constructor
  · intros; apply ArrayType.ext (Idx:=Idx); intro j; simp
    if h : i = j then
      simp [h,hcont.map_add]; sorry_proof
    else
      simp[h,ArrayType.get_set_neq,hcont.map_add]
  · intros; apply ArrayType.ext (Idx:=Idx); intro j; simp
    if h : i = j then
      simp [h,hcont.map_neg]; sorry_proof
    else
      simp[h,ArrayType.get_set_neq,hcont.map_neg]


def_fun_prop with_transitive (i : Idx) : IsLinearMap R (fun xs : Cont => ArrayType.get xs i) by
  constructor <;> simp

def_fun_prop with_transitive : IsLinearMap R (fun f : Idx → Elem => ArrayType.ofFn (Cont:=Cont) f) by
  constructor <;> (intros; apply ArrayType.ext (Idx:=Idx); simp)

def_fun_prop with_transitive (i : Idx) :
    IsLinearMap R (fun (x : Cont×Elem) => ArrayType.set x.1 i x.2) by
  constructor
  · intros; apply ArrayType.ext (Idx:=Idx); intro j; simp
    if h : i = j then simp[h,ArrayType.get_set_eq] else simp[h,ArrayType.get_set_neq]
  · intros; apply ArrayType.ext (Idx:=Idx); intro j; simp
    if h : i = j then simp[h,ArrayType.get_set_eq] else simp[h,ArrayType.get_set_neq]


#generate_linear_map_simps ArrayType.get.arg_cont.IsLinearMap_rule
#generate_linear_map_simps ArrayType.ofFn.arg_f.IsLinearMap_rule
-- TODO: fix unification issue
-- #generate_linear_map_simps ArrayType.set.arg_contxi.IsLinearMap_rule

@[fun_prop]
theorem ArrayType.modify.arg_contf.IsLinearMap_rule
    (cont : W → Cont) (hcont : IsLinearMap R cont) (i : Idx)
    (f : W → Elem → Elem) (hf : IsLinearMap R (fun (w,x) => f w x)) :
    IsLinearMap R (fun w => ArrayType.modify (cont w) i (f w)) := by
  constructor
  · intros; apply ArrayType.ext (Idx:=Idx); intro j; simp
    if h : i = j then
      simp [h,hcont.map_add]; sorry_proof
    else
      simp[h,ArrayType.get_set_neq,hcont.map_add]
  · intros; apply ArrayType.ext (Idx:=Idx); intro j; simp
    if h : i = j then
      simp [h,hcont.map_smul]; sorry_proof
    else
      simp[h,ArrayType.get_set_neq,hcont.map_smul]

end OnModule

section OnTopologicalSpace

variable [TopologicalSpace Elem]
  {W : Type} [TopologicalSpace W]

def_fun_prop with_transitive (i : Idx) :
   Continuous (fun xs : Cont => ArrayType.get xs i) by sorry_proof

def_fun_prop with_transitive :
   Continuous (fun f : Idx → Elem => ArrayType.ofFn (Cont:=Cont) f) by sorry_proof

def_fun_prop with_transitive (i : Idx) :
   Continuous (fun (x : Cont×Elem) => ArrayType.set x.1 i x.2) by sorry_proof

@[fun_prop]
theorem ArrayType.modify.arg_contf.Continuous_rule
    (cont : W → Cont) (hcont : Continuous cont) (i : Idx)
    (f : W → Elem → Elem) (hf : Continuous (fun (w,x) => f w x)) :
    Continuous (fun w => ArrayType.modify (cont w) i (f w)) := by sorry_proof

end OnTopologicalSpace


section OnNormedSpaces

variable [NormedAddCommGroup Elem] [NormedSpace K Elem]
  {W : Type} [NormedAddCommGroup W] [NormedSpace K W]

def_fun_prop with_transitive (i : Idx) :
    IsContinuousLinearMap K (fun xs : Cont => ArrayType.get xs i) by
  constructor; fun_prop; simp[autoParam]; fun_prop

def_fun_prop with_transitive :
    IsContinuousLinearMap K (fun f : Idx → Elem => ArrayType.ofFn (Cont:=Cont) f) by
  constructor; fun_prop; simp[autoParam]; fun_prop

def_fun_prop with_transitive (i : Idx) :
    IsContinuousLinearMap K (fun (x : Cont×Elem) => ArrayType.set x.1 i x.2) by
  constructor; fun_prop; simp[autoParam]; fun_prop

@[fun_prop]
theorem ArrayType.modify.arg_contf.IsContinuousLinearMap_rule
    (cont : W → Cont) (hcont : IsContinuousLinearMap K cont) (i : Idx)
    (f : W → Elem → Elem) (hf : IsContinuousLinearMap K (fun (w,x) => f w x)) :
    IsContinuousLinearMap K (fun w => ArrayType.modify (cont w) i (f w)) := by
  -- set_option trace.Meta.isDefEq true in
  constructor; fun_prop; simp[autoParam]
  -- todo: fix fun_prop such that it can postpone type class arguments
  --       bacause of this reason it can't apply `IsContinuousLinearMap.continuous`
  sorry_proof

end OnNormedSpaces

section OnVec

variable
  [Vec K Elem]
  {W : Type} [Vec K W]

def_fun_prop with_transitive (i : Idx) :
    IsSmoothLinearMap K (fun xs : Cont => ArrayType.get xs i) by
  constructor; fun_prop; sorry_proof

def_fun_prop with_transitive :
    IsSmoothLinearMap K (fun f : Idx → Elem => ArrayType.ofFn (Cont:=Cont) f) by
  constructor; fun_prop; sorry_proof

def_fun_prop with_transitive (i : Idx) :
    IsSmoothLinearMap K (fun (x : Cont×Elem) => ArrayType.set x.1 i x.2) by
  constructor; fun_prop; sorry_proof

@[fun_prop]
theorem ArrayType.modify.arg_contf.IsSmoothLinearMap_rule
    (cont : W → Cont) (hcont : IsSmoothLinearMap K cont) (i : Idx)
    (f : W → Elem → Elem) (hf : IsSmoothLinearMap K (fun (w,x) => f w x)) :
    IsSmoothLinearMap K (fun w => ArrayType.modify (cont w) i (f w)) := by
  constructor; fun_prop; sorry_proof

end OnVec

section OnSemiInnerProductSpace

variable
  [SemiInnerProductSpace K Elem]
  {W : Type} [SemiInnerProductSpace K W]

def_fun_prop with_transitive (i : Idx) :
    HasSemiAdjoint K (fun xs : Cont => ArrayType.get xs i) by sorry_proof

def_fun_prop with_transitive :
    HasSemiAdjoint K (fun f : Idx → Elem => ArrayType.ofFn (Cont:=Cont) f) by sorry_proof

def_fun_prop with_transitive (i : Idx) :
    HasSemiAdjoint K (fun (x : Cont×Elem) => ArrayType.set x.1 i x.2) by sorry_proof

@[fun_prop]
theorem ArrayType.modify.arg_contf.HasSemiAdjoint_rule
    (cont : W → Cont) (hcont : HasSemiAdjoint K cont) (i : Idx)
    (f : W → Elem → Elem) (hf : HasSemiAdjoint K (fun (w,x) => f w x)) :
    HasSemiAdjoint K (fun w => ArrayType.modify (cont w) i (f w)) := by sorry_proof

end OnSemiInnerProductSpace

section OnAdjointSpace

variable
  [NormedAddCommGroup Elem] [AdjointSpace K Elem] [CompleteSpace Elem]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace K W] [CompleteSpace W]

@[fun_trans]
theorem ArrayType.get.arg_cont.adjoint_rule (i : Idx) :
    adjoint K (fun c : Cont => ArrayType.get c i)
    =
    fun e : Elem => oneHot i e := by sorry_proof

@[fun_trans]
theorem ArrayType.set.arg_cont.adjoint_rule (i : Idx) :
    adjoint K (fun c : Cont => ArrayType.set c i 0)
    =
    fun c => ArrayType.set c i 0 := by sorry_proof

@[fun_trans]
theorem ArrayType.set.arg_xi.adjoint_rule (i : Idx) :
    adjoint K (fun xi : Elem => ArrayType.set (0:Cont) i xi)
    =
    fun c => ArrayType.get c i := by sorry_proof

@[fun_trans]
theorem ArrayType.set.arg_contxi.adjoint_rule (i : Idx) :
    adjoint K (fun cx : Cont×Elem => ArrayType.set cx.1 i cx.2)
    =
    fun c => (ArrayType.set c i (0:Elem), ArrayType.get c i) := by sorry_proof

@[fun_trans]
theorem ArrayType.ofFn.arg_f.adjoint_rule :
    adjoint K (fun f : Idx → Elem => ArrayType.ofFn (Cont:=Cont) f)
    =
    fun c i => ArrayType.get c i := by sorry_proof

end OnAdjointSpace


section OnAdjointSpace

variable
  [NormedAddCommGroup Elem] [AdjointSpace K Elem] [CompleteSpace Elem]
  {I : Type} [IndexType I] [DecidableEq I]
  {E : I → Type} [∀ i, NormedAddCommGroup (E i)] [∀ i, AdjointSpace K (E i)]
  [∀ i, CompleteSpace (E i)] [StructType Elem I E] [VecStruct K Elem I E]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace K W] [CompleteSpace W]


@[fun_trans]
theorem ArrayType.get.arg_cont.revFDerivProj_rule (i : Idx)
    (cont : W → Cont) (hf : Differentiable K cont) :
    revFDerivProj K I (fun w => ArrayType.get (cont w) i)
    =
    fun w : W =>
      let xi := revFDerivProj K (Idx×I) cont w
      (ArrayType.get xi.1 i, fun (j : I) (de : E j) =>
        xi.2 (i,j) de) := by
  unfold revFDerivProj; fun_trans[oneHot]
  funext x
  fun_trans
  funext i de
  congr
  funext i
  split_ifs
  · congr; funext i; aesop
  · aesop


@[fun_trans]
theorem ArrayType.get.arg_cont.revFDerivProjUpdate_rule (i : Idx)
    (cont : W → Cont) (hf : Differentiable K cont) :
    revFDerivProjUpdate K I (fun w => ArrayType.get (cont w) i)
    =
    fun w : W =>
      let xi := revFDerivProjUpdate K (Idx×I) cont w
      (ArrayType.get xi.1 i, fun (j : I) (de : E j) dw =>
        xi.2 (i,j) de dw) := by unfold revFDerivProjUpdate; fun_trans


end OnAdjointSpace


#exit

@[fun_trans]
theorem ArrayType.get.arg_cont.semiAdjoint_rule_simple (idx : Idx) :
    semiAdjoint K (fun cont : Cont => get cont idx)
    =
    fun elem => oneHot (X:=Cont) idx elem :=
by
  sorry_proof

@[fun_trans]
theorem ArrayType.get.arg_cont.revCDeriv_rule
  (f : X → Cont) (idx : Idx)
  (hf : HasAdjDiff K f)
  : revDeriv K (fun x => (f x)[idx])
    =
    fun x =>
      let ydf := revDerivProj K Idx f x
      (ydf.1[idx],
       fun delem => ydf.2 idx delem) :=
by
  unfold revDeriv;
  conv =>
    lhs; fun_trans; fun_trans; simp
  rfl

@[fun_trans]
theorem GetElem.getElem.arg_cont.revCDerivUpdate_rule
  (f : X → Cont) (idx : Idx)
  (hf : HasAdjDiff K f)
  : revDerivUpdate K (fun x => (f x)[idx])
    =
    fun x =>
      let ydf := revDerivProjUpdate K Idx f x
      (ydf.1[idx],
       fun delem dx => ydf.2 idx delem dx) :=
by
  unfold revDerivUpdate;
  conv =>
    lhs; fun_trans; fun_trans; simp
  rfl

@[fun_trans]
theorem GetElem.getElem.arg_cont.revCDerivProj_rule
  {J ElemJ} [StructType Elem J ElemJ] [IndexType J] [DecidableEq J]
  [∀ j, SemiInnerProductSpace K (ElemJ j)] [SemiInnerProductSpaceStruct K Elem J ElemJ]
  (f : X → Cont) (idx : Idx)
  (hf : HasAdjDiff K f)
  : revDerivProj K J (fun x => (f x)[idx])
    =
    fun x =>
      let ydf := revDerivProj K (Idx×J) f x
      (ydf.1[idx],
       fun j delem => ydf.2 (idx,j) delem) :=
by
  unfold revDerivProj
  conv =>
    lhs; fun_trans; fun_trans; simp
  funext x; simp[revDerivProj]
  funext j de
  simp [revDeriv]
  congr
  sorry_proof

end OnSemiInnerProductSpace


-- Indexed.set ----------------------------------------------------------------
--------------------------------------------------------------------------------

section OnVectorSpaces

variable {R : Type} [CommSemiring R] [AddCommGroup Elem] [Module R Elem]

@[fun_prop]
theorem ArrayType.set.arg_contelem.IsLinearMap_rule_simple (idx : Idx) :
    IsLinearMap R (fun ((cont,elem) : Cont×Elem) => Indexed.set cont idx elem) := by
  constructor
  · intros; simp; ext; sorry_proof
  · intros; simp; ext; sorry_proof

#generate_linear_map_simps ArrayType.set.arg_contelem.IsLinearMap_rule_simple

end OnVectorSpaces

section OnNormedSpaces

variable
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  [NormedAddCommGroup Elem] [NormedSpace K Elem]

@[fun_prop]
theorem LeanColls.Indexed.set.arg_contelem.IsContinuousLinearMap_rule_simple :
    IsContinuousLinearMap K (fun ((cont,elem) : Cont×Elem) => Indexed.set cont idx elem) :=
  sorry_proof

-- automatically infer: Differentiable, DifferentiableAt, ContDiff, fderiv, fwdFDeriv

end OnNormedSpaces

section OnVec

variable
  {X : Type} [Vec K X]
  [Vec K Elem]

@[fun_prop]
theorem LeanColls.Indexed.set.arg_contelem.IsSmoothLinearMap_rule_simple (idx : Idx) :
    IsSmoothLinearMap K (fun ((cont,elem) : Cont×Elem) => Indexed.set cont idx elem) := sorry_proof

-- automatically infer: CDifferentiable, CDifferentiableAt, CContDiff, cderiv, fwdDeriv

end OnVec

section OnSemiInnerProductSpace

variable
  {X : Type} [SemiInnerProductSpace K X]
  [SemiInnerProductSpace K Elem]

@[fun_prop]
theorem LeanColls.Indexed.set.arg_cont.HasSemiAdjoint_rule_simple (idx : Idx) :
    HasSemiAdjoint K (fun ((cont,elem) : Cont×Elem) => Indexed.set cont idx elem) := sorry_proof

@[fun_trans]
theorem LeanColls.Indexed.set.arg_cont.semiAdjoint_rule_simple (idx : Idx) :
    semiAdjoint K (fun ((cont,elem) : Cont×Elem) => Indexed.set cont idx elem)
    =
    fun cont' : Cont => (Indexed.set cont' idx 0, cont'[idx]) := sorry_proof

@[fun_trans]
theorem LeanColls.Indexed.set.arg_contelem.revCDeriv_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : revDeriv K (fun x => Indexed.set (cont x) idx (elem x))
    =
    fun x =>
      let cdc := revDeriv K cont x
      let ede := revDerivUpdate K elem x
      (Indexed.set cdc.1 idx ede.1,
       fun dc : Cont =>
         let dci := dc[idx]
         let dc := Indexed.set dc idx 0
         ede.2 dci (cdc.2 dc)) := by
  unfold revDeriv;
  conv =>
    lhs; fun_trans; fun_trans; simp
  rfl

@[fun_trans]
theorem LeanColls.Indexed.set.arg_contelem.revCDerivUpdate_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : revDerivUpdate K (fun x => Indexed.set (cont x) idx (elem x))
    =
    fun x =>
      let cdc := revDerivUpdate K cont x
      let ede := revDerivUpdate K elem x
      (Indexed.set cdc.1 idx ede.1,
       fun (dc : Cont) dx =>
         let dci := dc[idx]
         let dc := Indexed.set dc idx 0
         ede.2 dci (cdc.2 dc dx)) := by
  unfold revDerivUpdate
  conv =>
    lhs; fun_trans; fun_trans; simp
  simp[revDerivUpdate,add_assoc]


-- Consider formulating variant for index type `Idx×J`
@[fun_trans]
theorem LeanColls.Indexed.set.arg_contelem.revCDerivProj_rule
    (cont : X → Cont) (idx : Idx) (elem : X → Elem)
    (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem) :
    revDerivProj K Idx (fun x => Indexed.set (cont x) idx (elem x))
    =
    fun x =>
      let cdc := revDerivProj K Idx cont x
      let ede := revDeriv K elem x
      (Indexed.set cdc.1 idx ede.1,
       fun i delem =>
         if i = idx then
           ede.2 delem
         else
           cdc.2 i delem) :=
by
  unfold revDerivProj
  conv =>
    lhs; fun_trans; fun_trans; simp
  funext x; simp[revDerivProj,revDerivUpdate]
  funext i de
  if h : i = idx then
    simp [revDeriv,h,oneHot]
    sorry_proof
  else
    simp [revDeriv,h,oneHot]
    sorry_proof

-- Consider formulating variant for index type `Idx×J`
@[fun_trans]
theorem LeanColls.Indexed.set.arg_contelem.revCDerivProjUpdate_rule
    (cont : X → Cont) (idx : Idx) (elem : X → Elem)
    (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem) :
    revDerivProjUpdate K Idx (fun x => Indexed.set (cont x) idx (elem x))
    =
    fun x =>
      let cdc := revDerivProjUpdate K Idx cont x
      let ede := revDerivUpdate K elem x
      (Indexed.set cdc.1 idx ede.1,
       fun i delem dx =>
         if i = idx then
           ede.2 delem dx
         else
           cdc.2 i delem dx) :=
by
  unfold revDerivProjUpdate
  conv =>
    lhs; fun_trans; fun_trans; simp
  funext x; simp[revDerivProj,revDerivUpdate]
  funext i de
  if h : i = idx then
    simp [h]
  else
    simp [h]


end OnSemiInnerProductSpace


-- LeanColls.Indexed.ofFn -------------------------------------------------------------
--------------------------------------------------------------------------------

section OnVectorSpaces

variable {R : Type} [CommSemiring R] [AddCommGroup Elem] [Module R Elem]

@[fun_prop]
theorem LeanColls.Indexed.ofFn.arg_f.IsLinearMap_rule_simple :
    IsLinearMap R (fun f : Idx → Elem => Indexed.ofFn (C:=Cont) f) := by
  constructor
  · intros; ext; simp
  · intros; ext; simp

#generate_linear_map_simps LeanColls.Indexed.ofFn.arg_f.IsLinearMap_rule_simple

end OnVectorSpaces

section OnNormedSpaces

variable
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  [NormedAddCommGroup Elem] [NormedSpace K Elem]

@[fun_prop]
theorem LeanColls.Indexed.ofFn.arg_f.IsContinuousLinearMap_rule_simple :
    IsContinuousLinearMap K (fun f : Idx → Elem => Indexed.ofFn (C:=Cont) f) := sorry_proof

-- automatically infer: Differentiable, DifferentiableAt, ContDiff, fderiv, fwdFDeriv

end OnNormedSpaces

section OnVec

variable
  {X : Type} [Vec K X]
  [Vec K Elem]

@[fun_prop]
theorem LeanColls.Indexed.ofFn.arg_f.IsSmoothLinearMap_rule_simple
  (idx : Idx)
  : IsSmoothLinearMap K (fun f : Idx → Elem => Indexed.ofFn (C:=Cont) f) := sorry_proof

-- automatically infer: CDifferentiable, CDifferentiableAt, CContDiff, cderiv, fwdDeriv

end OnVec

section OnSemiInnerProductSpace

variable
  {X : Type} [SemiInnerProductSpace K X]
  [SemiInnerProductSpace K Elem]

@[fun_prop]
theorem LeanColls.Indexed.ofFn.arg_cont.HasSemiAdjoint_rule_simple :
    HasSemiAdjoint K (fun f : Idx → Elem => Indexed.ofFn (C:=Cont) f) := sorry_proof

@[fun_trans]
theorem LeanColls.Indexed.ofFn.arg_cont.semiAdjoint_rule_simple :
    semiAdjoint K (fun f : Idx → Elem => Indexed.ofFn (C:=Cont) f)
    =
    fun (cont : Cont) idx => cont[idx] :=
by
  sorry_proof

@[fun_trans]
theorem LeanColls.Indexed.ofFn.arg_cont.revCDeriv_rule
    (f : X → Idx → Elem) (hf : HasAdjDiff K f) :
    revDeriv K (fun x => Indexed.ofFn (C:=Cont) (f x))
    =
    fun x =>
      let fdf := revDeriv K f x
      (Indexed.ofFn fdf.1,
       fun dcont : Cont =>
         fdf.2 (fun idx => dcont[idx])) :=
by
  unfold revDeriv;
  conv => lhs; fun_trans; simp

@[fun_trans]
theorem LeanColls.Indexed.ofFn.arg_cont.revCDerivUpdate_rule
    (f : X → Idx → Elem) (hf : HasAdjDiff K f) :
    revDerivUpdate K (fun x => Indexed.ofFn (C:=Cont) (f x))
    =
    fun x =>
      let fdf := revDerivUpdate K f x
      (Indexed.ofFn fdf.1,
       fun (dcont : Cont) dx =>
         fdf.2 (fun idx => dcont[idx]) dx) :=
by
  unfold revDerivUpdate;
  conv => lhs; fun_trans; simp
  rfl

@[fun_trans]
theorem LeanColls.Indexed.ofFn.arg_cont.revCDerivProj_rule
    (f : X → Idx → Elem) (hf : HasAdjDiff K f) :
    revDerivProj K Idx (fun x => Indexed.ofFn (C:=Cont) (f x))
    =
    fun x =>
      let fdf := revDerivProj K Idx f x
      (Indexed.ofFn fdf.1,
       fdf.2) := by
  unfold revDerivProj;
  conv => lhs; fun_trans; simp
  funext x; simp[oneHot]

@[fun_trans]
theorem LeanColls.Indexed.ofFn.arg_cont.revCDerivProjUpdate_rule
    (f : X → Idx → Elem) (hf : HasAdjDiff K f) :
    revDerivProjUpdate K Idx (fun x => Indexed.ofFn (C:=Cont) (f x))
    =
    fun x =>
      let fdf := revDerivProjUpdate K Idx f x
      (Indexed.ofFn fdf.1,
       fdf.2) := by
  unfold revDerivProjUpdate;
  conv => lhs; fun_trans; simp
  rfl

end OnSemiInnerProductSpace



-- PushElem.pushElem -----------------------------------------------------------
--------------------------------------------------------------------------------


-- DropElem.dropElem -----------------------------------------------------------
--------------------------------------------------------------------------------


-- ReserveElem.reserveElem -----------------------------------------------------
--------------------------------------------------------------------------------


-- ArrayType.mapIdx ------------------------------------------------------------
--------------------------------------------------------------------------------


-- ArrayType.map ---------------------------------------------------------------
--------------------------------------------------------------------------------

-- section OnNormedSpaces

-- variable
--   {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
--   [NormedAddCommGroup Elem] [NormedSpace K Elem]

-- @[fun_prop]
-- theorem ArrayType.map.arg_a0.IsContinuousLinearMap_rule
--   (f : X → Elem → Elem) (arr : Cont)
--   (hf : IsContinuousLinearMap K f)
--   : IsContinuousLinearMap K (λ x => map (f x) arr) := sorry_proof

-- @[fun_prop]
-- theorem ArrayType.map.arg_arr.IsContinuousLinearMap_rule
--   (f : Elem → Elem) (arr : X → Cont)
--   (harr : IsContinuousLinearMap K arr)
--   : IsContinuousLinearMap K (λ x => map f (arr x)) := sorry_proof

-- @[fun_prop]
-- theorem ArrayType.map.arg_a0arr.Differentiable_rule
--   (f : X → Elem → Elem) (arr : X → Cont)
--   (hf : Differentiable K (fun (xe : X×Elem) => f xe.1 xe.2))
--   (harr : Differentiable K arr)
--   : Differentiable K (λ x => map (f x) (arr x)) := sorry_proof

-- @[fun_prop]
-- theorem ArrayType.map.arg_a0arr.DifferentiableAt_rule
--   (f : X → Elem → Elem) (arr : X → Cont) (x : X)
--   (hf : ∀ i, DifferentiableAt K (fun (xe : X×Elem) => f xe.1 xe.2) (x, (arr x)[i]))
--   (harr : DifferentiableAt K arr x)
--   : DifferentiableAt K (λ x => map (f x) (arr x)) x := sorry_proof

-- TODO: fderiv, fwdFDeriv, adjoint, revFDeriv

-- end OnNormedSpaces

-- namespace SciLean
-- section OnVec

-- variable
--   {X : Type _} [Vec K X]
--   [Vec K Elem]

-- @[fun_prop]
-- theorem ArrayType.map.arg_xs.IsDifferentiable_rule
--   (f : X → Cont) (idx : Idx) (dom)
--   (hf : IsDifferentiable K f)
--   : IsDifferentiable K (λ x => getElem (f x) idx dom) := sorry_proof

-- @[fun_prop]
-- theorem ArrayType.map.arg_xs.IsDifferentiableAt_rule
--   (f : X → Cont) (idx : Idx) (dom) (x : X)
--   (hf : IsDifferentiableAt K f x)
--   : IsDifferentiableAt K (λ x => getElem (f x) idx dom) x := sorry_proof

-- @[ftrans]
-- theorem ArrayType.map.arg_a0arr.cderiv_rule
--   (f : X → Elem → Elem) (arr : X → Cont)
--   (hf : IsDifferentiable K (fun (xe : X×Elem) => f xe.1 xe.2))
--   (harr : IsDifferentiable K arr)
--   : cderiv K (fun x => mapMono (f x) (arr x))
--     =
--     fun x dx =>
--       let a  := arr x
--       let da := cderiv K arr x dx
--       let df := cderiv K (fun (xe : X×Elem) => f xe.1 xe.2)
--       Indexed.ofFn (fun i => df (x,a[i]) (dx,da[i])) :=
-- by
--   sorry_proof

-- @[ftrans]
-- theorem ArrayType.map.arg_a0arr.cderiv_rule_at
--   (f : X → Elem → Elem) (arr : X → Cont)
--   (hf : ∀ i, IsDifferentiableAt K (fun (xe : X×Elem) => f xe.1 xe.2) (x, (arr x)[i]))
--   (harr : IsDifferentiableAt K arr x)
--   : cderiv K (fun x => mapMono (f x) (arr x)) x
--     =
--     fun dx =>
--       let a  := arr x
--       let da := cderiv K arr x dx
--       Indexed.ofFn (fun i =>
--         cderiv K (fun (xe : X×Elem) => f xe.1 xe.2) (x,a[i]) (dx,da[i])) :=
-- by
--   sorry_proof

-- @[ftrans]
-- theorem ArrayType.map.arg_xs.fwdCDeriv_rule
--   (f : X → Cont) (idx : Idx) (dom)
--   (hf : IsDifferentiable K f)
--   : fwdCDeriv K (fun x => getElem (f x) idx dom)
--     =
--     fun x dx =>
--       let ydy := fwdCDeriv K f x dx
--       (getElem ydy.1 idx dom, getElem ydy.2 idx dom) :=
-- by
--   sorry_proof

-- @[ftrans]
-- theorem ArrayType.map.arg_xs.fwdCDeriv_rule_at
--   (f : X → Cont) (idx : Idx) (dom) (x : X)
--   (hf : IsDifferentiableAt K f x)
--   : fwdCDeriv K (fun x => getElem (f x) idx dom) x
--     =
--     fun dx =>
--       let ydy := fwdCDeriv K f x dx
--       (getElem ydy.1 idx dom, getElem ydy.2 idx dom) :=
-- by
--   sorry_proof

-- end OnVec

-- section OnSemiInnerProductSpace

-- variable
--   {X : Type _} [SemiInnerProductSpace K X]
--   [SemiInnerProductSpace K Elem]

-- @[fun_prop]
-- theorem ArrayType.map.arg_a0arr.HasAdjDiff_rule
--   (f : X → Elem → Elem) (arr : X → Cont)
--   (hf : HasAdjDiff K (fun (xe : X×Elem) => f xe.1 xe.2)) (harr : HasAdjDiff K arr)
--   : HasAdjDiff K (fun x => mapMono (f x) (arr x)) := sorry_proof

-- @[ftrans]
-- theorem ArrayType.map.arg_a0arr.revDeriv_rule
--   (f : X → Elem → Elem) (arr : X → Cont)
--   (hf : HasAdjDiff K (fun (x,e) => f x e)) (harr : HasAdjDiff K arr)
--   : revDeriv K (fun x => mapMono (f x) (arr x))
--     =
--     fun x =>
--       let fdf := revDerivUpdate K (fun ((x,e) : X×Elem) => f x e)
--       let ada := revDerivUpdate K arr x
--       let a := ada.1
--       (map (f x) a,
--        fun da =>
--          let (dx,da) :=
--            Fold.fold
--              (IndexType.univ Idx)
--              (fun dxa (i : Idx) =>
--                let dxai := (fdf (x,a[i])).2 dxa.2[i] (dxa.1,0)
--                (dxai.1, Indexed.set dxa.2 i dxai.2))
--              ((0 : X),da)
--          ada.2 da dx) := sorry_proof


-- @[ftrans]
-- theorem ArrayType.map.arg_arr.revDeriv_rule
--   (f : Elem → Elem) (arr : X → Cont)
--   (hf : HasAdjDiff K f) (harr : HasAdjDiff K arr)
--   : revDeriv K (fun x => mapMono f (arr x))
--     =
--     fun x =>
--       let fdf := revDeriv K f
--       let ada := revDeriv K arr x
--       let a := ada.1
--       (mapMono f a,
--        fun da =>
--          let da := mapMonoIdx (fun i dai => (fdf a[i]).2 dai) da
--          ada.2 da) := sorry_proof


-- @[ftrans]
-- theorem ArrayType.map.arg_arr.revDerivUpdate_rule
--   (f : Elem → Elem) (arr : X → Cont)
--   (hf : HasAdjDiff K f) (harr : HasAdjDiff K arr)
--   : revDerivUpdate K (fun x => mapMono f (arr x))
--     =
--     fun x =>
--       let fdf := revDeriv K f
--       let ada := revDerivUpdate K arr x
--       let a := ada.1
--       (mapMono f a,
--        fun da dx =>
--          let da := mapMonoIdx (fun i dai => let df := (fdf a[i]).2; df dai) da
--          ada.2 da dx) := sorry_proof

--------------------------------------------------------------------------------

-- @[fun_prop]
-- theorem ArrayType.max.arg_cont.HasAdjDiff_rule
--   [LT Elem] [∀ x y : Elem, Decidable (x < y)] [Inhabited Idx]
--   (arr : X → Cont)
--   (hf : HasAdjDiff K arr) (hfalse : fun_propParam False)
--   : HasAdjDiff K (fun x => max (arr x)) := sorry_proof


-- @[ftrans]
-- theorem ArrayType.max.arg_arr.revDeriv_rule
--   [LT Elem] [∀ x y : Elem, Decidable (x < y)] [Inhabited Idx]
--   (arr : X → Cont)
--   (hf : HasAdjDiff K arr) (hfalse : fun_propParam False)
--   : revDeriv K (fun x => max (arr x))
--     =
--     fun x =>
--       let i := idxMax (arr x)
--       let fdf := revDerivProj K Idx arr x
--       (fdf.1[i], fun dei => fdf.2 i dei) := sorry_proof


-- @[ftrans]
-- theorem ArrayType.max.arg_arr.revDerivUpdate_rule
--   [LT Elem] [∀ x y : Elem, Decidable (x < y)] [Inhabited Idx]
--   (arr : X → Cont)
--   (hf : HasAdjDiff K arr) (hfalse : fun_propParam False)
--   : revDerivUpdate K (fun x => max (arr x))
--     =
--     fun x =>
--       let i := idxMax (arr x)
--       let fdf := revDerivProjUpdate K Idx arr x
--       (fdf.1[i], fun dei dx => fdf.2 i dei dx) := sorry_proof


-- @[ftrans]
-- theorem ArrayType.map.arg_a0arr.revDeriv_rule
--   (f : X → Elem → Elem) (arr : X → Cont)
--   (hf : HasAdjDiff K (fun (xe : X×Elem) => f xe.1 xe.2)) (harr : HasAdjDiff K arr)
--   : revDeriv K (fun x => mapMono (f x) (arr x))
--     =
--     fun x =>
--       let fdf := revDerivUpdate K (fun (x,e) => f x e)
--       let a := arr x
--       (map (f x) a,
--        fun da =>
--          Function.repeatIdx (init:=(0 : X)) fun i dx =>
--            let dai := da[i]
--            let ai := a[i]
--            ((fdf (x,ai)).2 dai (dx,0)).1) := sorry_proof

-- @[ftrans]
-- theorem ArrayType.map.arg_xs.semiAdjoint_rule
--   (f : X → Cont) (idx : Idx) (dom)
--   (hf : HasSemiAdjoint K f)
--   : semiAdjoint K (fun x => getElem (f x) idx dom)
--     =
--     fun elem =>
--       let cont : Cont := Indexed.ofFn fun i => if i=idx then elem else 0
--       semiAdjoint K f cont :=
-- by
--   sorry_proof

-- @[fun_prop]
-- theorem ArrayType.map.arg_xs.HasAdjDiff_rule
--   (f : X → Cont) (idx : Idx) (dom)
--   (hf : HasAdjDiff K f)
--   : HasAdjDiff K (fun x => getElem (f x) idx dom) := sorry_proof

-- @[ftrans]
-- theorem ArrayType.map.arg_xs.revCDeriv_rule
--   (f : X → Cont) (idx : Idx) (dom)
--   (hf : HasAdjDiff K f)
--   : revCDeriv K (fun x => getElem (f x) idx dom)
--     =
--     fun x =>
--       let ydf := revCDeriv K f x
--       (getElem ydf.1 idx dom,
--        fun delem =>
--          let dcont : Cont := Indexed.ofFn fun i => if i=idx then delem else 0
--          ydf.2 dcont) :=
-- by
--   have ⟨_,_⟩ := hf
--   unfold revCDeriv; ftrans; ftrans; simp

-- @[ftrans]
-- theorem ArrayType.map.arg_xs.revCDeriv_rule_at
--   (f : X → Cont) (idx : Idx) (dom) (x : X)
--   (hf : HasAdjDiffAt K f x)
--   : revCDeriv K (fun x => getElem (f x) idx dom) x
--     =
--     let ydf := revCDeriv K f x
--     (getElem ydf.1 idx dom,
--      fun delem =>
--        let dcont : Cont := Indexed.ofFn fun i => if i=idx then delem else 0
--        ydf.2 dcont) :=
-- by
--   have ⟨_,_⟩ := hf
--   unfold revCDeriv; ftrans; ftrans; simp

-- end OnSemiInnerProductSpace


-- ArrayType.split -------------------------------------------------------------
--------------------------------------------------------------------------------


-- ArrayType.append ------------------------------------------------------------
--------------------------------------------------------------------------------
