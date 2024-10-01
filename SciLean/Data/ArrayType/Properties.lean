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

-- TODO: add Differentiable, ContDiff for `modify` function

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
    fun e : Elem => oneHot (i,()) e := by sorry_proof

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


@[fun_trans]
theorem ArrayType.ofFn.arg_f.revFDerivProj_rule_unit_simple :
    revFDerivProj K Unit (fun f : Idx → Elem => ArrayType.ofFn f)
    =
    fun f =>
      (ArrayType.ofFn (Cont:=Cont) f, fun _ (dx : Cont) i => ArrayType.get dx i) := by
  unfold revFDerivProj; fun_trans[oneHot]


-- maybe this should be in compositional form
@[fun_trans]
theorem ArrayType.ofFn.arg_f.revFDerivProj_rule_simple :
    revFDerivProj K (Idx×I) (fun f : Idx → Elem => ArrayType.ofFn (Cont:=Cont) f)
    =
    fun f =>
      (ArrayType.ofFn (Cont:=Cont) f, fun (i,j) dei i' => if i = i' then oneHot j dei else 0) := by
  unfold revFDerivProj; fun_trans[oneHot]
  funext x; simp; funext (i,j) dei i'
  apply structExt (I:=I); intro j'
  split_ifs <;> aesop

@[fun_trans]
theorem ArrayType.ofFn.arg_f.revFDerivProjUpdate_rule_unit_simple :
    revFDerivProjUpdate K Unit (fun f : Idx → Elem => ArrayType.ofFn f)
    =
    fun f =>
      (ArrayType.ofFn (Cont:=Cont) f, fun _ (dx : Cont) df i => df i + ArrayType.get dx i) := by
  unfold revFDerivProjUpdate; fun_trans[oneHot]
  funext x; simp; funext _ de dx i; simp


@[fun_trans]
theorem ArrayType.ofFn.arg_f.revFDerivProjUpdate_rule_simple :
    revFDerivProjUpdate K (Idx×I) (fun f : Idx → Elem => ArrayType.ofFn (Cont:=Cont) f)
    =
    fun f =>
      (ArrayType.ofFn (Cont:=Cont) f,
       fun (i,j) dej df i' => if i=i' then structModify j (fun ej => ej + dej) (df i') else df i') := by
  unfold revFDerivProjUpdate; fun_trans[oneHot]
  funext x; simp; funext (i,j) de dx i'; simp
  apply structExt (I:=I); intro j'
  split_ifs <;> aesop




end OnAdjointSpace
