import SciLean.Core.FunctionPropositions
import SciLean.Core.FunctionTransformations
import SciLean.Data.ArrayType.Algebra


open SciLean

set_option linter.unusedVariables false

open LeanColls

section GenericArrayType

variable
  {K : Type} [IsROrC K]
  {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam}
  [ArrayType Cont Idx Elem] [IndexType Idx] [LawfulIndexType Idx] [DecidableEq Idx]

#exit

-- GetElem.getElem -------------------------------------------------------------
--------------------------------------------------------------------------------

section OnNormedSpaces

variable
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  [NormedAddCommGroup Elem] [NormedSpace K Elem]

-- @[fprop]
-- theorem GetElem.getElem.arg_xs.IsContinuousLinearMap_rule
--   (f : X → Cont) (idx : Idx) (dom)
--   (hf : IsContinuousLinearMap K f)
--   : IsContinuousLinearMap K (λ x => getElem (f x) idx dom) := sorry_proof

-- @[fprop]
-- theorem GetElem.getElem.arg_xs.Differentiable_rule
--   (f : X → Cont) (idx : Idx) (dom)
--   (hf : Differentiable K f)
--   : Differentiable K (λ x => getElem (f x) idx dom) := sorry_proof

-- @[fprop]
-- theorem GetElem.getElem.arg_xs.DifferentiableAt_rule
--   (f : X → Cont) (idx : Idx) (dom) (x : X)
--   (hf : DifferentiableAt K f x)
--   : DifferentiableAt K (λ x => getElem (f x) idx dom) x := sorry_proof

-- TODO: fderiv, fwdFDeriv, adjoint, revFDeriv

end OnNormedSpaces

section OnVec

variable
  {X : Type} [Vec K X]
  [Vec K Elem]

@[fprop]
theorem LeanColls.Indexed.get.arg_cont.IsLinearMap_rule_simple
  (idx : Idx)
  : IsLinearMap K (fun xs : Cont => xs[idx]) := sorry_proof

#generate_linear_map_simps LeanColls.Indexed.get.arg_cont.IsLinearMap_rule_simple

@[fprop]
theorem LeanColls.Indexed.get.arg_cont.IsDifferentiable_rule
  (f : X → Cont) (idx : Idx)
  (hf : IsDifferentiable K f)
  : IsDifferentiable K (λ x => (f x)[idx]) := sorry_proof

@[ftrans]
theorem LeanColls.Indexed.get.arg_cont.cderiv_rule
  (f : X → Cont) (idx : Idx)
  (hf : IsDifferentiable K f)
  : cderiv K (fun x => (f x)[idx])
    =
    fun x dx =>
      (cderiv K f x dx)[idx] :=
by
  sorry_proof

@[ftrans]
theorem LeanColls.Indexed.get.arg_cont.fwdCDeriv_rule
  (f : X → Cont) (idx : Idx)
  (hf : IsDifferentiable K f)
  : fwdCDeriv K (fun x => (f x)[idx])
    =
    fun x dx =>
      let ydy := fwdCDeriv K f x dx
      (ydy.1[idx], ydy.2[idx]) :=
by
  unfold fwdCDeriv; ftrans

end OnVec

section OnSemiInnerProductSpace

variable
  {X : Type} [SemiInnerProductSpace K X]
  [SemiInnerProductSpace K Elem]

@[fprop]
theorem LeanColls.Indexed.get.arg_cont.HasSemiAdjoint_rule
  (f : X → Cont) (idx : Idx)
  (hf : HasSemiAdjoint K f)
  : HasSemiAdjoint K (fun x => (f x)[idx]) := sorry_proof

@[ftrans]
theorem LeanColls.Indexed.get.arg_cont.semiAdjoint_rule
  (f : X → Cont) (idx : Idx)
  (hf : HasSemiAdjoint K f)
  : semiAdjoint K (fun x => (f x)[idx])
    =
    fun elem =>
      let cont : Cont := ⊞ i => if i=idx then elem else 0
      semiAdjoint K f cont :=
by
  sorry_proof

@[fprop]
theorem LeanColls.Indexed.get.arg_cont.HasAdjDiff_rule
  (f : X → Cont) (idx : Idx)
  (hf : HasAdjDiff K f)
  : HasAdjDiff K (fun x => (f x)[idx]) := sorry_proof

@[ftrans]
theorem LeanColls.Indexed.get.arg_cont.revCDeriv_rule
  (f : X → Cont) (idx : Idx)
  (hf : HasAdjDiff K f)
  : revCDeriv K (fun x => (f x)[idx])
    =
    fun x =>
      let ydf := revCDeriv K f x
      (ydf.1[idx],
       fun delem =>
         let dcont : Cont := ⊞ i => if i=idx then delem else 0
         ydf.2 dcont) :=
by
  have ⟨_,_⟩ := hf
  unfold revCDeriv; ftrans; ftrans; simp

@[ftrans]
theorem LeanColls.Indexed.get.arg_cont_i.revCDeriv_rule
  (f : X → Cont)
  (hf : HasAdjDiff K f)
  : revCDeriv K (fun x idx => (f x)[idx])
    =
    fun x =>
      let ydf := revCDeriv K f x
      (fun idx => ydf.1[idx],
       fun delem =>
         let dx := ⊞ i => delem i
         ydf.2 dx) :=
by
  have ⟨_,_⟩ := hf
  unfold revCDeriv; ftrans
  sorry_proof

@[ftrans]
theorem LeanColls.Indexed.get.arg_cont.revDeriv_rule
  (f : X → Cont) (idx : Idx)
  (hf : HasAdjDiff K f)
  : revDeriv K (fun x => (f x)[idx])
    =
    fun x =>
      let ydf := revDerivProj K Idx f x
      (ydf.1[idx],
       fun delem => ydf.2 idx delem) :=
by
  have ⟨_,_⟩ := hf
  unfold revDeriv; ftrans; ftrans
  funext x; simp[revDerivProj,revDeriv]
  funext delem;
  congr; sorry_proof

@[ftrans]
theorem LeanColls.Indexed.get.arg_cont.revDerivUpdate_rule
  (f : X → Cont) (idx : Idx)
  (hf : HasAdjDiff K f)
  : revDerivUpdate K (fun x => (f x)[idx])
    =
    fun x =>
      let ydf := revDerivProjUpdate K Idx f x
      (ydf.1[idx],
       fun delem dx => ydf.2 idx delem dx) :=
by
  unfold revDerivUpdate; ftrans; ftrans; simp[revDerivProjUpdate]


@[ftrans]
theorem LeanColls.Indexed.get.arg_cont.revDerivProj_rule
  {I ElemI} [StructType Elem I ElemI] [IndexType I] [LawfulIndexType I] [DecidableEq I] [∀ i, SemiInnerProductSpace K (ElemI i)]
  [SemiInnerProductSpaceStruct K Elem I ElemI]
  (f : X → Cont) (idx : Idx)
  (hf : HasAdjDiff K f)
  : revDerivProj K I (fun x => (f x)[idx])
    =
    fun x =>
      let ydf := revDerivProj K (Idx×I) f x
      (ydf.1[idx],
       fun i delem => ydf.2 (idx,i) delem) :=
by
  sorry_proof

@[ftrans]
theorem LeanColls.Indexed.get.arg_cont.revDerivProjUpdate_rule
  {I ElemI} [StructType Elem I ElemI] [IndexType I] [LawfulIndexType I] [DecidableEq I] [∀ i, SemiInnerProductSpace K (ElemI i)]
  [SemiInnerProductSpaceStruct K Elem I ElemI]
  (f : X → Cont) (idx : Idx)
  (hf : HasAdjDiff K f)
  : revDerivProjUpdate K I (fun x => (f x)[idx])
    =
    fun x =>
      let ydf := revDerivProjUpdate K (Idx×I) f x
      (ydf.1[idx],
       fun i delem dx => ydf.2 (idx,i) delem dx) :=
by
  sorry_proof


end OnSemiInnerProductSpace


-- SetElem.setElem -------------------------------------------------------------
--------------------------------------------------------------------------------

section OnNormedSpaces

variable
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  [NormedAddCommGroup Elem] [NormedSpace K Elem]

-- @[fprop]
-- theorem SetElem.setElem.arg_elem.IsContinuousLinearMap_rule
--   (cont : X → Cont) (idx : Idx) (elem : X → Elem)
--   (hcont : IsContinuousLinearMap K cont) (helem : IsContinuousLinearMap K elem)
--   : IsContinuousLinearMap K (λ x => setElem (0:Cont) idx (elem x)) := sorry_proof

-- @[fprop]
-- theorem SetElem.setElem.arg_contelem.Differentiable_rule
--   (cont : X → Cont) (idx : Idx) (elem : X → Elem)
--   (hcont : Differentiable K cont) (helem : Differentiable K elem)
--   : Differentiable K (λ x => setElem (cont x) idx (elem x)) := sorry_proof

-- @[fprop]
-- theorem SetElem.setElem.arg_contelem.DifferentiableAt_rule
--   (cont : X → Cont) (idx : Idx) (elem : X → Elem) (x : X)
--   (hcont : DifferentiableAt K cont x) (helem : DifferentiableAt K elem x)
--   : DifferentiableAt K (λ x => setElem (cont x) idx (elem x)) x := sorry_proof

end OnNormedSpaces

section OnVec

variable
  {X : Type _} [Vec K X]
  [Vec K Elem]

@[fprop]
theorem LeanColls.Indexed.set.arg_cont.IsLinearMap_rule_simple (idx : Idx)
  : IsLinearMap K (fun xs : Cont => Indexed.set xs idx 0) := sorry_proof

@[fprop]
theorem LeanColls.Indexed.set.arg_a0.IsLinearMap_rule_simple (idx : Idx)
  : IsLinearMap K (fun elem : Elem => Indexed.set (0 : Cont) idx elem) := sorry_proof

#generate_linear_map_simps LeanColls.Indexed.set.arg_cont.IsLinearMap_rule_simple
#generate_linear_map_simps LeanColls.Indexed.set.arg_a0.IsLinearMap_rule_simple

@[fprop]
theorem LeanColls.Indexed.set.arg_conta0.IsDifferentiable_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : IsDifferentiable K cont) (helem : IsDifferentiable K elem)
  : IsDifferentiable K (λ x => Indexed.set (cont x) idx (elem x)) := sorry_proof

@[fprop]
theorem LeanColls.Indexed.set.arg_conta0.IsDifferentiableAt_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) (x : X)
  (hcont : IsDifferentiableAt K cont x) (helem : IsDifferentiableAt K elem x)
  : IsDifferentiableAt K (λ x => Indexed.set (cont x) idx (elem x)) x := sorry_proof

@[ftrans]
theorem LeanColls.Indexed.set.arg_conta0.cderiv_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : IsDifferentiable K cont) (helem : IsDifferentiable K elem)
  : cderiv K (fun x => Indexed.set (cont x) idx (elem x))
    =
    fun x dx =>
      Indexed.set (cderiv K cont x dx) idx (cderiv K elem x dx) :=
by
  sorry_proof

@[ftrans]
theorem LeanColls.Indexed.set.arg_conta0.cderiv_rule_at
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) (x : X)
  (hcont : IsDifferentiableAt K cont x) (helem : IsDifferentiableAt K elem x)
  : cderiv K (fun x => Indexed.set (cont x) idx (elem x)) x
    =
    fun dx =>
      Indexed.set (cderiv K cont x dx) idx (cderiv K elem x dx) :=
by
  sorry_proof

@[ftrans]
theorem LeanColls.Indexed.set.arg_conta0.fwdCDeriv_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : IsDifferentiable K cont) (helem : IsDifferentiable K elem)
  : fwdCDeriv K (fun x => Indexed.set (cont x) idx (elem x))
    =
    fun x dx =>
      let cdc := fwdCDeriv K cont x dx
      let ede := fwdCDeriv K elem x dx
      (Indexed.set cdc.1 idx ede.1, Indexed.set cdc.2 idx ede.2) :=
by
  unfold fwdCDeriv; ftrans

@[ftrans]
theorem LeanColls.Indexed.set.arg_conta0.fwdCDeriv_rule_at
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) (x : X)
  (hcont : IsDifferentiableAt K cont x) (helem : IsDifferentiableAt K elem x)
  : fwdCDeriv K (fun x => Indexed.set (cont x) idx (elem x)) x
    =
    fun dx =>
      let cdc := fwdCDeriv K cont x dx
      let ede := fwdCDeriv K elem x dx
      (Indexed.set cdc.1 idx ede.1, Indexed.set cdc.2 idx ede.2) :=
by
  unfold fwdCDeriv; ftrans

end OnVec

section OnSemiInnerProductSpace

variable
  {X : Type _} [SemiInnerProductSpace K X]
  [SemiInnerProductSpace K Elem]

@[fprop]
theorem LeanColls.Indexed.set.arg_conta0.HasSemiAdjoint_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : HasSemiAdjoint K cont) (helem : HasSemiAdjoint K elem)
  : HasSemiAdjoint K (fun x => Indexed.set (cont x) idx (elem x)) := sorry_proof

@[ftrans]
theorem LeanColls.Indexed.set.arg_conta0.semiAdjoint_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : HasSemiAdjoint K cont) (helem : HasSemiAdjoint K elem)
  : semiAdjoint K (fun x => Indexed.set (cont x) idx (elem x))
    =
    fun x' =>
      semiAdjoint K cont (Indexed.set x' idx 0) +
      semiAdjoint K elem x'[idx] :=
by
  sorry_proof

@[fprop]
theorem LeanColls.Indexed.set.arg_conta0.HasAdjDiff_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : HasAdjDiff K (fun x => Indexed.set (cont x) idx (elem x)) := sorry_proof

@[ftrans]
theorem LeanColls.Indexed.set.arg_conta0.revCDeriv_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : revCDeriv K (fun x => Indexed.set (cont x) idx (elem x))
    =
    fun x =>
      let cdc := revCDeriv K cont x
      let ede := revCDeriv K elem x
      (Indexed.set cdc.1 idx ede.1,
       fun dcont' =>
         cdc.2 (Indexed.set dcont' idx 0)
         +
         ede.2 dcont'[idx]) :=
by
  have ⟨_,_⟩ := hcont
  have ⟨_,_⟩ := helem
  unfold revCDeriv; ftrans; ftrans; simp

@[ftrans]
theorem LeanColls.Indexed.set.arg_conta0.revCDeriv_rule_at
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) (x : X)
  (hcont : HasAdjDiffAt K cont x) (helem : HasAdjDiffAt K elem x)
  : revCDeriv K (fun x => Indexed.set (cont x) idx (elem x)) x
    =
    let cdc := revCDeriv K cont x
    let ede := revCDeriv K elem x
    (Indexed.set cdc.1 idx ede.1,
     fun dcont' =>
       cdc.2 (Indexed.set dcont' idx 0)
       +
       ede.2 dcont'[idx]) :=
by
  have ⟨_,_⟩ := hcont
  have ⟨_,_⟩ := helem
  unfold revCDeriv; ftrans; ftrans; simp


@[ftrans]
theorem LeanColls.Indexed.set.arg_conta0.revDeriv_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : revDeriv K (fun x => Indexed.set (cont x) idx (elem x))
    =
    fun x =>
      let cdc := revDeriv K cont x
      let ede := revDerivUpdate K elem x
      (Indexed.set cdc.1 idx ede.1,
       fun dcont' : Cont =>
         let delem' := dcont'[idx]
         let dcont' := Indexed.set dcont' idx 0
         let dx := cdc.2 dcont'
         ede.2 delem' dx) :=
by
  have ⟨_,_⟩ := hcont
  have ⟨_,_⟩ := helem
  unfold revDeriv; ftrans; ftrans; simp[revDerivUpdate,revDeriv]


@[ftrans]
theorem LeanColls.Indexed.set.arg_conta0.revDerivUpdate_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : revDerivUpdate K (fun x => Indexed.set (cont x) idx (elem x))
    =
    fun x =>
      let cdc := revDerivUpdate K cont x
      let ede := revDerivUpdate K elem x
      (Indexed.set cdc.1 idx ede.1,
       fun (dcont' : Cont) dx =>
         let delem' := dcont'[idx]
         let dcont' := Indexed.set dcont' idx 0
         let dx := cdc.2 dcont' dx
         ede.2 delem' dx) :=
by
  have ⟨_,_⟩ := hcont
  have ⟨_,_⟩ := helem
  unfold revDerivUpdate; ftrans; ftrans; simp[add_assoc,revDerivUpdate]

-- @[ftrans]
-- theorem LeanColls.Indexed.set.arg_conta0.revDerivProj_rule
--   (cont : X → Cont) (idx : Idx) (elem : X → Elem)
--   (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
--   : revDerivProj K Idx (fun x => Indexed.set (cont x) idx (elem x))
--     =
--     fun x =>
--       let cdc := revDerivProj K Idx cont x
--       let ede := revDeriv K elem x
--       (Indexed.set cdc.1 idx ede.1,
--        fun i dei =>
--          if i = idx then
--            ede.2 dei
--          else
--            cdc.2 i dei) :=
-- by
--   unfold revDerivProj; ftrans; ftrans; simp[revDerivUpdate,revDeriv]
--   funext x; simp; funext i dei
--   if h : i = idx then
--     subst h
--     simp[ArrayType.getElem_structProj, ArrayType.Indexed.set_structModify]
--     sorry_proof
--   else
--     simp[h,ArrayType.getElem_structProj, ArrayType.Indexed.set_structModify]
--     sorry_proof


@[ftrans]
theorem LeanColls.Indexed.set.arg_conta0.revDerivProj_rule'
  {I ElemI} [StructType Elem I ElemI] [IndexType I] [LawfulIndexType I] [DecidableEq I] [∀ i, SemiInnerProductSpace K (ElemI i)]
  [SemiInnerProductSpaceStruct K Elem I ElemI]
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : revDerivProj K (Idx×I) (fun x => Indexed.set (cont x) idx (elem x))
    =
    fun x =>
      let cdc := revDerivProj K (Idx×I) cont x
      let ede := revDerivProj K I elem x
      (Indexed.set cdc.1 idx ede.1,
       fun (i,j) deij =>
         if i = idx then
           ede.2 j deij
         else
           cdc.2 (i,j) deij) :=
by
  unfold revDerivProj; ftrans; ftrans; simp[revDerivUpdate,revDeriv]
  funext x; simp; funext (i,j) deij
  if h : i = idx then
    subst h
    simp
    sorry_proof
  else
    simp[h]
    sorry_proof


@[ftrans]
theorem LeanColls.Indexed.set.arg_conta0.revDerivProjUpdate_rule'
  {I ElemI} [StructType Elem I ElemI] [IndexType I] [LawfulIndexType I] [DecidableEq I] [∀ i, SemiInnerProductSpace K (ElemI i)]
  [SemiInnerProductSpaceStruct K Elem I ElemI]
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : revDerivProjUpdate K (Idx×I) (fun x => Indexed.set (cont x) idx (elem x))
    =
    fun x =>
      let cdc := revDerivProjUpdate K (Idx×I) cont x
      let ede := revDerivProjUpdate K I elem x
      (Indexed.set cdc.1 idx ede.1,
       fun (i,j) deij dx =>
         if i = idx then
           ede.2 j deij dx
         else
           cdc.2 (i,j) deij dx) :=
by
  unfold revDerivProjUpdate; ftrans; ftrans; simp[revDerivProjUpdate]
  funext x; simp; funext (i,j) deij
  if h : i = idx then
    subst h
    simp
  else
    simp[h]

end OnSemiInnerProductSpace


-- LeanColls.ofFn -------------------------------------------------------------
--------------------------------------------------------------------------------

section OnNormedSpaces

variable
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  [NormedAddCommGroup Elem] [NormedSpace K Elem]

-- @[fprop]
-- theorem LeanColls.ofFn.arg_f.IsContinuousLinearMap_rule
--   (f : X → Idx → Elem)
--   (hf : IsContinuousLinearMap K f)
--   : IsContinuousLinearMap K (λ x => Indexed.ofFn (Cont:=Cont) (f x)) := sorry_proof

-- @[fprop]
-- theorem LeanColls.ofFn.arg_f.Differentiable_rule [Fintype Idx]
--   (f : X → Idx → Elem)
--   (hf : Differentiable K f)
--   : Differentiable K (λ x => Indexed.ofFn (Cont:=Cont) (f x)) := sorry_proof

-- @[fprop]
-- theorem LeanColls.ofFn.arg_f.DifferentiableAt_rule [Fintype Idx]
--   (f : X → Idx → Elem) (x : X)
--   (hf : DifferentiableAt K f x)
--   : DifferentiableAt K (λ x => Indexed.ofFn (Cont:=Cont) (f x)) x := sorry_proof

end OnNormedSpaces

section OnVec

variable
  {X : Type _} [Vec K X]
  [Vec K Elem]

@[fprop]
theorem LeanColls.ofFn.arg_a0.IsLinearMap_rule_simple
  : IsLinearMap K (fun f : Idx → Elem => Indexed.ofFn (C:=Cont) f) := sorry_proof

#generate_linear_map_simps LeanColls.ofFn.arg_a0.IsLinearMap_rule_simple

@[fprop]
theorem LeanColls.ofFn.arg_a0.IsDifferentiable_rule
  (f : X → Idx → Elem)
  (hf : IsDifferentiable K f)
  : IsDifferentiable K (λ x => Indexed.ofFn (C:=Cont) (f x)) := sorry_proof

@[fprop]
theorem LeanColls.ofFn.arg_a0.IsDifferentiableAt_rule
  (f : X → Idx → Elem) (x : X)
  (hf : IsDifferentiableAt K f x)
  : IsDifferentiableAt K (λ x => Indexed.ofFn (C:=Cont) (f x)) x := sorry_proof

@[ftrans]
theorem LeanColls.ofFn.arg_a0.cderiv_rule
  (f : X → Idx → Elem)
  (hf : IsDifferentiable K f)
  : cderiv K (fun x => Indexed.ofFn (C:=Cont) (f x))
    =
    fun x dx => Indexed.ofFn (cderiv K f x dx) :=
by
  sorry_proof

@[ftrans]
theorem LeanColls.ofFn.arg_a0.cderiv_rule_at
  (f : X → Idx → Elem)  (x : X)
  (hf : IsDifferentiableAt K f x)
  : cderiv K (fun x => Indexed.ofFn (C:=Cont) (f x)) x
    =
    fun dx => Indexed.ofFn (cderiv K f x dx) :=
by
  sorry_proof

@[ftrans]
theorem LeanColls.ofFn.arg_a0.fwdCDeriv_rule
  (f : X → Idx → Elem)
  (hf : IsDifferentiable K f)
  : fwdCDeriv K (fun x => Indexed.ofFn (C:=Cont) (f x))
    =
    fun x dx =>
      let fdf := fwdCDeriv K f x dx
      (Indexed.ofFn fdf.1, Indexed.ofFn fdf.2) :=
by
  unfold fwdCDeriv; ftrans

@[ftrans]
theorem LeanColls.ofFn.arg_a0.fwdCDeriv_rule_at
  (f : X → Idx → Elem)  (x : X)
  (hf : IsDifferentiableAt K f x)
  : fwdCDeriv K (fun x => Indexed.ofFn (C:=Cont) (f x)) x
    =
    fun dx =>
      let fdf := fwdCDeriv K f x dx
      (Indexed.ofFn fdf.1, Indexed.ofFn fdf.2) :=
by
  unfold fwdCDeriv; ftrans

end OnVec

section OnSemiInnerProductSpace

variable
  {X : Type _} [SemiInnerProductSpace K X]
  [SemiInnerProductSpace K Elem]

@[fprop]
theorem LeanColls.ofFn.arg_a0.HasSemiAdjoint_rule
  (f : X → Idx → Elem)
  (hf : HasSemiAdjoint K f)
  : HasSemiAdjoint K (fun x => Indexed.ofFn (C:=Cont) (f x)) := sorry_proof

-- @[ftrans]
-- theorem LeanColls.ofFn.arg_a0.semiAdjoint_rule
--   (f : X → Idx → Elem)
--   (hf : HasSemiAdjoint K f)
--   : semiAdjoint K (fun x => Indexed.ofFn (C:=Cont) (f x))
--     =
--     fun c => semiAdjoint K f (fun i => c[i]) :=
-- by
--   sorry_proof

@[fprop]
theorem LeanColls.ofFn.arg_a0.HasAdjDiff_rule
  (f : X → Idx → Elem)
  (hf : HasAdjDiff K f)
  : HasAdjDiff K (fun x => Indexed.ofFn (C:=Cont) (f x)) := sorry_proof

-- @[ftrans]
-- theorem LeanColls.ofFn.arg_a0.revCDeriv_rule
--   (f : X → Idx → Elem)
--   (hf : HasAdjDiff K f)
--   : revCDeriv K (fun x => Indexed.ofFn (C:=Cont) (f x))
--     =
--     fun x =>
--       let fdf := revCDeriv K f x
--       (Indexed.ofFn fdf.1,
--        fun dc => fdf.2 (fun i => dc[i])) :=
-- by
--   have ⟨_,_⟩ := hf
--   unfold revCDeriv; ftrans; ftrans; simp

-- @[ftrans]
-- theorem LeanColls.ofFn.arg_a0.revCDeriv_rule_at
--   (f : X → Idx → Elem) (x : X)
--   (hf : HasAdjDiffAt K f x)
--   : revCDeriv K (fun x => Indexed.ofFn (C:=Cont) (f x)) x
--     =
--     let fdf := revCDeriv K f x
--     (Indexed.ofFn fdf.1,
--      fun dc => fdf.2 (fun i => dc[i])) :=
-- by
--   have ⟨_,_⟩ := hf
--   unfold revCDeriv; ftrans; ftrans; simp


-- @[ftrans]
-- theorem LeanColls.ofFn.arg_a0.revDeriv_rule
--   (f : X → Idx → Elem)
--   (hf : HasAdjDiff K f)
--   : revDeriv K (fun x => Indexed.ofFn (C:=Cont) (f x))
--     =
--     fun x =>
--       let fdf := revDeriv K f x
--       (Indexed.ofFn fdf.1,
--        fun dc => fdf.2 (fun i => dc[i])) :=
-- by
--   have ⟨_,_⟩ := hf
--   unfold revDeriv; ftrans; ftrans; simp

-- @[ftrans]
-- theorem LeanColls.ofFn.arg_a0.revDerivUpdate_rule
--   (f : X → Idx → Elem)
--   (hf : HasAdjDiff K f)
--   : revDerivUpdate K (fun x => Indexed.ofFn (C:=Cont) (f x))
--     =
--     fun x =>
--       let fdf := revDerivUpdate K f x
--       (Indexed.ofFn fdf.1,
--        fun dc dx => fdf.2 (fun i => dc[i]) dx) :=
-- by
--   unfold revDerivUpdate; ftrans

@[ftrans]
theorem LeanColls.ofFn.arg_a0.revDerivProj_rule
  {I ElemI} [StructType Elem I ElemI] [IndexType I] [LawfulIndexType I] [DecidableEq I] [∀ i, SemiInnerProductSpace K (ElemI i)]
  [SemiInnerProductSpaceStruct K Elem I ElemI]
  (f : X → Idx → Elem)
  (hf : HasAdjDiff K f)
  : revDerivProj K (Idx×I) (fun x => Indexed.ofFn (C:=Cont) (f x))
    =
    fun x =>
      let fdf := revDerivProj K (Idx×I) f x
      (Indexed.ofFn fdf.1,
       fun ij de => fdf.2 ij de) :=
by
  unfold revDerivProj; ftrans; ftrans; simp
  funext x; simp; funext i de
  sorry_proof

@[ftrans]
theorem LeanColls.ofFn.arg_a0.revDerivProjUpdate_rule
  {I ElemI} [StructType Elem I ElemI] [IndexType I] [LawfulIndexType I] [DecidableEq I] [∀ i, SemiInnerProductSpace K (ElemI i)]
  [SemiInnerProductSpaceStruct K Elem I ElemI]
  (f : X → Idx → Elem)
  (hf : HasAdjDiff K f)
  : revDerivProjUpdate K (Idx×I) (fun x => Indexed.ofFn (C:=Cont) (f x))
    =
    fun x =>
      let fdf := revDerivProjUpdate K (Idx×I) f x
      (Indexed.ofFn fdf.1,
       fun ij de dx => fdf.2 ij de dx) :=
by
  unfold revDerivProjUpdate; ftrans

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

section OnNormedSpaces

variable
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  [NormedAddCommGroup Elem] [NormedSpace K Elem]

-- @[fprop]
-- theorem ArrayType.map.arg_a0.IsContinuousLinearMap_rule
--   (f : X → Elem → Elem) (arr : Cont)
--   (hf : IsContinuousLinearMap K f)
--   : IsContinuousLinearMap K (λ x => map (f x) arr) := sorry_proof

-- @[fprop]
-- theorem ArrayType.map.arg_arr.IsContinuousLinearMap_rule
--   (f : Elem → Elem) (arr : X → Cont)
--   (harr : IsContinuousLinearMap K arr)
--   : IsContinuousLinearMap K (λ x => map f (arr x)) := sorry_proof

-- @[fprop]
-- theorem ArrayType.map.arg_a0arr.Differentiable_rule
--   (f : X → Elem → Elem) (arr : X → Cont)
--   (hf : Differentiable K (fun (xe : X×Elem) => f xe.1 xe.2))
--   (harr : Differentiable K arr)
--   : Differentiable K (λ x => map (f x) (arr x)) := sorry_proof

-- @[fprop]
-- theorem ArrayType.map.arg_a0arr.DifferentiableAt_rule
--   (f : X → Elem → Elem) (arr : X → Cont) (x : X)
--   (hf : ∀ i, DifferentiableAt K (fun (xe : X×Elem) => f xe.1 xe.2) (x, (arr x)[i]))
--   (harr : DifferentiableAt K arr x)
--   : DifferentiableAt K (λ x => map (f x) (arr x)) x := sorry_proof

-- TODO: fderiv, fwdFDeriv, adjoint, revFDeriv

end OnNormedSpaces

namespace SciLean
section OnVec

variable
  {X : Type _} [Vec K X]
  [Vec K Elem]

-- @[fprop]
-- theorem ArrayType.map.arg_xs.IsDifferentiable_rule
--   (f : X → Cont) (idx : Idx) (dom)
--   (hf : IsDifferentiable K f)
--   : IsDifferentiable K (λ x => getElem (f x) idx dom) := sorry_proof

-- @[fprop]
-- theorem ArrayType.map.arg_xs.IsDifferentiableAt_rule
--   (f : X → Cont) (idx : Idx) (dom) (x : X)
--   (hf : IsDifferentiableAt K f x)
--   : IsDifferentiableAt K (λ x => getElem (f x) idx dom) x := sorry_proof

@[ftrans]
theorem ArrayType.map.arg_a0arr.cderiv_rule
  (f : X → Elem → Elem) (arr : X → Cont)
  (hf : IsDifferentiable K (fun (xe : X×Elem) => f xe.1 xe.2))
  (harr : IsDifferentiable K arr)
  : cderiv K (fun x => mapMono (f x) (arr x))
    =
    fun x dx =>
      let a  := arr x
      let da := cderiv K arr x dx
      let df := cderiv K (fun (xe : X×Elem) => f xe.1 xe.2)
      Indexed.ofFn (fun i => df (x,a[i]) (dx,da[i])) :=
by
  sorry_proof

@[ftrans]
theorem ArrayType.map.arg_a0arr.cderiv_rule_at
  (f : X → Elem → Elem) (arr : X → Cont)
  (hf : ∀ i, IsDifferentiableAt K (fun (xe : X×Elem) => f xe.1 xe.2) (x, (arr x)[i]))
  (harr : IsDifferentiableAt K arr x)
  : cderiv K (fun x => mapMono (f x) (arr x)) x
    =
    fun dx =>
      let a  := arr x
      let da := cderiv K arr x dx
      Indexed.ofFn (fun i =>
        cderiv K (fun (xe : X×Elem) => f xe.1 xe.2) (x,a[i]) (dx,da[i])) :=
by
  sorry_proof

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

end OnVec

section OnSemiInnerProductSpace

variable
  {X : Type _} [SemiInnerProductSpace K X]
  [SemiInnerProductSpace K Elem]

@[fprop]
theorem ArrayType.map.arg_a0arr.HasAdjDiff_rule
  (f : X → Elem → Elem) (arr : X → Cont)
  (hf : HasAdjDiff K (fun (xe : X×Elem) => f xe.1 xe.2)) (harr : HasAdjDiff K arr)
  : HasAdjDiff K (fun x => mapMono (f x) (arr x)) := sorry_proof

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


@[ftrans]
theorem ArrayType.map.arg_arr.revDeriv_rule
  (f : Elem → Elem) (arr : X → Cont)
  (hf : HasAdjDiff K f) (harr : HasAdjDiff K arr)
  : revDeriv K (fun x => mapMono f (arr x))
    =
    fun x =>
      let fdf := revDeriv K f
      let ada := revDeriv K arr x
      let a := ada.1
      (mapMono f a,
       fun da =>
         let da := mapMonoIdx (fun i dai => (fdf a[i]).2 dai) da
         ada.2 da) := sorry_proof


@[ftrans]
theorem ArrayType.map.arg_arr.revDerivUpdate_rule
  (f : Elem → Elem) (arr : X → Cont)
  (hf : HasAdjDiff K f) (harr : HasAdjDiff K arr)
  : revDerivUpdate K (fun x => mapMono f (arr x))
    =
    fun x =>
      let fdf := revDeriv K f
      let ada := revDerivUpdate K arr x
      let a := ada.1
      (mapMono f a,
       fun da dx =>
         let da := mapMonoIdx (fun i dai => let df := (fdf a[i]).2; df dai) da
         ada.2 da dx) := sorry_proof

--------------------------------------------------------------------------------

@[fprop]
theorem ArrayType.max.arg_cont.HasAdjDiff_rule
  [LT Elem] [∀ x y : Elem, Decidable (x < y)] [Inhabited Idx]
  (arr : X → Cont)
  (hf : HasAdjDiff K arr) (hfalse : fpropParam False)
  : HasAdjDiff K (fun x => max (arr x)) := sorry_proof


@[ftrans]
theorem ArrayType.max.arg_arr.revDeriv_rule
  [LT Elem] [∀ x y : Elem, Decidable (x < y)] [Inhabited Idx]
  (arr : X → Cont)
  (hf : HasAdjDiff K arr) (hfalse : fpropParam False)
  : revDeriv K (fun x => max (arr x))
    =
    fun x =>
      let i := idxMax (arr x)
      let fdf := revDerivProj K Idx arr x
      (fdf.1[i], fun dei => fdf.2 i dei) := sorry_proof


@[ftrans]
theorem ArrayType.max.arg_arr.revDerivUpdate_rule
  [LT Elem] [∀ x y : Elem, Decidable (x < y)] [Inhabited Idx]
  (arr : X → Cont)
  (hf : HasAdjDiff K arr) (hfalse : fpropParam False)
  : revDerivUpdate K (fun x => max (arr x))
    =
    fun x =>
      let i := idxMax (arr x)
      let fdf := revDerivProjUpdate K Idx arr x
      (fdf.1[i], fun dei dx => fdf.2 i dei dx) := sorry_proof


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

-- @[fprop]
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

end OnSemiInnerProductSpace


-- ArrayType.split -------------------------------------------------------------
--------------------------------------------------------------------------------


-- ArrayType.append ------------------------------------------------------------
--------------------------------------------------------------------------------
