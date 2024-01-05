import SciLean.Core.FunctionPropositions
import SciLean.Core.FunctionTransformations
import SciLean.Data.ArrayType.Algebra


open SciLean

set_option linter.unusedVariables false

section GenericArrayType

variable 
  {K : Type} [IsROrC K]
  {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam}
  [ArrayType Cont Idx Elem] [Index Idx]
  

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
theorem GetElem.getElem.arg_xs.IsLinearMap_rule_simple
  (idx : Idx) (dom)
  : IsLinearMap K (fun xs : Cont => getElem xs idx dom) := sorry_proof

#generate_linear_map_simps GetElem.getElem.arg_xs.IsLinearMap_rule_simple

@[fprop]
theorem GetElem.getElem.arg_xs.IsDifferentiable_rule 
  (f : X → Cont) (idx : Idx) (dom)
  (hf : IsDifferentiable K f)
  : IsDifferentiable K (λ x => getElem (f x) idx dom) := sorry_proof

@[fprop]
theorem GetElem.getElem.arg_xs.IsDifferentiableAt_rule 
  (f : X → Cont) (idx : Idx) (dom) (x : X)
  (hf : IsDifferentiableAt K f x)
  : IsDifferentiableAt K (λ x => getElem (f x) idx dom) x := sorry_proof

@[ftrans]
theorem GetElem.getElem.arg_xs.cderiv_rule
  (f : X → Cont) (idx : Idx) (dom)
  (hf : IsDifferentiable K f)
  : cderiv K (fun x => getElem (f x) idx dom)
    =
    fun x dx =>
      getElem (cderiv K f x dx) idx dom :=
by
  sorry_proof

@[ftrans]
theorem GetElem.getElem.arg_xs.cderiv_rule_at
  (f : X → Cont) (idx : Idx) (dom) (x : X)
  (hf : IsDifferentiableAt K f x)
  : cderiv K (fun x => getElem (f x) idx dom) x
    =
    fun dx =>
      getElem (cderiv K f x dx) idx dom :=
by
  sorry_proof

@[ftrans]
theorem GetElem.getElem.arg_xs.fwdCDeriv_rule
  (f : X → Cont) (idx : Idx) (dom)
  (hf : IsDifferentiable K f)
  : fwdCDeriv K (fun x => getElem (f x) idx dom)
    =
    fun x dx =>
      let ydy := fwdCDeriv K f x dx
      (getElem ydy.1 idx dom, getElem ydy.2 idx dom) :=
by
  sorry_proof

@[ftrans]
theorem GetElem.getElem.arg_xs.fwdCDeriv_rule_at
  (f : X → Cont) (idx : Idx) (dom) (x : X)
  (hf : IsDifferentiableAt K f x)
  : fwdCDeriv K (fun x => getElem (f x) idx dom) x
    =
    fun dx =>
      let ydy := fwdCDeriv K f x dx
      (getElem ydy.1 idx dom, getElem ydy.2 idx dom) :=
by
  sorry_proof

end OnVec

section OnSemiInnerProductSpace

variable 
  {X : Type} [SemiInnerProductSpace K X]
  [SemiInnerProductSpace K Elem]

@[fprop]
theorem GetElem.getElem.arg_xs.HasSemiAdjoint_rule
  (f : X → Cont) (idx : Idx) (dom) 
  (hf : HasSemiAdjoint K f)
  : HasSemiAdjoint K (fun x => getElem (f x) idx dom) := sorry_proof

@[ftrans]
theorem GetElem.getElem.arg_xs.semiAdjoint_rule
  (f : X → Cont) (idx : Idx) (dom) 
  (hf : HasSemiAdjoint K f)
  : semiAdjoint K (fun x => getElem (f x) idx dom)
    =
    fun elem =>
      let cont : Cont := introElem fun i => if i=idx then elem else 0
      semiAdjoint K f cont :=
by
  sorry_proof

@[fprop]
theorem GetElem.getElem.arg_xs.HasAdjDiff_rule
  (f : X → Cont) (idx : Idx) (dom) 
  (hf : HasAdjDiff K f)
  : HasAdjDiff K (fun x => getElem (f x) idx dom) := sorry_proof

@[ftrans]
theorem GetElem.getElem.arg_xs.revCDeriv_rule
  (f : X → Cont) (idx : Idx) (dom) 
  (hf : HasAdjDiff K f)
  : revCDeriv K (fun x => getElem (f x) idx dom)
    =
    fun x =>
      let ydf := revCDeriv K f x
      (getElem ydf.1 idx dom,
       fun delem => 
         let dcont : Cont := introElem fun i => if i=idx then delem else 0
         ydf.2 dcont) :=
by
  have ⟨_,_⟩ := hf
  unfold revCDeriv; ftrans; ftrans; simp

@[ftrans]
theorem GetElem.getElem.arg_xs.revCDeriv_rule_at
  (f : X → Cont) (idx : Idx) (dom) (x : X)
  (hf : HasAdjDiffAt K f x)
  : revCDeriv K (fun x => getElem (f x) idx dom) x
    =
    let ydf := revCDeriv K f x
    (getElem ydf.1 idx dom,
     fun delem => 
       let dcont : Cont := introElem fun i => if i=idx then delem else 0
       ydf.2 dcont) :=
by
  have ⟨_,_⟩ := hf
  unfold revCDeriv; ftrans; ftrans; simp

@[ftrans]
theorem GetElem.getElem.arg_xs_i.revCDeriv_rule
  (f : X → Cont) (dom) 
  (hf : HasAdjDiff K f)
  : revCDeriv K (fun x idx => getElem (f x) idx dom)
    =
    fun x =>
      let ydf := revCDeriv K f x
      (fun idx => getElem ydf.1 idx dom,
       fun delem => 
         let dx := introElem delem
         ydf.2 dx) := 
by
  have ⟨_,_⟩ := hf
  unfold revCDeriv; ftrans
  sorry_proof

@[ftrans]
theorem GetElem.getElem.arg_xs.revDeriv_rule
  (f : X → Cont) (idx : Idx) (dom)
  (hf : HasAdjDiff K f)
  : revDeriv K (fun x => getElem (f x) idx dom)
    =
    fun x =>
      let ydf := revDerivProj K Idx f x
      (getElem ydf.1 idx dom,
       fun delem => ydf.2 idx delem) :=
by
  have ⟨_,_⟩ := hf
  unfold revDeriv; ftrans; ftrans
  funext x; simp[revDerivProj,revDeriv]
  funext delem;
  congr; apply ArrayType.ext; -- needs proper StructType instance for ArrayType
  sorry_proof

@[ftrans]
theorem GetElem.getElem.arg_xs.revDerivUpdate_rule
  (f : X → Cont) (idx : Idx) (dom)
  (hf : HasAdjDiff K f)
  : revDerivUpdate K (fun x => getElem (f x) idx dom)
    =
    fun x =>
      let ydf := revDerivProjUpdate K Idx f x
      (getElem ydf.1 idx dom,
       fun delem dx => ydf.2 idx delem dx) :=
by
  unfold revDerivUpdate; ftrans; ftrans; simp[revDerivProjUpdate]


@[ftrans]
theorem GetElem.getElem.arg_xs.revDerivProj_rule
  {I ElemI} [StructType Elem I ElemI] [EnumType I] [∀ i, SemiInnerProductSpace K (ElemI i)]
  [SemiInnerProductSpaceStruct K Elem I ElemI]
  (f : X → Cont) (idx : Idx) (dom)
  (hf : HasAdjDiff K f)
  : revDerivProj K I (fun x => getElem (f x) idx dom)
    =
    fun x =>
      let ydf := revDerivProj K (Idx×I) f x
      (getElem ydf.1 idx dom,
       fun i delem => ydf.2 (idx,i) delem) :=
by
  sorry_proof

@[ftrans]
theorem GetElem.getElem.arg_xs.revDerivProjUpdate_rule
  {I ElemI} [StructType Elem I ElemI] [EnumType I] [∀ i, SemiInnerProductSpace K (ElemI i)]
  [SemiInnerProductSpaceStruct K Elem I ElemI]
  (f : X → Cont) (idx : Idx) (dom)
  (hf : HasAdjDiff K f)
  : revDerivProjUpdate K I (fun x => getElem (f x) idx dom)
    =
    fun x =>
      let ydf := revDerivProjUpdate K (Idx×I) f x
      (getElem ydf.1 idx dom,
       fun i delem dx => ydf.2 (idx,i) delem dx) :=
by
  sorry_proof


end OnSemiInnerProductSpace


-- SetElem.setElem -------------------------------------------------------------
--------------------------------------------------------------------------------

namespace SciLean

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
theorem SetElem.setElem.arg_cont.IsLinearMap_rule_simple (idx : Idx)
  : IsLinearMap K (fun xs : Cont => setElem xs idx 0) := sorry_proof

@[fprop]
theorem SetElem.setElem.arg_elem.IsLinearMap_rule_simple (idx : Idx)
  : IsLinearMap K (fun elem : Elem => setElem (0 : Cont) idx elem) := sorry_proof

#generate_linear_map_simps SciLean.SetElem.setElem.arg_cont.IsLinearMap_rule_simple
#generate_linear_map_simps SciLean.SetElem.setElem.arg_elem.IsLinearMap_rule_simple

@[fprop]
theorem SetElem.setElem.arg_contelem.IsDifferentiable_rule 
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : IsDifferentiable K cont) (helem : IsDifferentiable K elem)
  : IsDifferentiable K (λ x => setElem (cont x) idx (elem x)) := sorry_proof

@[fprop]
theorem SetElem.setElem.arg_contelem.IsDifferentiableAt_rule 
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) (x : X)
  (hcont : IsDifferentiableAt K cont x) (helem : IsDifferentiableAt K elem x)
  : IsDifferentiableAt K (λ x => setElem (cont x) idx (elem x)) x := sorry_proof

@[ftrans]
theorem SetElem.setElem.arg_contelem.cderiv_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : IsDifferentiable K cont) (helem : IsDifferentiable K elem)
  : cderiv K (fun x => setElem (cont x) idx (elem x))
    =
    fun x dx =>
      setElem (cderiv K cont x dx) idx (cderiv K elem x dx) :=
by
  sorry_proof

@[ftrans]
theorem SetElem.setElem.arg_contelem.cderiv_rule_at
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) (x : X)
  (hcont : IsDifferentiableAt K cont x) (helem : IsDifferentiableAt K elem x)
  : cderiv K (fun x => setElem (cont x) idx (elem x)) x
    =
    fun dx =>
      setElem (cderiv K cont x dx) idx (cderiv K elem x dx) :=
by
  sorry_proof

@[ftrans]
theorem SetElem.setElem.arg_contelem.fwdCDeriv_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem)
  (hcont : IsDifferentiable K cont) (helem : IsDifferentiable K elem)
  : fwdCDeriv K (fun x => setElem (cont x) idx (elem x))
    =
    fun x dx =>
      let cdc := fwdCDeriv K cont x dx
      let ede := fwdCDeriv K elem x dx
      (setElem cdc.1 idx ede.1, setElem cdc.2 idx ede.2) :=
by
  unfold fwdCDeriv; ftrans

@[ftrans]
theorem SetElem.setElem.arg_contelem.fwdCDeriv_rule_at
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) (x : X)
  (hcont : IsDifferentiableAt K cont x) (helem : IsDifferentiableAt K elem x)
  : fwdCDeriv K (fun x => setElem (cont x) idx (elem x)) x
    =
    fun dx =>
      let cdc := fwdCDeriv K cont x dx
      let ede := fwdCDeriv K elem x dx
      (setElem cdc.1 idx ede.1, setElem cdc.2 idx ede.2) :=
by
  unfold fwdCDeriv; ftrans

end OnVec

section OnSemiInnerProductSpace

variable 
  {X : Type _} [SemiInnerProductSpace K X]
  [SemiInnerProductSpace K Elem]

@[fprop]
theorem SetElem.setElem.arg_contelem.HasSemiAdjoint_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) 
  (hcont : HasSemiAdjoint K cont) (helem : HasSemiAdjoint K elem)
  : HasSemiAdjoint K (fun x => setElem (cont x) idx (elem x)) := sorry_proof

@[ftrans]
theorem SetElem.setElem.arg_contelem.semiAdjoint_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) 
  (hcont : HasSemiAdjoint K cont) (helem : HasSemiAdjoint K elem)
  : semiAdjoint K (fun x => setElem (cont x) idx (elem x))
    =
    fun x' =>
      semiAdjoint K cont (setElem x' idx 0) + 
      semiAdjoint K elem x'[idx] :=
by
  sorry_proof

@[fprop]
theorem SetElem.setElem.arg_contelem.HasAdjDiff_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) 
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : HasAdjDiff K (fun x => setElem (cont x) idx (elem x)) := sorry_proof

@[ftrans]
theorem SetElem.setElem.arg_contelem.revCDeriv_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) 
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : revCDeriv K (fun x => setElem (cont x) idx (elem x))
    =
    fun x =>
      let cdc := revCDeriv K cont x
      let ede := revCDeriv K elem x
      (setElem cdc.1 idx ede.1,
       fun dcont' => 
         cdc.2 (setElem dcont' idx 0) 
         +
         ede.2 dcont'[idx]) :=
by
  have ⟨_,_⟩ := hcont
  have ⟨_,_⟩ := helem
  unfold revCDeriv; ftrans; ftrans; simp

@[ftrans]
theorem SetElem.setElem.arg_contelem.revCDeriv_rule_at
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) (x : X) 
  (hcont : HasAdjDiffAt K cont x) (helem : HasAdjDiffAt K elem x)
  : revCDeriv K (fun x => setElem (cont x) idx (elem x)) x
    =
    let cdc := revCDeriv K cont x
    let ede := revCDeriv K elem x
    (setElem cdc.1 idx ede.1,
     fun dcont' => 
       cdc.2 (setElem dcont' idx 0) 
       +
       ede.2 dcont'[idx]) :=
by
  have ⟨_,_⟩ := hcont
  have ⟨_,_⟩ := helem
  unfold revCDeriv; ftrans; ftrans; simp


@[ftrans]
theorem SetElem.setElem.arg_contelem.revDeriv_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) 
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : revDeriv K (fun x => setElem (cont x) idx (elem x))
    =
    fun x => 
      let cdc := revDeriv K cont x
      let ede := revDerivUpdate K elem x
      (setElem cdc.1 idx ede.1,
       fun dcont' => 
         let delem' := dcont'[idx]
         let dcont' := setElem dcont' idx 0
         let dx := cdc.2 dcont'
         ede.2 delem' dx) :=
by
  have ⟨_,_⟩ := hcont
  have ⟨_,_⟩ := helem
  unfold revDeriv; ftrans; ftrans; simp[revDerivUpdate,revDeriv]


@[ftrans]
theorem SetElem.setElem.arg_contelem.revDerivUpdate_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) 
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : revDerivUpdate K (fun x => setElem (cont x) idx (elem x))
    =
    fun x =>
      let cdc := revDerivUpdate K cont x
      let ede := revDerivUpdate K elem x
      (setElem cdc.1 idx ede.1,
       fun dcont' dx => 
         let delem' := dcont'[idx]
         let dcont' := setElem dcont' idx 0
         let dx := cdc.2 dcont' dx
         ede.2 delem' dx) := 
by
  have ⟨_,_⟩ := hcont
  have ⟨_,_⟩ := helem
  unfold revDerivUpdate; ftrans; ftrans; simp[add_assoc,revDerivUpdate]


@[ftrans]
theorem SetElem.setElem.arg_contelem.revDerivProj_rule
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) 
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : revDerivProj K Idx (fun x => setElem (cont x) idx (elem x))
    =
    fun x => 
      let cdc := revDerivProj K Idx cont x
      let ede := revDeriv K elem x
      (setElem cdc.1 idx ede.1,
       fun i dei => 
         if i = idx then 
           ede.2 dei
         else
           cdc.2 i dei) :=
by
  unfold revDerivProj; ftrans; ftrans; simp[revDerivUpdate,revDeriv]
  funext x; simp; funext i dei
  if h : i = idx then
    subst h
    simp[ArrayType.getElem_structProj, ArrayType.setElem_structModify]
    sorry_proof
  else 
    simp[h,ArrayType.getElem_structProj, ArrayType.setElem_structModify]
    sorry_proof


@[ftrans]
theorem SetElem.setElem.arg_contelem.revDerivProj_rule'
  {I ElemI} [StructType Elem I ElemI] [EnumType I] [∀ i, SemiInnerProductSpace K (ElemI i)]
  [SemiInnerProductSpaceStruct K Elem I ElemI]
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) 
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : revDerivProj K (Idx×I) (fun x => setElem (cont x) idx (elem x))
    =
    fun x => 
      let cdc := revDerivProj K (Idx×I) cont x
      let ede := revDerivProj K I elem x
      (setElem cdc.1 idx ede.1,
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
    simp[ArrayType.getElem_structProj, ArrayType.setElem_structModify]
    sorry_proof
  else 
    simp[h,ArrayType.getElem_structProj, ArrayType.setElem_structModify]
    sorry_proof


@[ftrans]
theorem SetElem.setElem.arg_contelem.revDerivProjUpdate_rule'
  {I ElemI} [StructType Elem I ElemI] [EnumType I] [∀ i, SemiInnerProductSpace K (ElemI i)]
  [SemiInnerProductSpaceStruct K Elem I ElemI]
  (cont : X → Cont) (idx : Idx) (elem : X → Elem) 
  (hcont : HasAdjDiff K cont) (helem : HasAdjDiff K elem)
  : revDerivProjUpdate K (Idx×I) (fun x => setElem (cont x) idx (elem x))
    =
    fun x => 
      let cdc := revDerivProjUpdate K (Idx×I) cont x
      let ede := revDerivProjUpdate K I elem x
      (setElem cdc.1 idx ede.1,
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
    simp[ArrayType.getElem_structProj, ArrayType.setElem_structModify]
  else 
    simp[h,ArrayType.getElem_structProj, ArrayType.setElem_structModify]

end OnSemiInnerProductSpace


-- IntroElem.introElem -------------------------------------------------------------
--------------------------------------------------------------------------------

section OnNormedSpaces

variable 
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  [NormedAddCommGroup Elem] [NormedSpace K Elem]

-- @[fprop]
-- theorem IntroElem.introElem.arg_f.IsContinuousLinearMap_rule 
--   (f : X → Idx → Elem)
--   (hf : IsContinuousLinearMap K f)
--   : IsContinuousLinearMap K (λ x => introElem (Cont:=Cont) (f x)) := sorry_proof

-- @[fprop]
-- theorem IntroElem.introElem.arg_f.Differentiable_rule [Fintype Idx]
--   (f : X → Idx → Elem)
--   (hf : Differentiable K f)
--   : Differentiable K (λ x => introElem (Cont:=Cont) (f x)) := sorry_proof

-- @[fprop]
-- theorem IntroElem.introElem.arg_f.DifferentiableAt_rule [Fintype Idx]
--   (f : X → Idx → Elem) (x : X)
--   (hf : DifferentiableAt K f x) 
--   : DifferentiableAt K (λ x => introElem (Cont:=Cont) (f x)) x := sorry_proof

end OnNormedSpaces

section OnVec

variable 
  {X : Type _} [Vec K X]
  [Vec K Elem]

@[fprop]
theorem IntroElem.introElem.arg_f.IsLinearMap_rule_simple
  : IsLinearMap K (fun f : Idx → Elem => introElem (Cont:=Cont) f) := sorry_proof

#generate_linear_map_simps SciLean.IntroElem.introElem.arg_f.IsLinearMap_rule_simple

@[fprop]
theorem IntroElem.introElem.arg_f.IsDifferentiable_rule 
  (f : X → Idx → Elem) 
  (hf : IsDifferentiable K f) 
  : IsDifferentiable K (λ x => introElem (Cont:=Cont) (f x)) := sorry_proof

@[fprop]
theorem IntroElem.introElem.arg_f.IsDifferentiableAt_rule 
  (f : X → Idx → Elem) (x : X)
  (hf : IsDifferentiableAt K f x) 
  : IsDifferentiableAt K (λ x => introElem (Cont:=Cont) (f x)) x := sorry_proof

@[ftrans]
theorem IntroElem.introElem.arg_f.cderiv_rule
  (f : X → Idx → Elem) 
  (hf : IsDifferentiable K f) 
  : cderiv K (fun x => introElem (Cont:=Cont) (f x))
    =
    fun x dx => introElem (cderiv K f x dx) :=
by
  sorry_proof

@[ftrans]
theorem IntroElem.introElem.arg_f.cderiv_rule_at
  (f : X → Idx → Elem)  (x : X)
  (hf : IsDifferentiableAt K f x) 
  : cderiv K (fun x => introElem (Cont:=Cont) (f x)) x
    =
    fun dx => introElem (cderiv K f x dx) :=
by
  sorry_proof

@[ftrans]
theorem IntroElem.introElem.arg_f.fwdCDeriv_rule
  (f : X → Idx → Elem) 
  (hf : IsDifferentiable K f) 
  : fwdCDeriv K (fun x => introElem (Cont:=Cont) (f x))
    =
    fun x dx =>
      let fdf := fwdCDeriv K f x dx
      (introElem fdf.1, introElem fdf.2) :=
by
  unfold fwdCDeriv; ftrans

@[ftrans]
theorem IntroElem.introElem.arg_f.fwdCDeriv_rule_at
  (f : X → Idx → Elem)  (x : X)
  (hf : IsDifferentiableAt K f x) 
  : fwdCDeriv K (fun x => introElem (Cont:=Cont) (f x)) x
    =
    fun dx =>
      let fdf := fwdCDeriv K f x dx
      (introElem fdf.1, introElem fdf.2) :=
by
  unfold fwdCDeriv; ftrans

end OnVec

section OnSemiInnerProductSpace

variable 
  {X : Type _} [SemiInnerProductSpace K X]
  [SemiInnerProductSpace K Elem]

@[fprop]
theorem IntroElem.introElem.arg_f.HasSemiAdjoint_rule
  (f : X → Idx → Elem)  
  (hf : HasSemiAdjoint K f) 
  : HasSemiAdjoint K (fun x => introElem (Cont:=Cont) (f x)) := sorry_proof

@[ftrans]
theorem IntroElem.introElem.arg_f.semiAdjoint_rule
  (f : X → Idx → Elem)  
  (hf : HasSemiAdjoint K f) 
  : semiAdjoint K (fun x => introElem (Cont:=Cont) (f x))
    =
    fun c => semiAdjoint K f (fun i => c[i]) :=
by
  sorry_proof

@[fprop]
theorem IntroElem.introElem.arg_f.HasAdjDiff_rule
  (f : X → Idx → Elem)  
  (hf : HasAdjDiff K f) 
  : HasAdjDiff K (fun x => introElem (Cont:=Cont) (f x)) := sorry_proof

@[ftrans]
theorem IntroElem.introElem.arg_f.revCDeriv_rule
  (f : X → Idx → Elem)  
  (hf : HasAdjDiff K f) 
  : revCDeriv K (fun x => introElem (Cont:=Cont) (f x))
    =
    fun x =>
      let fdf := revCDeriv K f x
      (introElem fdf.1,
       fun dc => fdf.2 (fun i => dc[i])) :=
by
  have ⟨_,_⟩ := hf
  unfold revCDeriv; ftrans; ftrans; simp

@[ftrans]
theorem IntroElem.introElem.arg_f.revCDeriv_rule_at
  (f : X → Idx → Elem) (x : X) 
  (hf : HasAdjDiffAt K f x) 
  : revCDeriv K (fun x => introElem (Cont:=Cont) (f x)) x
    =
    let fdf := revCDeriv K f x
    (introElem fdf.1,
     fun dc => fdf.2 (fun i => dc[i])) :=
by
  have ⟨_,_⟩ := hf
  unfold revCDeriv; ftrans; ftrans; simp


@[ftrans]
theorem IntroElem.introElem.arg_f.revDeriv_rule
  (f : X → Idx → Elem)  
  (hf : HasAdjDiff K f) 
  : revDeriv K (fun x => introElem (Cont:=Cont) (f x))
    =
    fun x =>
      let fdf := revDeriv K f x
      (introElem fdf.1,
       fun dc => fdf.2 (fun i => dc[i])) :=
by
  have ⟨_,_⟩ := hf
  unfold revDeriv; ftrans; ftrans; simp

@[ftrans]
theorem IntroElem.introElem.arg_f.revDerivUpdate_rule
  (f : X → Idx → Elem)  
  (hf : HasAdjDiff K f) 
  : revDerivUpdate K (fun x => introElem (Cont:=Cont) (f x))
    =
    fun x =>
      let fdf := revDerivUpdate K f x
      (introElem fdf.1,
       fun dc dx => fdf.2 (fun i => dc[i]) dx) :=
by
  unfold revDerivUpdate; ftrans

@[ftrans]
theorem IntroElem.introElem.arg_f.revDerivProj_rule
  {I ElemI} [StructType Elem I ElemI] [EnumType I] [∀ i, SemiInnerProductSpace K (ElemI i)]
  [SemiInnerProductSpaceStruct K Elem I ElemI]
  (f : X → Idx → Elem)  
  (hf : HasAdjDiff K f) 
  : revDerivProj K (Idx×I) (fun x => introElem (Cont:=Cont) (f x))
    =
    fun x =>
      let fdf := revDerivProj K (Idx×I) f x
      (introElem fdf.1,
       fun ij de => fdf.2 ij de) :=
by
  unfold revDerivProj; ftrans; ftrans; simp
  funext x; simp; funext i de
  apply congr_arg; sorry_proof
  
@[ftrans]
theorem IntroElem.introElem.arg_f.revDerivProjUpdate_rule
  {I ElemI} [StructType Elem I ElemI] [EnumType I] [∀ i, SemiInnerProductSpace K (ElemI i)]
  [SemiInnerProductSpaceStruct K Elem I ElemI]
  (f : X → Idx → Elem)  
  (hf : HasAdjDiff K f) 
  : revDerivProjUpdate K (Idx×I) (fun x => introElem (Cont:=Cont) (f x))
    =
    fun x =>
      let fdf := revDerivProjUpdate K (Idx×I) f x
      (introElem fdf.1,
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
-- theorem ArrayType.map.arg_f.IsContinuousLinearMap_rule 
--   (f : X → Elem → Elem) (arr : Cont)
--   (hf : IsContinuousLinearMap K f)
--   : IsContinuousLinearMap K (λ x => map (f x) arr) := sorry_proof

-- @[fprop]
-- theorem ArrayType.map.arg_arr.IsContinuousLinearMap_rule 
--   (f : Elem → Elem) (arr : X → Cont)
--   (harr : IsContinuousLinearMap K arr)
--   : IsContinuousLinearMap K (λ x => map f (arr x)) := sorry_proof

-- @[fprop]
-- theorem ArrayType.map.arg_farr.Differentiable_rule
--   (f : X → Elem → Elem) (arr : X → Cont)
--   (hf : Differentiable K (fun (xe : X×Elem) => f xe.1 xe.2))
--   (harr : Differentiable K arr)
--   : Differentiable K (λ x => map (f x) (arr x)) := sorry_proof

-- @[fprop]
-- theorem ArrayType.map.arg_farr.DifferentiableAt_rule
--   (f : X → Elem → Elem) (arr : X → Cont) (x : X)
--   (hf : ∀ i, DifferentiableAt K (fun (xe : X×Elem) => f xe.1 xe.2) (x, (arr x)[i]))
--   (harr : DifferentiableAt K arr x)
--   : DifferentiableAt K (λ x => map (f x) (arr x)) x := sorry_proof

-- TODO: fderiv, fwdFDeriv, adjoint, revFDeriv

end OnNormedSpaces

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
theorem ArrayType.map.arg_farr.cderiv_rule
  (f : X → Elem → Elem) (arr : X → Cont)
  (hf : IsDifferentiable K (fun (xe : X×Elem) => f xe.1 xe.2))
  (harr : IsDifferentiable K arr)
  : cderiv K (fun x => map (f x) (arr x))
    =
    fun x dx =>
      let a  := arr x
      let da := cderiv K arr x dx
      let df := cderiv K (fun (xe : X×Elem) => f xe.1 xe.2)
      introElem (fun i => df (x,a[i]) (dx,da[i])) :=
by
  sorry_proof

@[ftrans]
theorem ArrayType.map.arg_farr.cderiv_rule_at
  (f : X → Elem → Elem) (arr : X → Cont)
  (hf : ∀ i, IsDifferentiableAt K (fun (xe : X×Elem) => f xe.1 xe.2) (x, (arr x)[i]))
  (harr : IsDifferentiableAt K arr x)
  : cderiv K (fun x => map (f x) (arr x)) x
    =
    fun dx =>
      let a  := arr x
      let da := cderiv K arr x dx
      introElem (fun i => 
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
theorem ArrayType.map.arg_farr.HasAdjDiff_rule
  (f : X → Elem → Elem) (arr : X → Cont)
  (hf : HasAdjDiff K (fun (xe : X×Elem) => f xe.1 xe.2)) (harr : HasAdjDiff K arr)
  : HasAdjDiff K (fun x => map (f x) (arr x)) := sorry_proof

@[ftrans]
theorem ArrayType.map.arg_farr.revDeriv_rule
  (f : X → Elem → Elem) (arr : X → Cont)
  (hf : HasAdjDiff K (fun (x,e) => f x e)) (harr : HasAdjDiff K arr)
  : revDeriv K (fun x => map (f x) (arr x))
    =
    fun x => 
      let fdf := revDerivUpdate K (fun ((x,e) : X×Elem) => f x e)
      let ada := revDerivUpdate K arr x
      let a := ada.1
      (map (f x) a, 
       fun da => 
         let (dx,da) := Function.repeatIdx (init:=((0 : X),da)) 
           (fun (i : Idx) dxa => 
             let dxai := (fdf (x,a[i])).2 dxa.2[i] (dxa.1,0)
             (dxai.1, setElem dxa.2 i dxai.2)) 
         ada.2 da dx) := sorry_proof


@[ftrans]
theorem ArrayType.map.arg_arr.revDeriv_rule
  (f : Elem → Elem) (arr : X → Cont)
  (hf : HasAdjDiff K f) (harr : HasAdjDiff K arr)
  : revDeriv K (fun x => map f (arr x))
    =
    fun x => 
      let fdf := revDeriv K f
      let ada := revDeriv K arr x
      let a := ada.1
      (map f a, 
       fun da => 
         let da := mapIdx (fun i dai => (fdf a[i]).2 dai) da
         ada.2 da) := sorry_proof


@[ftrans]
theorem ArrayType.map.arg_arr.revDerivUpdate_rule
  (f : Elem → Elem) (arr : X → Cont)
  (hf : HasAdjDiff K f) (harr : HasAdjDiff K arr)
  : revDerivUpdate K (fun x => map f (arr x))
    =
    fun x => 
      let fdf := revDeriv K f
      let ada := revDerivUpdate K arr x
      let a := ada.1
      (map f a, 
       fun da dx => 
         let da := mapIdx (fun i dai => let df := (fdf a[i]).2; df dai) da
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
-- theorem ArrayType.map.arg_farr.revDeriv_rule
--   (f : X → Elem → Elem) (arr : X → Cont)
--   (hf : HasAdjDiff K (fun (xe : X×Elem) => f xe.1 xe.2)) (harr : HasAdjDiff K arr)
--   : revDeriv K (fun x => map (f x) (arr x))
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
--       let cont : Cont := introElem fun i => if i=idx then elem else 0
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
--          let dcont : Cont := introElem fun i => if i=idx then delem else 0
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
--        let dcont : Cont := introElem fun i => if i=idx then delem else 0
--        ydf.2 dcont) :=
-- by
--   have ⟨_,_⟩ := hf
--   unfold revCDeriv; ftrans; ftrans; simp

end OnSemiInnerProductSpace


-- ArrayType.split -------------------------------------------------------------
--------------------------------------------------------------------------------


-- ArrayType.append ------------------------------------------------------------
--------------------------------------------------------------------------------
