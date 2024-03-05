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


-- Indexed.get -----------------------------------------------------------------
--------------------------------------------------------------------------------

section OnVectorSpaces

variable {R : Type} [CommSemiring R] [AddCommGroup Elem] [Module R Elem]

@[fun_prop]
theorem LeanColls.Indexed.get.arg_cont.IsLinearMap_rule_simple (idx : Idx) :
    IsLinearMap R (fun xs : Cont => xs[idx]) := by
  constructor
  . intros; simp
  . intros; simp

#generate_linear_map_simps LeanColls.Indexed.get.arg_cont.IsLinearMap_rule_simple

end OnVectorSpaces

section OnNormedSpaces

variable
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  [NormedAddCommGroup Elem] [NormedSpace K Elem]

@[fun_prop]
theorem LeanColls.Indexed.get.arg_cont.IsContinuousLinearMap_rule_simple :
    IsContinuousLinearMap K (λ cont : Cont => cont[idx]) := sorry_proof

-- automatically infer: Differentiable, DifferentiableAt, ContDiff, fderiv, fwdFDeriv

end OnNormedSpaces

section OnVec

variable
  {X : Type} [Vec K X]
  [Vec K Elem]

@[fun_prop]
theorem LeanColls.Indexed.get.arg_cont.IsSmoothLinearMap_rule_simple
  (idx : Idx)
  : IsSmoothLinearMap K (fun xs : Cont => xs[idx]) := sorry_proof

-- automatically infer: CDifferentiable, CDifferentiableAt, CContDiff, cderiv, fwdDeriv

end OnVec

section OnSemiInnerProductSpace

variable
  {X : Type} [SemiInnerProductSpace K X]
  [SemiInnerProductSpace K Elem]

@[fun_prop]
theorem LeanColls.Indexed.get.arg_cont.HasSemiAdjoint_rule_simple (idx : Idx) :
    HasSemiAdjoint K (fun cont : Cont => cont[idx]) := sorry_proof

@[fun_trans]
theorem LeanColls.Indexed.get.arg_cont.semiAdjoint_rule_simple (idx : Idx) :
    semiAdjoint K (fun cont : Cont => cont[idx])
    =
    fun elem => oneHot (X:=Cont) idx elem :=
by
  sorry_proof

@[fun_trans]
theorem LeanColls.Indexed.get.arg_cont.revCDeriv_rule
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

@[fun_trans]
theorem LeanColls.Indexed.get.arg_cont.revCDerivUpdate_rule
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

@[fun_trans]
theorem LeanColls.Indexed.get.arg_cont.revCDerivProj_rule
  {J ElemJ} [StructType Elem J ElemJ] [IndexType J] [LawfulIndexType J] [DecidableEq J]
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
theorem LeanColls.Indexed.set.arg_contelem.IsLinearMap_rule_simple (idx : Idx) :
    IsLinearMap R (fun ((cont,elem) : Cont×Elem) => Indexed.set cont idx elem) := by
  constructor
  . intros; simp; ext; sorry_proof
  . intros; simp; ext; sorry_proof

#generate_linear_map_simps LeanColls.Indexed.set.arg_contelem.IsLinearMap_rule_simple

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
  . intros; ext; simp
  . intros; ext; simp

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

end OnSemiInnerProductSpace

#exit

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

end OnNormedSpaces

namespace SciLean
section OnVec

variable
  {X : Type _} [Vec K X]
  [Vec K Elem]

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

@[fun_prop]
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

@[fun_prop]
theorem ArrayType.max.arg_cont.HasAdjDiff_rule
  [LT Elem] [∀ x y : Elem, Decidable (x < y)] [Inhabited Idx]
  (arr : X → Cont)
  (hf : HasAdjDiff K arr) (hfalse : fun_propParam False)
  : HasAdjDiff K (fun x => max (arr x)) := sorry_proof


@[ftrans]
theorem ArrayType.max.arg_arr.revDeriv_rule
  [LT Elem] [∀ x y : Elem, Decidable (x < y)] [Inhabited Idx]
  (arr : X → Cont)
  (hf : HasAdjDiff K arr) (hfalse : fun_propParam False)
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
  (hf : HasAdjDiff K arr) (hfalse : fun_propParam False)
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

end OnSemiInnerProductSpace


-- ArrayType.split -------------------------------------------------------------
--------------------------------------------------------------------------------


-- ArrayType.append ------------------------------------------------------------
--------------------------------------------------------------------------------
