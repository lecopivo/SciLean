import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Data.IndexType.Operations
import SciLean.Tactic.Autodiff

import SciLean.Meta.GenerateAddGroupHomSimp
import SciLean.Meta.GenerateFunProp

import SciLean.Analysis.Scalar.FloatAsReal

set_option linter.unusedVariables false

namespace SciLean

open IndexType Range

variable {I: Type*} [IndexType I]

section OnModule

variable
  {R : Type*} [CommSemiring R]
  {X : Type*} [AddCommGroup X] [Module R X]
  {W : Type*} [AddCommGroup W] [Module R W]

@[fun_prop]
theorem IndexType.Range.foldl.arg_opinit.IsAddGroupHom_rule (r : Range I)
  (op : W → X → I → X) (hop : ∀ i, IsAddGroupHom (fun (w,x) => op w x i))
  (init : W → X) (hinit : IsAddGroupHom init) :
  IsAddGroupHom (fun w => r.foldl (op w) (init w)) := by sorry_proof

@[fun_prop]
theorem IndexType.Range.foldl.arg_opinit.IsLinearMap_rule (r : Range I)
  (op : W → X → I → X) (hop : ∀ i, IsLinearMap R (fun (w,x) => op w x i))
  (init : W → X) (hinit : IsLinearMap R init) :
  IsLinearMap R (fun w => r.foldl (op w) (init w)) := by sorry_proof


end OnModule



section OnTopologicalSpace

variable
  {X : Type*} [TopologicalSpace X]
  {W : Type*} [TopologicalSpace W]

@[fun_prop]
theorem IndexType.Range.foldl.arg_opinit.Continuous_rule (r : Range I)
  (op : W → X → I → X) (hop : ∀ i, Continuous (fun (w,x) => op w x i))
  (init : W → X) (hinit : Continuous init) :
  Continuous (fun w => r.foldl (op w) (init w)) := by sorry_proof

end OnTopologicalSpace



section OnNormedSpace

variable
  {R : Type*} [RCLike R]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace R W]

@[fun_prop]
theorem IndexType.Range.foldl.arg_opinit.IsContinuousLinearMap_rule (r : Range I)
    (op : W → X → I → X) (hop : ∀ i, IsContinuousLinearMap R (fun (w,x) => op w x i))
    (init : W → X) (hinit : IsContinuousLinearMap R init) :
    IsContinuousLinearMap R (fun w => r.foldl (op w) (init w)) := by

  have := fun i => (hop i).2
  have := hinit.2
  simp_all
  constructor
  · fun_prop
  · simp[autoParam]; fun_prop


@[fun_prop]
theorem IndexType.Range.foldl.arg_opinit.Differentiable_rule (r : Range I)
    (op : W → X → I → X) (hop : ∀ i, Differentiable R (fun (w,x) => op w x i))
    (init : W → X) (hinit : Differentiable R init) :
    Differentiable R (fun w => r.foldl (op w) (init w)) := by sorry_proof

-- @[fun_prop]
-- theorem IndexType.Range.foldl.arg_opinit.ContDiff_rule (r : Range I) (n : ℕ∞)
--     (op : W → X → I → X) (hop : ∀ i, ContDiff R n (fun (w,x) => op w x i))
--     (init : W → X) (hinit : ContDiff R n init) :
--     ContDiff R n (fun w => r.foldl (op w) (init w)) := by sorry_proof

@[fun_trans]
theorem IndexType.Range.foldl.arg_opinit.fderiv_rule (r : Range I)
    (op : W → X → I → X) (hop : ∀ i, Differentiable R (fun (w,x) => op w x i))
    (init : W → X) (hinit : Differentiable R init) :
    fderiv R (fun w => r.foldl (op w) (init w))
    =
    fun w => ContinuousLinearMap.mk' R (fun dw : W =>
      let init' := init w
      let dinit' := fderiv R init w dw
      let op' := fun ((x,dx) : (X×X)) (i : I) =>
        let x' := op w x i
        let dx' := fderiv R (fun (w,x) => op w x i) (w,x) (dw,dx)
        (x',dx')
      (r.foldl op' (init',dinit')).2) (sorry_proof /- this is tricky -/) := by sorry_proof

@[fun_trans]
theorem IndexType.Range.foldl.arg_opinit.fwdFDeriv_rule (r : Range I)
    (op : W → X → I → X) (hop : ∀ i, Differentiable R (fun (w,x) => op w x i))
    (init : W → X) (hinit : Differentiable R init) :
    fwdFDeriv R (fun w => r.foldl (op w) (init w))
    =
    fun w dw =>
      let init' := init w
      let dinit' := fderiv R init w dw
      let op' := fun ((x,dx) : (X×X)) (i : I) =>
        let x' := op w x i
        let dx' := fderiv R (fun (w,x) => op w x i) (w,x) (dw,dx)
        (x',dx')
      (r.foldl op' (init',dinit')) := by
  unfold fwdFDeriv; fun_trans
  -- how to prove this?
  sorry_proof

end OnNormedSpace




section OnAdjointSpace

variable
  {R : Type*} [RCLike R]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X]
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace R W]

@[fun_trans]
theorem IndexType.Range.foldl.arg_opinit.adjoint_rule (r : Range I)
    (op : W → X → I → X) (hop : ∀ i, IsContinuousLinearMap R (fun (w,x) => op w x i))
    (init : W → X) (hinit : IsContinuousLinearMap R init) :
    adjoint R (fun w => r.foldl (op w) (init w))
    =
    fun x' =>
      let (w,x) := r.reverse.foldl (fun (w,x) i =>
        let (w',x) := adjoint R (fun (w,x) => op w x i) x
        (w + w', x)) (0, init w)
      let w' := adjoint R init x
      w + w' := sorry_proof

@[fun_trans]
theorem IndexType.Range.foldl.arg_init.adjoint_rule (r : Range I)
    (op : X → I → X) (hop : ∀ i, IsContinuousLinearMap R (fun x => op x i))
    (init : W → X) (hinit : IsContinuousLinearMap R init) :
    adjoint R (fun w => r.foldl op (init w))
    =
    fun x' =>
      let x := r.reverse.foldl (fun x i =>
        let x := adjoint R (fun x => op x i) x
        x) (init w)
      let w := adjoint R init x
      w := sorry_proof

variable [CompleteSpace W] [CompleteSpace X]


/-- Reverse derivative of fold - version storing closures for every step. -/
-- @[fun_trans]
theorem IndexType.Range.foldl.arg_opinit.revFDeriv_rule_closures (r : Range I)
    (op : W → X → I → X) (hop : ∀ i, Differentiable R (fun (w,x) => op w x i))
    (init : W → X) (hinit : Differentiable R init) :
    revFDeriv R (fun w => r.foldl (op w) (init w))
    =
    fun w =>
      let idi := revFDeriv R init w
      let (dops,x) := r.foldl (fun (dops,x) i =>
        let (x, dop) := revFDeriv R (fun (w,x) => op w x i) (w,x)
        (dops.push dop, x)) ((#[] : Array (X → W×X)), idi.1)
      (x, fun dx =>
        let (dw,dx) := dops.foldr (fun df (dw,dx) =>
          let (dw', dx) := df dx
          (dw + dw', dx)) (0, dx)
        let dw' := idi.2 dx
        dw + dw') := sorry_proof



/-- Reverse derivative of fold - version storing every point -/
@[fun_trans]
theorem IndexType.Range.foldl.arg_opinit.revFDeriv_rule (r : Range I)
    (op : W → X → I → X) (hop : ∀ i, Differentiable R (fun (w,x) => op w x i))
    (init : W → X) (hinit : Differentiable R init) :
    revFDeriv R (fun w => r.foldl (op w) (init w))
    =
    fun w =>
      let idi := revFDeriv R init w
      let xsx := r.foldl (fun (xs,x) i =>
        let xs := xs.push (x,i)
        let x := op w x i
        (xs,x)) ((#[] : Array (X×I)), idi.1)
      let xs := xsx.1
      let x := xsx.2
      (x, fun dx =>
        let dwx := xs.foldr (fun (x,i) (dw,dx) =>
          let dwx := (revFDeriv R (fun (w,x) => op w x i) (w,x)).2 dx
          (dw + dwx.1, dwx.2)) (0, dx)
        let dw' := idi.2 dwx.2
        dwx.1 + dw') := sorry_proof


/-- Reverse derivative of fold - version with linear operation, we do not need to store
values of the forward pass. -/
@[fun_trans]
theorem IndexType.Range.foldl.arg_opinit.revFDeriv_rule_linear (r : Range I)
    (op : W → X → I → X) (hop : ∀ i, IsContinuousLinearMap R (fun (w,x) => op w x i))
    (init : W → X) (hinit : Differentiable R init) :
    revFDeriv R (fun w => r.foldl (op w) (init w))
    =
    fun w =>
      let idi := revFDeriv R init w
      let x := r.foldl (fun x i =>
        let x := op w x i
        x) idi.1
      (x, fun dx =>
        let dwx := r.reverse.foldl (fun (dw,dx) i =>
          let dwx := (revFDeriv R (fun (w,x) => op w x i) (w,0)).2 dx
          (dw + dwx.1, dwx.2)) (0, dx)
        let dw' := idi.2 dwx.2
        dwx.1 + dw') := sorry_proof

-- TODO: add checkpointing version
