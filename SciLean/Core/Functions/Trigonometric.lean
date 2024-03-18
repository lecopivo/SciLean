import SciLean.Core.FunctionTransformations
-- import SciLean.Core.Meta.GenerateRevDeriv

open ComplexConjugate

namespace SciLean.Scalar

variable
  {R C} [Scalar R C]
  {W} [Vec C W]
  {U} [SemiInnerProductSpace C U]


--------------------------------------------------------------------------------
-- Sin -------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem sin.arg_x.CDifferentiable_rule
    (x : W → C) (hx : CDifferentiable C x) :
    CDifferentiable C fun w => sin (x w) := sorry_proof

@[fun_trans]
theorem sin.arg_x.ceriv_rule
    (x : W → C) (hx : CDifferentiable C x) :
    cderiv C (fun w => sin (x w))
    =
    fun w dw =>
      let xdx := fwdDeriv C x w dw
      let c := cos xdx.1
      xdx.2 * c := sorry_proof

@[fun_trans]
theorem sin.arg_x.fwdDeriv_rule
    (x : W → C) (hx : CDifferentiable C x) :
    fwdDeriv C (fun w => sin (x w))
    =
    fun w dw =>
      let xdx := fwdDeriv C x w dw
      let s := sin xdx.1
      let c := cos xdx.1
      (s, xdx.2 * c) := by
  unfold fwdDeriv; fun_trans; rfl


@[fun_trans]
theorem sin.arg_x.HasAdjDiff_rule
    (x : U → C) (hx : HasAdjDiff C x) :
    HasAdjDiff C (fun u => sin (x u)) := by
  intro x
  constructor
  fun_prop
  fun_trans [fwdDeriv]; fun_prop


open ComplexConjugate
@[fun_trans]
theorem sin.arg_x.revDeriv_rule
    (x : U → C) (hx : HasAdjDiff C x) :
    revDeriv C (fun u => sin (x u))
    =
    fun u =>
      let xdx := revDeriv C x u
      (sin xdx.1, fun dy => xdx.2 (conj (cos xdx.1) * dy)) := by
  unfold revDeriv
  fun_trans only [fwdDeriv, smul_push, ftrans_simp]


--------------------------------------------------------------------------------
-- Cos -------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem cos.arg_x.CDifferentiable_rule
  (x : W → C) (hx : CDifferentiable C x)
  : CDifferentiable C fun w => cos (x w) := sorry_proof

@[fun_trans]
theorem cos.arg_x.ceriv_rule
  (x : W → C) (hx : CDifferentiable C x)
  : cderiv C (fun w => cos (x w))
    =
    fun w dw =>
      let xdx := fwdDeriv C x w dw
      let s := -sin xdx.1
      xdx.2 * s := sorry_proof

@[fun_trans]
theorem cos.arg_x.fwdDeriv_rule
  (x : W → C) (hx : CDifferentiable C x)
  : fwdDeriv C (fun w => cos (x w))
    =
    fun w dw =>
      let xdx := fwdDeriv C x w dw
      let s := sin xdx.1
      let c := cos xdx.1
      (c, xdx.2 * -s) :=
by
  unfold fwdDeriv; fun_trans; rfl

@[fun_trans]
theorem cos.arg_x.HasAdjDiff_rule
    (x : U → C) (hx : HasAdjDiff C x) :
    HasAdjDiff C (fun u => cos (x u)) := by
  intro x
  constructor
  fun_prop
  fun_trans [fwdDeriv]; fun_prop


open ComplexConjugate
@[fun_trans]
theorem cos.arg_x.revDeriv_rule
    (x : U → C) (hx : HasAdjDiff C x) :
    revDeriv C (fun u => cos (x u))
    =
    fun u =>
      let xdx := revDeriv C x u
      (cos xdx.1, fun dy => xdx.2 (conj (- sin xdx.1) * dy)) := by
  unfold revDeriv
  fun_trans only [fwdDeriv, smul_push, ftrans_simp]


--------------------------------------------------------------------------------
-- Tanh -------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem tanh.arg_x.CDifferentiable_rule
    (x : W → C) (hx : CDifferentiable C x) :
    CDifferentiable C fun w => tanh (x w) := sorry_proof

@[fun_trans]
theorem tanh.arg_x.ceriv_rule
    (x : W → C) (hx : CDifferentiable C x) :
    cderiv C (fun w => tanh (x w))
    =
    fun w dw =>
      let xdx := fwdDeriv C x w dw
      let t := tanh xdx.1
      let dt := 1 - t^2
      xdx.2 * dt := sorry_proof

@[fun_trans]
theorem tanh.arg_x.fwdDeriv_rule
    (x : W → C) (hx : CDifferentiable C x) :
    fwdDeriv C (fun w => tanh (x w))
    =
    fun w dw =>
      let xdx := fwdDeriv C x w dw
      let t := tanh xdx.1
      let dt := 1-t^2
      (t, xdx.2 * dt) :=
by
  unfold fwdDeriv; fun_trans; rfl


@[fun_trans]
theorem tanh.arg_x.HasAdjDiff_rule
    (x : U → C) (hx : HasAdjDiff C x) :
    HasAdjDiff C (fun u => tanh (x u)) := by
  intro x
  constructor
  fun_prop
  fun_trans [fwdDeriv]; fun_prop


open ComplexConjugate
@[fun_trans]
theorem tanh.arg_x.revDeriv_rule
    (x : U → C) (hx : HasAdjDiff C x) :
    revDeriv C (fun u => tanh (x u))
    =
    fun u =>
      let xdx := revDeriv C x u
      (tanh xdx.1, fun dy => xdx.2 (conj (1 - tanh (xdx.1) ^ 2) * dy)) := by
  unfold revDeriv
  fun_trans only [fwdDeriv, smul_push, ftrans_simp]
