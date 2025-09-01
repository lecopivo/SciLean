import SciLean.Analysis.Calculus.FDeriv
import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.HasFwdFDeriv
import SciLean.Analysis.Calculus.HasRevFDeriv
import SciLean.Analysis.Calculus.Notation.Deriv
-- import SciLean.Analysis.Calculus.Notation.RevDeriv

set_option linter.unusedVariables false

namespace SciLean

variable
  {R : Type _} [RCLike R]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]

set_default_scalar R

def IsOdeSolution (f : R → X → X) (t₀ : R) (x₀ : X) (x : R → X) : Prop :=
  (∀ t, (∂ x) t = f t (x t))
  ∧
  x t₀ = x₀

structure HasOdeSolution (f : R → X → X) : Prop where
  ex : ∀ t₀ x₀, ∃ x, IsOdeSolution f t₀ x₀ x

structure HasUniqueOdeSolution (f : R → X → X) : Prop extends HasOdeSolution f where
  uniq : ∀ t₀ x₀ x x', IsOdeSolution f t₀ x₀ x → IsOdeSolution f t₀ x₀ x' → x = x'

open Classical in
/-- Solution of ordinary differentiale equation.

Function `x := fun t => odeSolve f t₀ t x₀` satisfies ODE
```
∂ x t = f t (x t)
```
with initial condition `x t₀ = x₀`.

Junk value is returned if `f` does define ODE with an unique solution.
 -/
noncomputable
def odeSolve (f : R → X → X) (t₀ t : R) (x₀ : X) : X :=
  if h : HasUniqueOdeSolution f -- TODO: can we reduce it to just HasOdeSolution?
  then Classical.choose (h.ex t₀ x₀) t
  else Classical.arbitrary X

section OnNormedSpace

variable
  {R : Type _} [RCLike R]
  {W : Type _} [NormedAddCommGroup W] [NormedSpace R W]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace R Z]


@[fun_prop]
theorem odeSolve.arg_ft₀tx₀.Differentiable_rule
    (f : W → R → X → X) (t₀ t : W → R) (x₀ : W → X)
    (hf : Differentiable R (fun (w,t,x) => f w t x))
    (ht₀ : Differentiable R t₀) (ht : Differentiable R t)
    (hx : Differentiable R x₀) :
    Differentiable R fun w => odeSolve (f w) (t₀ w) (t w) (x₀ w) := sorry_proof


@[fun_trans]
theorem odeSolve.arg_ft₀tx₀.cderiv_rule
  (f : W → R → X → X) (t₀ t : W → R) (x₀ : W → X)
  (hf : Differentiable R (fun (w,t,x) => f w t x))
  (ht₀ : Differentiable R t₀) (ht : Differentiable R t)
  (hx : Differentiable R x₀)
  : fderiv R (fun w => odeSolve (f w) (t₀ w) (t w) (x₀ w))
    =
    fun w => ContinuousLinearMap.mk' R (fun dw =>
    let t₀dt₀ := fwdFDeriv R t₀ w dw
    let tdt   := fwdFDeriv R t₀ w dw
    let x₀dx₀ := fwdFDeriv R x₀ w dw
    let Tf := fwdFDeriv R (fun wkx : W×R×X => f wkx.1 wkx.2.1 wkx.2.2)

    let F := holdLet <| fun (t : R) (xdx : X×X) =>
      let x  := xdx.1
      let dx := xdx.2
      Tf (w,t,x) (dw,t₀dt₀.2,dx)

    let xdx := odeSolve F (t₀dt₀.1) (tdt.1) x₀dx₀

    (xdx.2 + tdt.2 • f w tdt.1 xdx.1)) sorry_proof
    := sorry_proof


@[fun_trans]
theorem odeSolve.arg_ft₀tx₀.fwdDeriv_rule
  (f : W → R → X → X) (t₀ t : W → R) (x₀ : W → X)
  (hf : Differentiable R (fun (w,t,x) => f w t x))
  (ht₀ : Differentiable R t₀) (ht : Differentiable R t)
  (hx : Differentiable R x₀)
  : fwdFDeriv R (fun w => odeSolve (f w) (t₀ w) (t w) (x₀ w))
    =
    fun w dw =>
      let t₀dt₀ := fwdFDeriv R t₀ w dw
      let tdt   := fwdFDeriv R t w dw
      let x₀dx₀ := fwdFDeriv R x₀ w dw
      let Tf := fwdFDeriv R (fun wkx : W×R×X => f wkx.1 wkx.2.1 wkx.2.2)

      let F := holdLet <| fun (t : R) (xdx : X×X) =>
        let x  := xdx.1
        let dx := xdx.2
        Tf (w,t,x) (dw,t₀dt₀.2,dx)

      let xdx := odeSolve F (t₀dt₀.1) (tdt.1) x₀dx₀

      (xdx.1, xdx.2 + tdt.2 • f w tdt.1 xdx.1) :=
by
  (conv => lhs; unfold fwdFDeriv)
  fun_trans
  funext w dw
  simp[fwdFDeriv]
  sorry_proof


@[data_synth]
theorem odeSolve.arg_ft₀tx₀.HasFwdFDeriv_rule
  (f : W → R → X → X) (t₀ t : W → R) (x₀ : W → X) {f' t₀' t' x₀'}
  (hf : HasFwdFDeriv R (fun (w,t,x) => f w t x) f')
  (ht₀ : HasFwdFDeriv R t₀ t₀') (ht : HasFwdFDeriv R t t')
  (hx : HasFwdFDeriv R x₀ x₀')
  : HasFwdFDeriv R (fun w => odeSolve (f w) (t₀ w) (t w) (x₀ w))
      (fun w dw =>
        let' (t₀,dt₀) := t₀' w dw
        let' (t,dt)   := t' w dw
        let' (x₀,dx₀) := x₀' w dw

        let F := holdLet <| fun (t : R) (xdx : X×X) =>
          let' (x,dx)  := xdx
          f' (w,t,x) (dw,dt₀,dx)

        let' (x,dx) := odeSolve F t₀ t x₀dx₀

        (x, dx + dt • f w t x)) := by
  sorry_proof


@[fun_prop]
theorem odeSolve.arg_x₀.IsContinuousLinearMap_rule
  (f : R → X → X) (t₀ t : R) (x₀ : W → X)
  (hf : ∀ t, IsContinuousLinearMap R (f t)) (hx₀ : IsContinuousLinearMap R x₀)
  : IsContinuousLinearMap R (fun w => odeSolve f t₀ t (x₀ w)) := sorry_proof

end OnNormedSpace

section OnAdjointSpace

set_option deprecated.oldSectionVars true

variable
  {R : Type _} [RCLike R]
  {W : Type _} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [AdjointSpace R Z] [CompleteSpace Z]

@[fun_trans]
theorem odeSolve.arg_x₀.adjoint_rule
  (f : R → X → X) (t₀ t : R) (x₀ : W → X)
  (hf : ∀ t, IsContinuousLinearMap R (f t)) (hx₀ : IsContinuousLinearMap R x₀)
  : adjoint R (fun w => odeSolve f t₀ t (x₀ w))
    =
    fun x₀' =>
      let f' := holdLet <| (fun s y => - adjoint R (f s) y)
      let y := odeSolve f' t t₀ x₀'
      adjoint R x₀ y :=
by
  -- Define adjoint solution `y` such that
  -- ∀ s, ⟪x s, y s⟫ = constant
  -- and `y t = x₀'`
  -- Now pick s := t and s := t₀ and we get the following relation:
  --    ⟪x t, x₀'⟫ = ⟪x t₀, y t₀⟫
  -- We know that `x t = S (x t₀)`, where S is the evolution operator we want to find adjoint of.
  -- Thus `y t₀ = S† x₀'`
  --
  -- We can show that `y` satisfies diffrential equation `ⅆ y t = -(f t)† (y t)`
  -- by differentiating `⟪x s, y s⟫` w.r.t. to `s`
  --
  -- Therefore we can express `y t₀` using `odeSolve`
  sorry_proof


@[data_synth]
theorem odeSolve.arg_x₀.HasAdjoint_rule
  (f : R → X → X) (t₀ t : R) (x₀ : W → X) {f' : R → _} {x₀'}
  (hf : ∀ t, HasAdjoint R (f t) (f' t)) (hx₀ : HasAdjoint R x₀ x₀')
  : HasAdjoint R
      (fun w => odeSolve f t₀ t (x₀ w))
      (fun x' =>
        let y := odeSolve (fun s y => - f' s y) t t₀ x'
        let y := x₀' y
        y) := by
  sorry_proof

@[data_synth]
theorem odeSolve.arg_x₀.HasAdjointAupdate_rule
  (f : R → X → X) (t₀ t : R) (x₀ : W → X) {f' : R → _} {x₀'}
  (hf : ∀ t, HasAdjoint R (f t) (f' t)) (hx₀ : HasAdjointUpdate R x₀ x₀')
  : HasAdjointUpdate R
      (fun w => odeSolve f t₀ t (x₀ w))
      (fun x' w' =>
        let y := odeSolve (fun s y => - f' s y) t t₀ x'
        let w' := x₀' y w'
        w') := by
  have := hx₀.hasAdjoint
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  intros; dsimp; rw[hx₀.apply_eq_zero_add]; ac_rfl


@[fun_trans]
theorem odeSolve.arg_x₀.revFDeriv_rule
  (f : R → X → X) (t₀ t : R) (x₀ : W → X)
  (hf : Differentiable R (fun (t,x) => f t x))
  (hx : Differentiable R x₀)
  : revFDeriv R (fun w => odeSolve f t₀ t (x₀ w))
    =
    fun w =>
      let' (x₀,dx₀') := revFDeriv R x₀ w
      let x := holdLet <| fun s => odeSolve f t₀ s x₀
      let dfdx := holdLet <| fun s dx' => - adjointFDeriv R (fun x' => f s x') (x s) dx'
      (x t,
       fun dx =>
         let dx := odeSolve dfdx t₀ t dx
         dx₀' dx) :=
by
  unfold adjointFDeriv revFDeriv
  fun_trans
  funext w; simp[fwdFDeriv]
  -- set_option trace.Meta.Tactic.simp.discharge true in
  -- set_option trace.Meta.Tactic.simp.unify true in
  -- set_option trace.Meta.Tactic.fun_trans.step true in
  sorry_proof


@[data_synth]
theorem odeSolve.arg_x₀.HasRevFDeriv_rule
  (f : R → X → X) (t₀ t : R) (x₀ : W → X) {f' : R → _} {x₀'}
  (hf : ∀ t, HasRevFDeriv R (f t ·) (f' t))
  (hx : HasRevFDeriv R x₀ x₀') :
  HasRevFDeriv R
    (fun w => odeSolve f t₀ t (x₀ w))
    (fun w =>
      let' (x₀,dx₀') := x₀' w
      let x := holdLet <| fun s => odeSolve f t₀ s x₀
      (x t,
       fun dx =>
         let dx := odeSolve (fun s dx' => - (f' t (x s)).2 dx') t₀ t dx
         dx₀' dx)) :=
by
  sorry_proof


-- TODO: fix this
-- @[fun_trans]
-- theorem odeSolve.arg_fx₀.revFDeriv_rule
--     (f : W → R → X → X) (t₀ t : R) (x₀ : W → X)
--     (hf : Differentiable R (fun (w,t,x) => f w t x))
--     (hx₀ : Differentiable R x₀) :
--     revFDeriv R (fun w => odeSolve (f w) t₀ t (x₀ w))
--     =
--     fun w =>
--       let x₀dx₀ := revFDeriv R x₀ w
--       let x := fun s => odeSolve (f w) t₀ s x₀dx₀.1

--       let dfdx := fun s dx => adjointFDeriv R (fun x' => f w s x') (x s) dx
--       let dfdw := fun s dx => adjointFDeriv R (fun w' => f w' s (x s)) w dx

--       let F := fun t (xw : X×W) =>
--         (  dfdx t xw.1,
--          - dfdw t xw.2)

--       (x t, fun dx =>
--         let x' := odeSolve F t t₀ (dx,0)
--         x₀dx₀.2 x'.1 + x'.2) := by sorry_proof


end OnAdjointSpace
