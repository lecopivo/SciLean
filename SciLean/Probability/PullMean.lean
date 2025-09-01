import Lean.Meta.Transform

import Mathlib.Tactic.FunProp

import SciLean.Probability.Rand
import SciLean.Probability.IsAffineRandMap
import SciLean.Tactic.LSimp

open Lean Meta Qq Mathlib.Meta

namespace SciLean.Rand

variable {X} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X] [TopologicalSpace X]
variable {Y} [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Y] [TopologicalSpace Y]
variable {Z} [AddCommGroup Z] [Module ℝ Z] [MeasurableSpace Z] [TopologicalSpace Z]

set_option linter.unusedVariables false

private theorem let_mean_mean (x' : Rand X) (f : X → Rand Y) (hf : IsAffineRandMap f) :
  (let x := x'.mean; (f x).mean)
  =
  (Rand.mean do
    let x ← x'
    f x) := sorry_proof

private theorem let_mean (x' : Rand X) (f : X → Y) (hf : IsAffineMap ℝ f) :
  (let x := x'.mean; f x)
  =
  (Rand.mean do
    let x ← x'
    return (f x)) := sorry_proof


simproc_decl pullMean (_) := fun e => do

  match e with
  -- todo: handle app and lam case
  | .letE n t v b dep =>
    match v.isAppOfArity ``Rand.mean 6, b.isAppOfArity ``Rand.mean 6 with
    | true, true =>
      let x := v.appArg!
      let f := Expr.lam n t b.appArg! .default
      let Hf ← mkAppM ``IsAffineRandMap #[f]
      let (.some hf, _) ← FunProp.funProp Hf {} {} -- todo: utilized `simp` cache!
        | throwError "the subexpression `{← ppExpr f}` has to be affine function"
      let prf ← mkAppM ``let_mean_mean #[x,f,hf.proof]
      let rhs := (← inferType prf).appArg!
      return .continue (.some { expr := rhs, proof? := prf })
    | true, false =>
      let x := v.appArg!
      let f := Expr.lam n t b .default
      let Hf ← mkAppM ``IsAffineMap #[q(ℝ), f]
      let (.some hf, _) ← FunProp.funProp Hf {} {} -- todo: utilized `simp` cache!
        | throwError "the subexpression `{← ppExpr f}` has to be affine function"
      let prf ← mkAppM ``let_mean #[x,f,hf.proof]
      let rhs := (← inferType prf).appArg!
      return .continue (.some { expr := rhs, proof? := prf })
    | false, true =>
      let f := b.appFn!
      let x := b.appArg!
      if f.hasLooseBVar 0 then throwError s!"can't pull mean out of {← ppExpr e}"
      return .continue (.some { expr := (f.app (.letE n t v x dep)) })
    | false, false => return .continue
  | _ => return .continue



/-- This tactic tries to pull `Rand.mean` from subexpressions and put it on top level of the
expression.

For example, running `pull_mean` on
```
let x := x'.mean
let y := y'.mean
x + y
```
will product
```
Rand.mean do
  let x ← x'
  let y ← y'
  return x + y
```

In general, it will take an expression of the form `f x₁'.mean ... xₙ'.mean` and turns it into
```
Rand.mean do
  let x₁ ← x₁'
  ...
  let xₙ ← xₙ'
  return f x₁ ... xₙ
```
this tactic succeeds only if `f` is affine function in all of its arguments!
 -/
macro "pull_mean" : conv => `(conv|
   (simp (config:={zeta:=false,singlePass:=true}) only [pullMean];
    lsimp (config:={zeta:=false}) only [pure_bind, bind_assoc, bind_pure]))
