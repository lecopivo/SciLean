import Mathlib.Tactic.FunProp
import Mathlib

import SciLean.Core.Rand.Rand
import SciLean.Lean.Meta.Replace

open Lean Meta Qq Mathlib.Meta

namespace SciLean.Rand

variable {Z} [AddCommGroup Z] [Module ℝ Z] [MeasurableSpace Z] [TopologicalSpace Z]

-- I think this is Fubini theorem in disguise
private theorem mean_bind_mean_bind (x' : Rand X) (y' : Rand Y) (f : X → Y → Rand Z) :
  (Rand.mean do let x ← x'; return (Rand.mean do let y ← y'; f x y))
  =
  (Rand.mean do
    let x ← x'
    let y ← y'
    f x y) := sorry_proof


/-- Takes an expression of the form `f x₁.mean ... xₙ.mean` and converts it to
```
Rand.mean do
  let x₁' ← x₁
  ...
  let xₙ
  return f x₁' ... xₙ'
```
and returns a proof that that these two expressions are equal.

For this to be true `f` has to be affine in every `xᵢ` and this function tries to prove that.

Warrning: Currently we do not emit a valid proof. This is because we can't even state that
`Rand.mean` is linear function because `Rand X` is not a vector space.

One way to deal with this is to uncurry `f` and then apply `mean_affine` only once.
This would require tranforming
```
(x₁.mean, ..., xₙ.mean)
==>
Rand.mean <|
  let x₁' ← x₁
  ...
  let xₙ' ← xₙ
  pure (x₁', ..., xₙ')
``` -/
def pullMeanCore (e : Expr) : MetaM (Expr×Expr) := do

  replaceWithFVarsNoBVars e (fun e' => pure (e'.isAppOfArity ``Rand.mean 6))
    fun fvars vals e => do
      let mut e := e
      let mut prf ← mkAppM ``Eq.refl #[e]

      -- check that `e` is affine in every variable
      -- todo: combine these proofs to emit valid final proof
      let F ← mkLambdaFVars fvars e >>= mkUncurryFun fvars.size
      let Hf ← mkAppM ``IsAffineMap #[q(ℝ), F]
      let (.some _, _) ← FunProp.funProp Hf {} {}
        | throwError "the function `{← ppExpr F}` has to be affine function"


      for fvar in fvars, val in vals, i in [0:fvars.size] do

        prf := prf.replaceFVar fvar val

        let x := val.appArg!
        let f ← mkLambdaFVars #[fvar] e
        let Hf ← mkAppM ``IsAffineMap #[q(ℝ), f]
        let hf := (Expr.const ``sorryProofAxiom []).app Hf

        let prf' ← mkAppM ``Rand.mean_affine #[x, f, hf]
        prf ← mkEqTrans prf prf'
        e := (← inferType prf).appArg!

        -- squash two successive `Rand.mean` based on `mean_bind_mean_bind`
        if i > 0 then
          let thmInfo ← getConstInfo ``mean_bind_mean_bind
          let (xs,bis,b) ← forallMetaTelescope thmInfo.type
          let .some (_,lhs,rhs) := b.eq? | throwError ""
          unless (← isDefEq e lhs) do throwError "can't unify {← ppExpr e} with {← ppExpr lhs}"

          -- filter only explicit arguments
          let args := (xs.zip (.range xs.size)).filterMap
            (fun (x,i) => if bis[i]! == .default then .some x else none)
          prf ← mkEqTrans prf (← mkAppM ``mean_bind_mean_bind args)
          e ← instantiateMVars rhs

      -- unless ← isTypeCorrect prf do throwError "proof is not correct!"
      -- unless (← isDefEq e (← inferType prf).appArg!) do throwError "proof rhs is not equal e"

      return (e, prf)


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
syntax (name:=pullMeanStx) "pull_mean" : conv

open Elab.Tactic Conv
@[tactic pullMeanStx]
def pullMeanElab : Tactic := fun _ => withMainContext do

  let e ← getLhs

  let (e', prf) ← pullMeanCore e

  -- clean up the result
  let (e'', prf') ← elabConvRewrite e' #[] (← `(conv| lsimp (config := {singlePass:=true}) only))

  updateLhs e'' (← mkEqTrans prf prf')


def foo : Rand ℝ := sorry

#check (let a := foo.mean
        let b := (foo + (1:ℝ)).mean
        let c := (foo + (2:ℝ)).mean
        let d := (foo + (3:ℝ)).mean
        a + b + c + d) rewrite_by pull_mean


#check Lean.indentExpr
