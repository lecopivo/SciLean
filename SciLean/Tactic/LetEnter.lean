import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv
open Meta

private def getContext : MetaM Simp.Context := do
  Simp.mkContext
    (config        := Simp.neutralConfig)
    (simpTheorems  := {})
    (congrTheorems := (← getSimpCongrTheorems))

private def pre (letName : Name) (state : IO.Ref (MVarId ⊕ Nat)) (e : Expr) : SimpM Simp.Step := do
  match ← state.get with
  | .inl _ => return Simp.Step.visit { expr := e }
  | .inr n =>
  if e.isLet && e.letName! = letName then
    if n ≠ 0 then
      state.set (.inr (n-1))
      return Simp.Step.visit { expr := e }
    else
      let (rhs, newGoal) ← mkConvGoalFor e.letValue!
      state.set (.inl newGoal.mvarId!)
      let proof ← mkCongrArg (.lam e.letName! e.letType! e.letBody! default) newGoal
      return Simp.Step.done { expr := .letE e.letName! e.letType! rhs e.letBody! false, proof? := proof }
  else
    return Simp.Step.visit { expr := e }


/-- Conv tactic `enter_let x` focuses on the value of let binding `let x := _`

`enter_let x n` focuses on `(n-1)`th occurrence of let binding `let x := _`
-/
syntax (name := let_enter) " enter_let" ident (num)? : conv

@[tactic let_enter]
def convLetEnter : Tactic
| `(conv| enter_let $id:ident $[$n]?) => withMainContext do
    let lhs ← getLhs
    let n := n.map (λ n => n.getNat) |>.getD 0
    let state ← IO.mkRef (.inr n)
    let ctx ← getContext
    let (result, _) ← Simp.main lhs ctx (methods := { pre := pre id.getId state })
    let .inl subgoal ← state.get
      | throwError "'let_enter' conv tacitc failed, let binding '{id.getId}' not found!"
    (← getRhs).mvarId!.assign result.expr
    (← getMainGoal).assign (← result.getProof)
    replaceMainGoal [subgoal]
  | _ => throwUnsupportedSyntax



-- example
--   : (λ x : Nat =>
--       let a := x
--       let b := x + a
--       λ y =>
--       let c := x + a + b + y
--       let d := x + a + b
--       a + b + (let z := 10; c + z) + d + y)
--     =
--     (λ x : Nat =>
--       let a := x
--       let b := x + a
--       λ y =>
--       let c := x + a + b + y
--       let d := x + a + b
--       a + b + (let z := 10; c + z) + d + y)
--   :=
-- by
--   conv =>
--     lhs
--     enter_let a
