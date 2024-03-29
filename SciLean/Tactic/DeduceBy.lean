import Lean
import Qq

import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.UInt
import Mathlib.Tactic.Ring

import SciLean.Util.RewriteBy

namespace SciLean

syntax (name:=deduceBy) "deduce_by " conv : tactic

namespace DeduceBy
open Qq Lean Meta

/--
Assuming that `a` has mvar `m` and `b` is an expression.

Return mvar `m` and value `x` for it such that `a=b` is likely to hold.

Examples:
- `a = 4 * ?m + 2`, `b = 2*n` => `(?m, (2*n-2)/4)`
-/
partial def invertNat (a b : Q(Nat)) : MetaM (Q(Nat) × Q(Nat)) := do
  if a.isMVar then
    return (a,b)
  else
    match a with
    | ~q($x * $y) =>
      if x.hasMVar
      then invertNat x q($b / $y)
      else invertNat y q($b / $x)
    | ~q($x / $y) =>
      if x.hasMVar
      then invertNat x q($b * $y)
      else invertNat y q($x / $b)
    | ~q($x + $y) =>
      if x.hasMVar
      then invertNat x q($b - $y)
      else invertNat y q($b - $x)
    | ~q($x - $y) =>
      if x.hasMVar
      then invertNat x q($b + $y)
      else invertNat y q($x - $b)
    | _ =>
      throwError s!"`decuce_by` does not support Nat operation {← ppExpr a}"


open Lean Meta Elab Tactic Qq
@[tactic deduceBy]
partial def deduceByTactic : Tactic
| `(tactic| deduce_by $t:conv) => do

  let goal ← getMainGoal
  let .some (_,lhs,rhs) := Expr.eq? (← goal.getType) | throwError "expected `?m = e`, got {← ppExpr (← goal.getType)}"

  if ¬lhs.hasMVar ∨ ¬rhs.hasMVar then
    let prf ← elabTerm (← `(by (conv => ($t;$t)); try simp)) (← goal.getType)
    goal.assign prf
    return ()

  -- if ¬lhs.isMVar then
  --   throwError "lhs is not mvar"

  -- now we assume that a is mvar and b is and expression we want to simplify
  let (goal,a,b) ←
    if lhs.hasMVar then
      pure (goal,lhs,rhs)
    else
      let goal' ← mkFreshExprMVar (← mkEq rhs lhs)
      goal.assign (← mkEqSymm goal')
      pure (goal'.mvarId!,rhs,lhs)

  let A ← inferType a
  if A == q(Nat) then
    let (m,x) ← invertNat a b
    let (x', _) ← elabConvRewrite x #[] t
    m.mvarId!.assign x'
    let subgoals ← evalTacticAt (← `(tactic| (conv => (conv => lhs; $t); (conv => rhs; $t)); try field_simp)) goal
    if subgoals.length ≠ 0 then
      throwError "`decide_by` failed to show {← ppExpr (← goal.getType)}"

  else
    let (b',prf) ← elabConvRewrite b #[] t
    a.mvarId!.assign b'
    goal.assign prf
| _ => throwUnsupportedSyntax


-- def foo {n : Nat} {m : Nat} (i : Fin n) (h : 2 * m = n := by deduce_by ring_nf) : Fin m := ⟨i/2, sorry⟩

-- def bar {n : Nat} (i : Fin n) : Fin (n/2) := ⟨i/2, sorry⟩

-- variable (n : Nat)

-- #check foo (8 : Fin 10)
-- #eval foo (8 : Fin 10)

-- #check bar (8 : Fin 10)

-- variable (i : Fin (2*n))
-- #eval foo i
