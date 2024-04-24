import Lean
import Qq

import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.UInt
import Mathlib.Tactic.Ring

import SciLean.Util.RewriteBy

namespace SciLean

/-- Tactic used to reduce expressions in return types of a function. For example if the return
type is `Fin (n*m)` and we call the function with `n=5`, `m=3` we want the return type to be
`Fin 15` rather than `Fin 5*3`.

Consider this function
```
def halve (i : Fin n) : Fin (n/2) := ...
```
it is not ideal that the return type is `Fin (n/2)`. For example, for `i : Fin 10` calling
`halve i` has type `Fin 10/2` which is undesirable. We would like to simplify `10/2` in the type.

Using `deduce_by` you can write
```
def halve {n m} (i : Fin n) (hm : 2 * m = n := by deduce_by norm_num) := ...
```
Now for `i : Fin 10`, calling `halve i` will have type `

The tactic `deduce_by <conv>` expects equality `lhs = rhs` where `lhs` contains metavariable i.e.
variable which is not yet determined like `m` when we call `halve`. `deduce_by` will express
the meta variable from this equality e.g. `n/2` in the above example, simplifies the expression
with provided conv tactic and uses it also to prove the equality ofter the asigment.

For example:
- For `i : Fin 10` calling `halve i` will first look at `2 * ?m = 10` and solves it for `?m` i.e.
  `?m = 10 / 2`. The provided tactic, like `norm_num`, is called on `10 / 2` yielding `5`. The result
  `5` is assigned to `?m`. As the last them the tactic tries to prove `2 * 5 = 10` which succeeds
  and the resulting proof is provided to the `hm` argument of `halve` and calling `halve i` succeeds.

- For `i : Fin 11` calling `halve i` will first look at `2 * ?m = 11` and solves it for `?m` i.e.
  `?m = 11 / 2`. The provided tactic, like `norm_num`, is called on `11 / 2` yielding `5`. The result
  `5` is assigned to `?m`. As the last them the tactic tries to prove `2 * 5 = 11` which fails.
  Thus calling `halve i` is unsuccessful.

Limitation:
  When adding function argument like `{x} (hx : lhs = rhs := deduce_by <conv>)` then
  - if `x` is of type `Nat` then `lhs` can be expression involing arithemtic operations `+,-,*,/`
  - if `x` if of any other type then `lhs` has to be just `x`
 -/
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

  if ¬lhs.hasMVar && ¬rhs.hasMVar then
    let prf ← elabTerm (← `(by (conv => ($t;$t)); try simp)) (← goal.getType)
    goal.assign prf
    return ()

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

-- #exit

-- #check bar (8 : Fin 10)

-- variable (i : Fin (2*n))
-- #eval foo i
