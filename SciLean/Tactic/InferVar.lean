import Lean
import Qq

import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.UInt
import Mathlib.Tactic.Ring

import SciLean.Util.RewriteBy

namespace SciLean

open Lean Parser Tactic Conv in
syntax normalizer := atomic(" (" patternIgnore(&"normalizer" <|> &"norm")) " := " withoutPosition(convSeq) ")"


/- Tactic used to reduce expressions in return types of a function. For example if the return
type is `Fin (n*m)` and we call the function with `n=5`, `m=3` we want the return type to be
`Fin 15` rather than `Fin 5*3`.

Another way of looking at this tactic is that it tries to prove equality `lhs = rhs` where `lhs`
contains an unknown variable(metavariable). This tactic will try to fill in this variable and
prove the equality. For example, `5 * ?m = 15 := by infer_var` will assign `3` to `?m` and return
proof that `5 * 3 = 15`.

An example of intended application is following. Consider this function
```
def halve (i : Fin n) : Fin (n/2) := ...
```
it is not ideal that the return type is `Fin (n/2)`. For example, for `i : Fin 10` calling
`halve i` has type `Fin 10/2` which is undesirable. We would like to simplify `10/2` in the type.

Using `infer_var` you can write
```
def halve {n m} (i : Fin n) (hm : 2 * m = n := by infer_var) := ...
```
Now for `i : Fin 10`, calling `halve i` will have type `

The tactic `infer_var <conv>` expects equality `lhs = rhs` where `lhs` contains metavariable i.e.
variable which is not yet determined like `m` when we call `halve`. `infer_var` will express
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
  When adding function argument like `{x} (hx : lhs = rhs := infer_var <conv>)` then
  - if `x` is of type `Nat` then `lhs` can be expression involing arithemtic operations `+,-,*,/`
  - if `x` if of any other type then `lhs` has to be just `x`
 -/
open Lean.Parser.Tactic in
syntax (name:=inferVar) "infer_var " (normalizer)? (discharger)? : tactic


namespace InferVar
open Qq Lean Meta

/--
Assuming that `a` has mvar `m` and `b` is an expression.

Return mvar `m` and value `x` for it such that `a=b` is likely to hold.

Examples:
- `a = 4 * ?m + 2`, `b = 2*n` => `(?m, (2*n-2)/4)`
-/
partial def invertNat (a b : Q(Nat)) : MetaM (Q(Nat) × Q(Nat)) := do
  if a.getAppFn.isMVar then
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
      throwError s!"`infer_var` does not support Nat operation {← ppExpr a}"


open Lean Meta Elab Tactic Qq
@[tactic inferVar]
partial def deduceByTactic : Tactic
| `(tactic| infer_var (norm:=$c) (disch:=$t)) => do


  let goal ← getMainGoal

  trace[Meta.Tactic.infer_var] "goal {← ppExpr (← goal.getType)}"

  let .some (_,lhs,rhs) := Expr.eq? (← goal.getType)
    | throwError "infer_var: expected goal of the form `?m = e`, got {← ppExpr (← goal.getType)}"

  if ¬lhs.hasMVar && ¬rhs.hasMVar then
    let subgoals ← evalTacticAt t goal
    if subgoals.length = 0 then
      return ()
    else
      throwError "infer_var: discharger `{Syntax.prettyPrint t}` failed proving \
                  {← ppExpr (←goal.getType)}"

  -- now we assume that a is mvar and b is and expression we want to simplify
  let (goal,a,b) ←
    if lhs.hasMVar then
      pure (goal,lhs,rhs)
    else
      let goal' ← mkFreshExprMVar (← mkEq rhs lhs)
      goal.assign (← mkEqSymm goal')
      pure (goal'.mvarId!,rhs,lhs)

  trace[Meta.Tactic.infer_var] "infering {← ppExpr a} from {← ppExpr b}"

  let A ← inferType a
  if A == q(Nat) then
    let (m,x) ← invertNat a b
    trace[Meta.Tactic.infer_var] "candidate value for {← ppExpr m} is {← ppExpr x}"
    let (x', _) ← elabConvRewrite x #[] (← `(conv| ($c)))
    trace[Meta.Tactic.infer_var] "simplified candidate value is {← ppExpr x'}"
    unless (← isDefEq m x') do throwError "infer_var: failed to assign {← ppExpr x'} to {← ppExpr m}"
    let subgoals ←
      evalTacticAt (← `(tactic| (conv => (conv => lhs; ($c)); (conv => rhs; ($c))); (try $t))) goal
    if subgoals.length ≠ 0 then
      throwError "infer_var: discharger `{Syntax.prettyPrint t}` failed proving {← ppExpr (← goal.getType)}"
  else
    let (b',prf) ← elabConvRewrite b #[] (← `(conv| ($c)))
    trace[Meta.Tactic.infer_var] "simplified value {← ppExpr b'}"
    a.mvarId!.assign b'
    goal.assign prf
| `(tactic| infer_var) => do
  evalTactic (← `(tactic| infer_var (norm:=norm_num) (disch:=simp)))
| _ => throwUnsupportedSyntax




initialize registerTraceClass `Meta.Tactic.infer_var
