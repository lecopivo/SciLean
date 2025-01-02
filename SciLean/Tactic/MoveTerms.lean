import Lean

import Mathlib.Algebra.Group.Defs

import SciLean.Lean.Expr
import SciLean.Lean.Meta.Basic
import SciLean.Util.SorryProof

namespace SciLean

open  Lean Elab Tactic Conv Meta

namespace MoveTermsTo

private def splitAddOfTypeImpl (e E : Expr) (negate : Bool) : MetaM (Array Expr) := do
  match e with
  | .mdata _ e' => return ← splitAddOfTypeImpl e' E negate
  | Expr.mkApp6 (.const name _) X Y Z _ x y =>
    if (← isDefEq X E) &&
       (← isDefEq Y E) &&
       (← isDefEq Z E) then
       if name = ``HAdd.hAdd then
         let l1 ← splitAddOfTypeImpl x E negate
         let l2 ← splitAddOfTypeImpl y E negate
         return l1.append l2
       else if name = ``HSub.hSub then
         let l1 ← splitAddOfTypeImpl x E negate
         let l2 ← splitAddOfTypeImpl y E !negate
         return l1.append l2
  | Expr.mkApp3 (.const name _) X _ x =>
    if (← isDefEq X E) &&
       name = ``Neg.neg then
       return ← splitAddOfTypeImpl x E !negate
  | _ => pure ()

  if negate then
    return #[← mkAppM ``Neg.neg #[e]]
  else
    return #[e]



/-- Take and expresion of the form `a₁ + ... + aₙ` and return array `#[a₁, ..., aₙ]`. It ensures that all `aᵢ` have the type `E`, this is to prevent splitting unexpected heterogenous addition.

The term `e` can also contain negation, subtraction and arbitrary bracketing.

For example, calling this function on

```
  a₁ - (a₂ - a₃) + a₄
```

will return

```
  #[a₁,-a₂,a₃,a₄]
```
-/
def splitAddOfType (e E : Expr): MetaM (Array Expr) := splitAddOfTypeImpl e E false


/-- `move x y terms_to_lhs` moves all terms with `x` and `y` to the left hand side of an equality

WARNING: this tactic uses sorry TODO: implement proof generation
-/
syntax (name := move_terms_to) "move" ident+ "terms_to_lhs" : conv

@[tactic move_terms_to] def moveTermsToTactic : Tactic
  | `(conv| move $xs* terms_to_lhs) => withMainContext do

    let lhs ← getLhs
    let .some (E, eqLhs, eqRhs) := lhs.app3? ``Eq
      | throwError "the expression {← ppExpr lhs} is not an equality"

    -- make sure that specified variables are valid free variables
    let names := xs.map (·.getId)
    let lctx ← getLCtx
    let fvars ← names.mapM (λ name => do
      let .some decl := lctx.findFromUserName? name
        | throwError s!"not free variable with the name {name}"
      return decl.fvarId)

    -- check that we are indeed working with additive commutative group
    let group ← mkAppM ``AddCommGroup #[E]
    if Option.isNone <| (← Meta.synthInstance? group) then
      throwError "failed to synthesize {← ppExpr group}, this tactic is only applicable to types with `AddCommGroup` structure"

    -- split terms on rhs
    let terms ← splitAddOfType eqRhs E
    let (eqRhsIn, eqRhsOut) := terms.partition (fun term => fvars.any (fun fvar => term.containsFVar fvar))

    let eqLhs' ← mkAppFoldlM ``HSub.hSub (#[eqLhs].append eqRhsIn)
    let eqRhs' ← mkAppFoldlM ``HAdd.hAdd eqRhsOut

    let lhs' ← mkEq eqLhs' eqRhs'

    -- TODO: generate valid proof
    let eqProof ← mkAppOptM ``sorryProofAxiom #[← mkEq lhs lhs']

    updateLhs lhs' eqProof

  | _ => throwUnsupportedSyntax
