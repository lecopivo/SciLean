import Lean

namespace SciLean.Meta.CustomSimp

open Lean Meta Elab Elab.Term


-- Maybe add option to write logical formulas in simp guard
-- something like @[simp_guard (n = 0) || (m = n)]

/-- Prevent applying the theorem if the specified argument is equation to the specified value.

Warning: It only works with custom simplifiers! Normal simplifier ignores this.


Example:
---
Adding the following simp guard to the chain rule prevents appying it if `g` is an identity function.

```
  @[simp_guard g (λ x => x)]
  theorem chain_rule {α β γ : Type}
    (f : β → γ) (g : α → β)
    : ∂ (λ x => f (g x)) = λ x dx => ∂ f (g x) (∂ g x dx) := ...
```
-/
syntax (name := simp_guard) "simp_guard" (ident term),+ : attr

initialize simpGuardAttr : ParametricAttribute (Array (Nat × Expr × Nat)) ←
  registerParametricAttribute {
    name := `simp_guard
    descr := "Do not apply this simp theorem if the specified argument has the specified value."
    getParam := fun name => fun
      | `(attr| simp_guard $[$ids $vals],*) =>
        MetaM.run' <| TermElabM.run' <| (ids.zip vals).mapM λ (id, val) => do
          let info ← getConstInfo name

          let nth ← forallTelescope info.type λ args _ => do
            let i? ← args.findIdxM?
              (λ arg => do
                let argDecl ← getFVarLocalDecl arg
                pure (argDecl.userName = id.getId))
            match i? with
            | some i => pure i
            | none => throwError "Theorem does not have an argument with the name `{id.getId}`"

          -- `valueFun` is a function taking all theorem arguments [0,..,nth) and returning guard value
          let (valFun, numMVars) ← forallBoundedTelescope info.type nth λ args _ => do
            let value ← elabTerm val none
            let value ← abstractMVars value

            pure (← mkLambdaFVars args value.expr, value.numMVars)

          pure (nth, valFun, numMVars)
      | _ => Elab.throwUnsupportedSyntax
  }


def hasCustomSimpGuard (env : Environment) (n : Name) : Bool :=
  match simpGuardAttr.getParam? env n with
  | some _ => true
  | none => false
