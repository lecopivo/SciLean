import Lean

namespace SciLean.Meta.CustomSimp

open Lean Meta Elab Elab.Term


/-- Prevent applying the theorem if the specified argument is equation to the specified value. 

WARNING: It only works with custom simplifiers! Normal simplifier ignores this.
-/
syntax (name := simp_guard) "simp_guard" ident term : attr

initialize simpGuardAttr : ParametricAttribute (Nat × Expr) ←
  registerParametricAttribute {
    name := `simp_guard
    descr := "Do not apply this simp theorem if the specified argument has the specified value."
    getParam := fun name => fun
      | `(attr| simp_guard $id $val) => MetaM.run' <| TermElabM.run' do
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
        let valFun ← forallBoundedTelescope info.type nth λ args _ => do
          let value ← elabTerm val none
          if value.hasMVar then
            throwError "Simp guard value `{value}` contains metavariable! This is not supported currently!"
          mkLambdaFVars args value

        pure (nth, valFun)
      | _ => Elab.throwUnsupportedSyntax
  }


def hasCustomSimpGuard (env : Environment) (n : Name) : Bool :=
  match simpGuardAttr.getParam? env n with
  | some _ => true
  | none => false
