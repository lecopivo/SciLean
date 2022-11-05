import Lean

namespace SciLean.Meta.CustomSimp

open Lean Meta Elab Elab.Term


/-- Prevent applying the theorem if the specified argument is equation to the specified value. -/
syntax (name := simp_guard) "simp_guard" ident term : attr


initialize simpGuardAttr : ParametricAttribute (Nat × Expr) ←
  registerParametricAttribute {
    name := `simp_guard
    descr := "Do not apply this simp theorem if the specified argument has the specified value."
    getParam := fun name => fun
      | `(attr| simp_guard $id $val) => MetaM.run' <| TermElabM.run' do
        dbg_trace s!"decl name: {name}"
        let info ← getConstInfo name

        let (nth, value) ← forallTelescope info.type λ args _ => do
          let mut i := 0
          for arg in args do
            let argDecl ← getFVarLocalDecl arg
            if (argDecl.userName = id.getId) then
              let value ← elabTerm val argDecl.type
              if ¬(← isDefEq (← inferType value) argDecl.type) then
                throwError "Guard value `{val.raw.prettyPrint}` has to have type `{argDecl.type}`"  

              return (i, value)
            i := i + 1

          throwError "Theorem does not have an argument with the name `{id.getId}`"  

        pure (nth, value)
      | _ => Elab.throwUnsupportedSyntax
  }


def hasCustomSimpGuard (env : Environment) (n : Name) : Bool :=
  match simpGuardAttr.getParam? env n with
  | some _ => true
  | none => false

