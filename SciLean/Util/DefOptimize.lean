import Lean
import SciLean.Util.RewriteBy
import Mathlib.Tactic.Ring

open Lean.Parser.Tactic.Conv
open Lean.Elab.Tactic.Conv

open Lean Meta Elab Term

namespace SciLean


elab "def_optimize" f:ident "by " t:convSeq : command => do
  -- let info ← Lean.getConstInfo f.getId
  let info ← Lean.getConstInfoDefn f.getId

  Command.liftTermElabM <| do

  let (value',eq) ←
    lambdaTelescope info.value fun xs val => do
      let (value',eq) ← elabConvRewrite val #[] (← `(conv| ($t)))
      pure (← mkLambdaFVars xs value', ← mkLambdaFVars xs eq)

  let optName := info.name.append (.mkSimple "optimized")

  let optimizedDef : DefinitionVal :=
  {
    name  := optName
    type  := info.type
    value := value'
    hints := info.hints
    safety := info.safety
    levelParams := info.levelParams
  }

  addAndCompile (.defnDecl optimizedDef)


  let eqType ← forallTelescope info.type fun xs _ => do
    let lhs ← mkAppOptM info.name (xs.map .some)
    let rhs ← mkAppOptM optName (xs.map .some)
    mkForallFVars xs (← mkEq lhs rhs)

  let thmName := info.name.append (.mkSimple "optimize_rule")

  let eqTheorem : TheoremVal :=
  {
    name  := info.name.append (.mkSimple "optimize_rule")
    type  := eqType
    value := (← instantiateMVars eq)
    levelParams := info.levelParams
  }

  let csimpEntry : Compiler.CSimp.Entry := {
    fromDeclName := info.name
    toDeclName := optName
    thmName := thmName
  }

  addDecl (.thmDecl eqTheorem)
  Compiler.CSimp.ext.add csimpEntry
