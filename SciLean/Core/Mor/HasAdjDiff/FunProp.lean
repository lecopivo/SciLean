import SciLean.FunPropCore
import SciLean.Core.Mor.HasAdjDiff.Core

namespace SciLean.FunProp

open Lean.TSyntax.Compat -- makes old untyped syntax code compile

open Lean

syntax "hasAdjDiff"   bracketedBinder* ":=" term : argProp
syntax "hasAdjDiff"   bracketedBinder*           : argProp

macro_rules
| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
      hasAdjDiff $extraParms:bracketedBinder* := $proof:term) => do

  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]!
  let postArgs := getExplicitArgs postParms

  let darg  := Lean.mkIdent $ arg.getId.appendBefore "d"
  let dparm := mkNode ``Lean.Parser.Term.explicitBinder #[parm[0], mkNullNode #[darg], parm[2], parm[3], parm[4]]

  let funName  := funId.getId
  let declBase := funName.append $ x.getId.appendBefore "arg_"
  let instId := Lean.mkIdent $ declBase.append "hasAdjDiff"

  let lam ← `((fun $parm => $funId $preArgs* $arg $postArgs*))
  let type ← `(SciLean.HasAdjDiff $lam)

  `(instance $instId:ident $preParms:bracketedBinder* $postParms* $extraParms* : $type := $proof)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
      hasAdjDiff $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
      hasAdjDiff $extraParms:bracketedBinder* := by unfold $funId; simp; infer_instance; done)
