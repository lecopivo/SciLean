import SciLean.FunPropCore
import SciLean.Core.Mor.IsSmooth.Core

namespace SciLean.FunProp

open Lean.TSyntax.Compat -- makes old untyped syntax code compile

syntax "isSmooth"   bracketedBinder* ":=" term : argProp
syntax "isSmooth"   bracketedBinder*           : argProp

macro_rules
| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
      isSmooth $extraParms:bracketedBinder* := $proof:term) => do

  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]!
  let postArgs := getExplicitArgs postParms

  let funName  := funId.getId
  -- let funId    := Lean.mkIdent funName
  let declBase := funName.append $ x.getId.appendBefore "arg_"
  let instId := Lean.mkIdent $ declBase.append "isSmooth"

  let lam ← `(fun $parm $postParms* => $funId $preArgs* $arg $postArgs*)

  `(instance $instId:ident $preParms:bracketedBinder* $extraParms* : SciLean.IsSmooth $lam := $proof)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
      isSmooth $extraParms:bracketedBinder*) => do

  -- let funId    := Lean.mkIdent $ funId.getIdAt 0
  `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
      isSmooth $extraParms:bracketedBinder* := by first | (apply linear_is_smooth; done) | (unfold $funId; simp; infer_instance; done))
