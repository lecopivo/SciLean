import SciLean.FunPropCore
import SciLean.Core.Mor.IsLin.Core

namespace SciLean.FunProp

syntax "isLin"   bracketedBinder* ":=" term : argProp
syntax "isLin"   bracketedBinder*           : argProp

macro_rules
| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
      isLin $extraParms:bracketedBinder* := $proof:term) => do

  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]
  let postArgs := getExplicitArgs postParms

  let funName  := funId.getId
  let declBase := funName.append $ x.getId.appendBefore "arg_"
  let instId := Lean.mkIdent $ declBase.append "isLin"

  let lam ← `(fun $parm $postParms* => $funId $preArgs* $arg $postArgs*)

  let st ← `(instance $instId:ident $preParms:bracketedBinder*  $extraParms* : SciLean.IsLin $lam := $proof)

  pure st

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
      isLin $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
      isLin $extraParms:bracketedBinder* := by unfold $funId; infer_instance; done)

