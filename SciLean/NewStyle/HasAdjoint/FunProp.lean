import SciLean.FunPropCore
import SciLean.NewStyle.HasAdjoint.Core

namespace SciLean.FunProp

syntax "hasAdjoint"   bracketedBinder* ":=" term : argProp
syntax "hasAdjoint"   bracketedBinder*           : argProp

macro_rules
| `(argument_property $x:ident $argParms:bracketedBinder* $funId:ident $parms:bracketedBinder* : $retType:term where
      hasAdjoint $extraParms:bracketedBinder* := $proof:term) => do

  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]
  let postArgs := getExplicitArgs postParms

  let funName  := funId.getId
  let declBase := funName.append $ x.getId.appendBefore "arg_"
  let instId := Lean.mkIdent $ declBase.append "hasAdjoint"

  let lam ← `(fun $parm => $funId $preArgs* $arg $postArgs*)

  `(instance $instId:ident $preParms:bracketedBinder* $postParms* $argParms* $extraParms* : SciLean.HasAdjoint $lam := $proof)

| `(argument_property $x:ident $argParms:bracketedBinder* $funId:ident $parms:bracketedBinder* : $retType:term where
      hasAdjoint $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident $argParms:bracketedBinder* $funId:ident $parms:bracketedBinder* : $retType:term where
      hasAdjoint $extraParms:bracketedBinder* := by unfold $funId; infer_instance; done)
