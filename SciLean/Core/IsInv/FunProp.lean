import SciLean.FunPropCore
import SciLean.Core.IsInv.Core

namespace SciLean.FunProp

syntax "isInv"   bracketedBinder* ":=" term : argProp
syntax "isInv"   bracketedBinder*           : argProp

macro_rules
| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
      isInv $extraParms:bracketedBinder* := $proof:term) => do

  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]
  let postArgs := getExplicitArgs postParms

  let funName  := funId.getId
  let declBase := funName.append $ x.getId.appendBefore "arg_"
  let instId := Lean.mkIdent $ declBase.append "isInv"

  let lam ← `(fun $parm => $funId $preArgs* $arg $postArgs*)

  `(instance $instId:ident $preParms:bracketedBinder* $postParms* $extraParms* : SciLean.IsInv $lam := $proof)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
      isInv $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
      isInv $extraParms:bracketedBinder* := by unfold $funId; infer_instance; done)
