import SciLean.Core.Inv.Core
import SciLean.FunPropCore

namespace SciLean.FunProp

open Lean

inductive InverseMode where
| explicit (fT proof : Syntax) : InverseMode
| rewrite  (rw : Syntax) : InverseMode

def generateInverseCommands 
  (x id retType : Syntax) 
  (parms extraParms: Array Syntax) 
  (mode : InverseMode) 
  (makeDef := true)
  : MacroM Syntax := 
do
  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]
  let postArgs := getExplicitArgs postParms
  let argType  := parm[2][1]

  let arg'  := Lean.mkIdent $ arg.getId.appendAfter "'"
  let parm' := mkNode ``Lean.Parser.Term.explicitBinder #[parm[0], mkNullNode #[arg'], mkNullNode #[parm[2][0], retType], parm[3], parm[4]]

  let funName  := id.getId
  let funId    := Lean.mkIdent funName
  let declBase := funName.append $ x.getId.appendBefore "arg_"

  let invId := Lean.mkIdent $ declBase.append "inv"
  let invSimpId  := Lean.mkIdent $ declBase.append "inv_simp"

  let invNonComp ← `((fun $parm => $funId:ident $preArgs* $arg $postArgs*)⁻¹)
  let invComp ← 
    match mode with
      | .explicit fT proof => 
        `(($fT : $argType))
      | .rewrite rw => 
       `((by 
           conv => enter[1]; $rw
           apply AutoImpl.finish
          : AutoImpl $invNonComp).val $arg')
  let eqProof ← 
    match mode with
      | .explicit df proof => 
        `(by $proof)
      | .rewrite rw =>
        if makeDef then
          `(by unfold $invId; apply (AutoImpl.impl_eq_spec _))
        else
          `(by apply (AutoImpl.impl_eq_spec _))

  if makeDef then
    let invDef ← `(def $invId:declId $preParms:bracketedBinder* $parm' $postParms* $extraParms* := $invComp:term)
    let invSimp ← `(@[simp] theorem $invSimpId:declId $preParms:bracketedBinder* $postParms* $extraParms* 
                                   : $invNonComp = (fun $parm' => $invId $preArgs* $arg' $postArgs*) := $eqProof)
    pure $ mkNullNode #[invDef,invSimp]
  else
    let invSimp ← `(@[simp] theorem $invSimpId:declId $preParms:bracketedBinder* $postParms* $extraParms*
                                    : $invNonComp = (fun $parm' => $invComp) := $eqProof)
    pure invSimp


open Lean.Parser.Tactic.Conv
syntax "inv" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "inv" bracketedBinder* "by" convSeq : argProp
syntax "inv" bracketedBinder* : argProp

-- Sometime it is undesirable to generate definition `f.arg_x.inv
-- This is usefull for example for inverential of composition:
--
--   δ λ x => f (g x) = λ x dx => δ f (g x) (δ g x dx)
--
--   In this case `comp.arg_x.inv would have to be noncomputable and
--   most of the time we do not want that. So `inv_simp` just defines the simp
--   theorem with the above equality where rhs is not hidden behind comp.arg_x.inv
-- syntax "inv'" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "inv_simp" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "inv_simp" bracketedBinder* "by" convSeq : argProp
syntax "inv_simp" bracketedBinder* : argProp

macro_rules
| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       inv $extraParms:bracketedBinder* := $df:term by $proof:tacticSeq) => do

  generateInverseCommands x funId retType parms extraParms (.explicit df proof)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       inv $extraParms:bracketedBinder* by $rewrite:convSeq) => do

  generateInverseCommands x funId retType parms extraParms (.rewrite rewrite)  

| `(argument_property $x:ident $argParms:bracketedBinder* $funId:ident $parms:bracketedBinder* : $retType:term where
       inv $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       inv $extraParms:bracketedBinder* by unfold $funId; simp)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       inv_simp $extraParms:bracketedBinder* := $df:term by $proof:tacticSeq) => do

  generateInverseCommands x funId retType parms extraParms (.explicit df proof) (makeDef := false)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       inv_simp $extraParms:bracketedBinder* by $rw:convSeq) => do

  generateInverseCommands x funId retType parms extraParms (.rewrite rw) (makeDef := false)

| `(argument_property $x:ident  $funId:ident $parms:bracketedBinder* : $retType:term where
       inv_simp $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       inv_simp $extraParms:bracketedBinder* by unfold $funId; simp)

