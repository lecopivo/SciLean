import SciLean.Core.Fun.Adjoint.Core
import SciLean.FunPropCore

namespace SciLean.FunProp

open Lean.TSyntax.Compat -- makes old untyped syntax code compile

open Lean

inductive AdjointMode where
| explicit (fT proof : Syntax) : AdjointMode
| rewrite  (rw : Syntax) : AdjointMode

def generateAdjointCommands 
  (x id retType : Syntax) 
  (parms extraParms: Array Syntax) 
  (mode : AdjointMode) 
  (makeDef := true)
  : MacroM Syntax := 
do
  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]!
  let postArgs := getExplicitArgs postParms
  let argType  := parm[2][1]

  let arg'  := Lean.mkIdent $ arg.getId.appendAfter "'"
  let parm' := mkNode ``Lean.Parser.Term.explicitBinder #[parm[0], mkNullNode #[arg'], mkNullNode #[parm[2][0], retType], parm[3], parm[4]]

  let funName  := id.getId
  let funId    := Lean.mkIdent funName
  let declBase := funName.append $ x.getId.appendBefore "arg_"

  let adjId := Lean.mkIdent $ declBase.append "adj"
  let adjSimpId  := Lean.mkIdent $ declBase.append "adj_simp"

  let adjNonComp ← `((fun $parm => $funId:ident $preArgs* $arg $postArgs*)†)
  let adjComp ← 
    match mode with
      | .explicit fT proof => 
        `(($fT : $argType))
      | .rewrite rw => 
       `((by 
           conv => enter[1]; $rw
           apply AutoImpl.finish
          : AutoImpl $adjNonComp).val $arg')
  let eqProof ← 
    match mode with
      | .explicit df proof => 
        `(by $proof)
      | .rewrite rw =>
        if makeDef then
          `(by unfold $adjId; apply (AutoImpl.impl_eq_spec _))
        else
          `(by apply (AutoImpl.impl_eq_spec _))

  if makeDef then
    let adjDef ← `(def $adjId:declId $preParms:bracketedBinder* $parm' $postParms* $extraParms* := $adjComp:term)
    let adjSimp ← `(@[simp ↓] theorem $adjSimpId:declId $preParms:bracketedBinder* $postParms* $extraParms* 
                                   : $adjNonComp = (fun $parm' => $adjId $preArgs* $arg' $postArgs*) := $eqProof)
    pure $ mkNullNode #[adjDef,adjSimp]
  else
    let adjSimp ← `(@[simp ↓] theorem $adjSimpId:declId $preParms:bracketedBinder* $postParms* $extraParms*
                                    : $adjNonComp = (fun $parm' => $adjComp) := $eqProof)
    pure adjSimp


open Lean.Parser.Tactic.Conv
syntax "adj" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "adj" bracketedBinder* "by" convSeq : argProp
syntax "adj" bracketedBinder* : argProp

-- Sometime it is undesirable to generate definition `f.arg_x.adj
-- This is usefull for example for adjerential of composition:
--
--   ∂ λ x => f (g x) = λ x dx => ∂ f (g x) (∂ g x dx)
--
--   In this case `comp.arg_x.adj would have to be noncomputable and
--   most of the time we do not want that. So `adj_simp` just defines the simp
--   theorem with the above equality where rhs is not hidden behind comp.arg_x.adj
-- syntax "adj'" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "adj_simp" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "adj_simp" bracketedBinder* "by" convSeq : argProp
syntax "adj_simp" bracketedBinder* : argProp

macro_rules
| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adj $extraParms:bracketedBinder* := $df:term by $proof:tacticSeq) => do

  generateAdjointCommands x funId retType parms extraParms (.explicit df proof)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adj $extraParms:bracketedBinder* by $rewrite:convSeq) => do

  generateAdjointCommands x funId retType parms extraParms (.rewrite rewrite)  

| `(argument_property $x:ident $argParms:bracketedBinder* $funId:ident $parms:bracketedBinder* : $retType:term where
       adj $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adj $extraParms:bracketedBinder* by unfold $funId; simp)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adj_simp $extraParms:bracketedBinder* := $df:term by $proof:tacticSeq) => do

  generateAdjointCommands x funId retType parms extraParms (.explicit df proof) (makeDef := false)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adj_simp $extraParms:bracketedBinder* by $rw:convSeq) => do

  generateAdjointCommands x funId retType parms extraParms (.rewrite rw) (makeDef := false)

| `(argument_property $x:ident  $funId:ident $parms:bracketedBinder* : $retType:term where
       adj_simp $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adj_simp $extraParms:bracketedBinder* by unfold $funId; simp)

