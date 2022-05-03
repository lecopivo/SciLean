import SciLean.NewStyle.Diff.Core
import SciLean.FunPropCore

namespace SciLean.FunProp

open Lean

inductive DifferentialMode where
| explicit (df proof : Syntax) : DifferentialMode
| rewrite  (rw : Syntax) : DifferentialMode

def generateDifferentialCommands 
  (x id retType : Syntax) 
  (parms extraParms: Array Syntax) 
  (mode : DifferentialMode) 
  (makeDef := true)
  : MacroM Syntax := 
do
  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]
  let postArgs := getExplicitArgs postParms

  let darg  := Lean.mkIdent $ arg.getId.appendBefore "d"
  let dparm := mkNode ``Lean.Parser.Term.explicitBinder #[parm[0], mkNullNode #[darg], parm[2], parm[3], parm[4]]

  let funName  := id.getId
  let funId    := Lean.mkIdent funName
  let declBase := funName.append $ x.getId.appendBefore "arg_"

  let diffId := Lean.mkIdent $ declBase.append "diff"
  let diffSimpId  := Lean.mkIdent $ declBase.append "diff_simp"

  let diffNonComp ← `(δ (fun $parm $postParms* => $funId:ident $preArgs* $arg $postArgs*))
  let diffComp ← 
    match mode with
      | .explicit df proof => 
        `(fun $parm $dparm $postParms* => ($df : $retType))
      | .rewrite rw => 
       `((by 
           conv => enter[1]; $rw
           apply AutoImpl.finish
          : AutoImpl $diffNonComp).val)
  let eqProof ← 
    match mode with
      | .explicit df proof => 
        `(by $proof)
      | .rewrite rw =>
        if makeDef then
          `(by unfold $diffId; apply (AutoImpl.impl_eq_spec _))
        else
          `(by apply (AutoImpl.impl_eq_spec _))

  if makeDef then
    let diffDef ← `(def $diffId:declId $preParms:bracketedBinder* := $diffComp:term)
    -- TODO: replace $diffId with $diffComp when we do not generate definition
    let diffSimp ← `(@[simp] theorem $diffSimpId:declId $preParms:bracketedBinder* $extraParms* : $diffNonComp = $diffId $preArgs* := $eqProof)
    pure $ mkNullNode #[diffDef,diffSimp]
  else
    let diffSimp ← `(@[simp] theorem $diffSimpId:declId $preParms:bracketedBinder* $extraParms* : $diffNonComp = $diffComp := $eqProof)
    pure diffSimp


open Lean.Parser.Tactic.Conv
syntax "diff" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "diff" bracketedBinder* "by" convSeq : argProp
syntax "diff" bracketedBinder* : argProp

-- Sometime it is undesirable to generate definition `f.arg_x.diff
-- This is usefull for example for differential of composition:
--
--   δ λ x => f (g x) = λ x dx => δ f (g x) (δ g x dx)
--
--   In this case `comp.arg_x.diff would have to be noncomputable and
--   most of the time we do not want that. So `diff_simp` just defines the simp
--   theorem with the above equality where rhs is not hidden behind comp.arg_x.diff
-- syntax "diff'" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "diff_simp" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "diff_simp" bracketedBinder* "by" convSeq : argProp
syntax "diff_simp" bracketedBinder* : argProp

macro_rules
| `(argument_property $x:ident $argParms:bracketedBinder* $funId:ident $parms:bracketedBinder* : $retType:term where
       diff $extraParms:bracketedBinder* := $df:term by $proof:tacticSeq) => do

  generateDifferentialCommands x funId retType parms (argParms.append extraParms) (.explicit df proof)

| `(argument_property $x:ident $argParms:bracketedBinder* $funId:ident $parms:bracketedBinder* : $retType:term where
       diff $extraParms:bracketedBinder* by $rewrite:convSeq) => do

  generateDifferentialCommands x funId retType parms (argParms.append extraParms) (.rewrite rewrite)  

| `(argument_property $x:ident $argParms:bracketedBinder* $funId:ident $parms:bracketedBinder* : $retType:term where
       diff $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident $argParms:bracketedBinder* $funId:ident $parms:bracketedBinder* : $retType:term where
       diff $extraParms:bracketedBinder* by unfold $funId; simp)

| `(argument_property $x:ident $argParms:bracketedBinder* $funId:ident $parms:bracketedBinder* : $retType:term where
       diff_simp $extraParms:bracketedBinder* := $df:term by $proof:tacticSeq) => do

  generateDifferentialCommands x funId retType parms (argParms.append extraParms) (.explicit df proof) (makeDef := false)

| `(argument_property $x:ident $argParms:bracketedBinder* $funId:ident $parms:bracketedBinder* : $retType:term where
       diff_simp $extraParms:bracketedBinder* by $rw:convSeq) => do

  generateDifferentialCommands x funId retType parms (argParms.append extraParms) (.rewrite rw) (makeDef := false)

| `(argument_property $x:ident $argParms:bracketedBinder* $funId:ident $parms:bracketedBinder* : $retType:term where
       diff_simp $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident $argParms:bracketedBinder* $funId:ident $parms:bracketedBinder* : $retType:term where
       diff_simp $extraParms:bracketedBinder* by unfold $funId; simp)

