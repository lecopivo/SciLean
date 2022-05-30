import SciLean.Core.Fun.FwdDiff.Core
import SciLean.FunPropCore

namespace SciLean.FunProp

open Lean

inductive FwdDifferentialMode where
| explicit (df proof : Syntax) : FwdDifferentialMode
| rewrite  (rw : Syntax) : FwdDifferentialMode

def generateFwdDifferentialCommands 
  (x id retType : Syntax) 
  (parms extraParms: Array Syntax) 
  (mode : FwdDifferentialMode) 
  (makeDef := true)
  : MacroM Syntax := 
do
  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]
  let postArgs := getExplicitArgs postParms

  let type  := parm[2][1]
  let darg  := Lean.mkIdent $ arg.getId.appendBefore "d"
  let dparm := mkNode ``Lean.Parser.Term.explicitBinder #[parm[0], mkNullNode #[darg], parm[2], parm[3], parm[4]]

  let funName  := id.getId
  let funId    := Lean.mkIdent funName
  let declBase := funName.append $ x.getId.appendBefore "arg_"

  let diffId := Lean.mkIdent $ declBase.append "fwdDiff"
  let diffSimpId  := Lean.mkIdent $ declBase.append "fwdDiff_simp"

  let diffNonComp ← `(fwdDiff α (fun $parm $postParms* => $funId:ident $preArgs* $arg $postArgs*))
  let diffComp ← 
    match mode with
      | .explicit df proof => 
        `(fun (($arg, $darg) : ($type) × ($type)) $postParms* => ($df : ($retType) × ($retType)))
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
    let diffSimp ← `(@[simp] theorem $diffSimpId:declId $preParms:bracketedBinder* $extraParms* {α} : $diffNonComp = $diffId $preArgs* := $eqProof)
    dbg_trace diffDef.prettyPrint
    dbg_trace diffSimp.prettyPrint
    pure $ mkNullNode #[diffDef,diffSimp]
  else
    let diffSimp ← `(@[simp] theorem $diffSimpId:declId $preParms:bracketedBinder* $extraParms* {α} : $diffNonComp = $diffComp := $eqProof)
    pure diffSimp


open Lean.Parser.Tactic.Conv
syntax "fwdDiff" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "fwdDiff" bracketedBinder* "by" convSeq : argProp
syntax "fwdDiff" bracketedBinder* : argProp
syntax "fwdDiff?" bracketedBinder* : argProp

-- Sometime it is undesirable to generate definition `f.arg_x.fwdDiff
-- This is usefull for example for fwdDifferential of composition:
--
--   δ λ x => f (g x) = λ x dx => δ f (g x) (δ g x dx)
--
--   In this case `comp.arg_x.fwdDiff would have to be noncomputable and
--   most of the time we do not want that. So `fwdDiff_simp` just defines the simp
--   theorem with the above equality where rhs is not hidden behind comp.arg_x.fwdDiff
-- syntax "fwdDiff'" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "fwdDiff_simp" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "fwdDiff_simp" bracketedBinder* "by" convSeq : argProp
syntax "fwdDiff_simp" bracketedBinder* : argProp
syntax "fwdDiff_simp?" bracketedBinder* : argProp

macro_rules
| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       fwdDiff $extraParms:bracketedBinder* := $df:term by $proof:tacticSeq) => do

  generateFwdDifferentialCommands x funId retType parms extraParms (.explicit df proof)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       fwdDiff $extraParms:bracketedBinder* by $rewrite:convSeq) => do

  generateFwdDifferentialCommands x funId retType parms extraParms (.rewrite rewrite)  

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       fwdDiff $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident  $funId:ident $parms:bracketedBinder* : $retType:term where
       fwdDiff $extraParms:bracketedBinder* by (first | rw[fwdDiff_of_linear] | (unfold $funId; simp; unfold hold; simp)))

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       fwdDiff? $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident  $funId:ident $parms:bracketedBinder* : $retType:term where
       fwdDiff $extraParms:bracketedBinder* by (first | rw[fwdDiff_of_linear] | (unfold $funId; simp; unfold hold; simp)); trace_state)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       fwdDiff_simp $extraParms:bracketedBinder* := $df:term by $proof:tacticSeq) => do

  generateFwdDifferentialCommands x funId retType parms extraParms (.explicit df proof) (makeDef := false)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       fwdDiff_simp $extraParms:bracketedBinder* by $rw:convSeq) => do

  generateFwdDifferentialCommands x funId retType parms extraParms (.rewrite rw) (makeDef := false)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       fwdDiff_simp $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       fwdDiff_simp $extraParms:bracketedBinder*  by (first | rw[fwdDiff_of_linear] | (unfold $funId; simp; unfold hold; simp)))

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       fwdDiff_simp? $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       fwdDiff_simp $extraParms:bracketedBinder* by (first | rw[fwdDiff_of_linear] | (unfold $funId; simp; unfold hold; simp));trace_state)

