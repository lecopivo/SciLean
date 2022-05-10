import SciLean.Core.Fun.AdjDiff.Core
import SciLean.FunPropCore

namespace SciLean.FunProp

open Lean

inductive AdjDifferentialMode where
| explicit (df' proof : Syntax) : AdjDifferentialMode
| rewrite  (rw : Syntax) : AdjDifferentialMode

def generateAdjDifferentialCommands 
  (x id retType : Syntax) 
  (parms extraParms: Array Syntax) 
  (mode : AdjDifferentialMode) 
  (makeDef := true)
  : MacroM Syntax := 
do
  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]
  let postArgs := getExplicitArgs postParms
  let argType  := parm[2][1]

  let darg'  := Lean.mkIdent $ arg.getId.appendBefore "d" |>.appendAfter "'"
  let dparm' := mkNode ``Lean.Parser.Term.explicitBinder #[parm[0], mkNullNode #[darg'], mkNullNode #[parm[2][0], retType], parm[3], parm[4]]

  let funName  := id.getId
  let funId    := Lean.mkIdent funName
  let declBase := funName.append $ x.getId.appendBefore "arg_"

  let adjDiffId := Lean.mkIdent $ declBase.append "adjDiff"
  let adjDiffSimpId  := Lean.mkIdent $ declBase.append "adjDiff_simp"

  let adjDiffNonComp ← `(δ† (fun $parm => $funId:ident $preArgs* $arg $postArgs*))
  let adjDiffComp ← 
    match mode with
      | .explicit df' proof => 
        `(($df' : $argType))
      | .rewrite rw => 
       `((by 
           conv => enter[1]; $rw
           apply AutoImpl.finish
          : AutoImpl ($adjDiffNonComp $arg $darg')).val)
  let eqProof ← 
    match mode with
      | .explicit df proof => 
        `(by $proof)
      | .rewrite rw =>
        if makeDef then
          `(by unfold $adjDiffId;  conv in (AutoImpl.val _) => rw[← AutoImpl.impl_eq_spec _])
        else
          `(by conv in (AutoImpl.val _) => rw[← AutoImpl.impl_eq_spec _])

  if makeDef then
    let adjDiffDef ← `(def $adjDiffId:declId $preParms:bracketedBinder* $parm $dparm' $postParms* $extraParms* := $adjDiffComp:term)
    let adjDiffSimp ← `(@[simp] theorem $adjDiffSimpId:declId $preParms:bracketedBinder* $postParms* $extraParms* 
                                        : $adjDiffNonComp = fun $parm $dparm' => $adjDiffId $preArgs* $arg $darg' $postArgs* := $eqProof)
    pure $ mkNullNode #[adjDiffDef,adjDiffSimp]
  else
    let adjDiffSimp ← `(@[simp] theorem $adjDiffSimpId:declId $preParms:bracketedBinder* $postParms* $extraParms* 
                                        : $adjDiffNonComp = (fun $parm $dparm' => $adjDiffComp:term) := $eqProof)
    pure adjDiffSimp


open Lean.Parser.Tactic.Conv
syntax "adjDiff" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "adjDiff" bracketedBinder* "by" convSeq : argProp
syntax "adjDiff" bracketedBinder* : argProp
syntax "adjDiff?" bracketedBinder* : argProp


-- Sometime it is undesirable to generate definition `f.arg_x.adjDiff
-- This is usefull for example for adjDifferential of composition:
--
--   δ λ x => f (g x) = λ x dx => δ f (g x) (δ g x dx)
--
--   In this case `comp.arg_x.adjDiff would have to be noncomputable and
--   most of the time we do not want that. So `adjDiff_simp` just defines the simp
--   theorem with the above equality where rhs is not hidden behind comp.arg_x.adjDiff
-- syntax "adjDiff'" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "adjDiff_simp" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "adjDiff_simp" bracketedBinder* "by" convSeq : argProp
syntax "adjDiff_simp" bracketedBinder* : argProp
syntax "adjDiff_simp?" bracketedBinder* : argProp

macro_rules
| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adjDiff $extraParms:bracketedBinder* := $df:term by $proof:tacticSeq) => do

  generateAdjDifferentialCommands x funId retType parms extraParms (.explicit df proof)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adjDiff $extraParms:bracketedBinder* by $rewrite:convSeq) => do

  generateAdjDifferentialCommands x funId retType parms extraParms (.rewrite rewrite)  

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adjDiff $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident  $funId:ident $parms:bracketedBinder* : $retType:term where
       adjDiff $extraParms:bracketedBinder* by unfold $funId; simp; unfold hold; simp)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adjDiff? $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident  $funId:ident $parms:bracketedBinder* : $retType:term where
       adjDiff $extraParms:bracketedBinder* by unfold $funId; simp; unfold hold; simp; trace_state)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adjDiff_simp $extraParms:bracketedBinder* := $df:term by $proof:tacticSeq) => do

  generateAdjDifferentialCommands x funId retType parms extraParms (.explicit df proof) (makeDef := false)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adjDiff_simp $extraParms:bracketedBinder* by $rw:convSeq) => do

  generateAdjDifferentialCommands x funId retType parms extraParms (.rewrite rw) (makeDef := false)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adjDiff_simp $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adjDiff_simp $extraParms:bracketedBinder* by unfold $funId; simp; unfold hold; simp)

| `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adjDiff_simp? $extraParms:bracketedBinder*) => do

  `(argument_property $x:ident $funId:ident $parms:bracketedBinder* : $retType:term where
       adjDiff_simp $extraParms:bracketedBinder* by unfold $funId; simp; unfold hold; simp; trace_state)

