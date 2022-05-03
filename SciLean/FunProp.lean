import Lean.Parser
import SciLean.Basic
import SciLean.AutoImpl

open Lean.Parser Lean Syntax

def Lean.Name.decapitalize : Name → Name
  | Name.str p s _ => Name.mkStr p s.decapitalize
  | n              => n

namespace SciLean.FunProp

def separateExplicitBinders (binders : Array Syntax) : (Array Syntax) := Id.run do
  let mut binders' : Array Syntax := #[]
  for (b : Syntax) in binders do
    if b.getKind != ``Lean.Parser.Term.explicitBinder then
      binders' := binders'.push b
    else
      for arg in b[1].getArgs do
        binders' := binders'.push $
          mkNode ``Lean.Parser.Term.explicitBinder #[b[0], mkNullNode #[arg], b[2], b[3], b[4]]
  pure binders'


def splitParms (parms : Array Syntax) (name : Name) : MacroM (Array Syntax × Syntax × Array Syntax) := do
  let parms := separateExplicitBinders parms

  let mut parm : Syntax := default
  let mut preParms : Array Syntax := #[]
  let mut postParms : Array Syntax := #[]
  let mut found : Bool := false

  for p in parms do
    if found then
      postParms := postParms.push p
    else if ((p[1].getIdAt 0) != name) then 
      preParms := preParms.push p
    else
      found := true
      parm := p

  if ¬found then
    Macro.throwError s!"Function does not have parameter with the name {name}!"
  else
    pure (preParms, parm, postParms)

def getExplicitArgs (binders : Array Syntax) : (Array Syntax) := Id.run do
  let mut args : Array Syntax := #[]
  for (b : Syntax) in binders do
    if b.getKind == ``Lean.Parser.Term.explicitBinder then
      args := args.append b[1].getArgs
  pure args


declare_syntax_cat argProp (behavior := both)

syntax "argument_property" ident declId bracketedBinder* ":" term "where" argProp  : command

syntax (name := argProperty)  "classProperty" ident bracketedBinder* ":=" term : argProp

macro_rules
| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
      classProperty $P:ident $extraParms:bracketedBinder* := $proof:term) => do

  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]
  let postArgs := getExplicitArgs postParms

  let funName  := fId.getIdAt 0
  let funId    := Lean.mkIdent funName
  let declBase := funName.append $ x.getId.appendBefore "arg_"

  let instId := Lean.mkIdent $ declBase.append P.getId.decapitalize
  let lam ← `(fun $parm $postParms* => $funId $preArgs* $arg $postArgs*)
  let st ← `(instance $instId:declId $preParms:bracketedBinder* $extraParms* : $P $lam := $proof)

  pure st


syntax "isSmooth"   bracketedBinder* ":=" term : argProp
syntax "isSmooth"   bracketedBinder*           : argProp
syntax "isLin"      bracketedBinder* ":=" term : argProp
syntax "isLin"      bracketedBinder*           : argProp
syntax "hasAdjoint" bracketedBinder* ":=" term : argProp
syntax "hasAdjoint" bracketedBinder*           : argProp
syntax "isInv"      bracketedBinder* ":=" term : argProp
syntax "isInv"      bracketedBinder*           : argProp

syntax "hasAdjDiff" bracketedBinder* ":=" term : argProp
syntax "hasAdjDiff" bracketedBinder*           : argProp
syntax "hasInvDiff" bracketedBinder* ":=" term : argProp
syntax "hasInvDiff" bracketedBinder*           : argProp


macro_rules
| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
      isSmooth $extraParms:bracketedBinder* := $proof:term) => 
  `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       classProperty $(mkIdent `IsSmooth) $extraParms:bracketedBinder* := $proof:term)

| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
      isSmooth $extraParms:bracketedBinder*) => do
  `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       isSmooth $extraParms:bracketedBinder* := by (unfold $(mkIdent $ fId.getIdAt 0); infer_instance))

| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
      isLin $extraParms:bracketedBinder* := $proof:term) => 
  `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       classProperty $(mkIdent `IsLin) $extraParms:bracketedBinder* := $proof:term)

| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
      isLin $extraParms:bracketedBinder*) => do
  `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       isLin $extraParms:bracketedBinder* := by (unfold $(mkIdent $ fId.getIdAt 0); infer_instance))

macro_rules
| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
      hasAdjoint $extraParms:bracketedBinder* := $proof:term) => do
  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]
  let postArgs := getExplicitArgs postParms

  let funName  := fId.getIdAt 0
  let funId    := Lean.mkIdent funName
  let declBase := funName.append $ x.getId.appendBefore "arg_"

  let instId := Lean.mkIdent $ declBase.append "hasAdjoint"
  let lam ← `(fun $parm => $funId $preArgs* $arg $postArgs*)
  `(instance $instId:declId $preParms:bracketedBinder* $postParms:bracketedBinder* $extraParms* : HasAdjoint $lam := $proof)

| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
      hasAdjoint $extraParms:bracketedBinder*) => do
  `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       hasAdjoint $extraParms:bracketedBinder* := by (unfold $(mkIdent $ fId.getIdAt 0); infer_instance))


syntax (name := argPropHasAdjDiff) "hasAdjDiff" bracketedBinder* ":=" term : argProp
syntax (name := argPropHasAdjDiffAuto) "hasAdjDiff" bracketedBinder* : argProp

macro_rules
| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
      hasAdjDiff $extraParms:bracketedBinder* := $proof:term) => do

  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]
  let postArgs := getExplicitArgs postParms

  let darg  := Lean.mkIdent $ arg.getId.appendBefore "d"
  let dparm := mkNode ``Lean.Parser.Term.explicitBinder #[parm[0], mkNullNode #[darg], parm[2], parm[3], parm[4]]

  let funName  := fId.getIdAt 0
  let funId    := Lean.mkIdent funName
  let declBase := funName.append $ x.getId.appendBefore "arg_"

  let instId := Lean.mkIdent $ declBase.append "hasAdjDiff"
  let lam ← `(fun $dparm => δ (fun $parm => $funId $preArgs* $arg) $arg $darg $postArgs*)
  `(instance $instId:declId $preParms:bracketedBinder* $parm $postParms:bracketedBinder* $extraParms* : HasAdjoint $lam := $proof)

| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
      hasAdjDiff $extraParms:bracketedBinder*) => do
  `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       hasAdjDiff $extraParms:bracketedBinder* := by (unfold $(mkIdent $ fId.getIdAt 0); simp; infer_instance))

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

  let funName  := id.getIdAt 0
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
--   most of the time we do not want that. So `diff_no_def` just defines the simp
--   theorem with the above equality where rhs is not hidden behind comp.arg_x.diff
-- syntax "diff'" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "diff_no_def" bracketedBinder* ":=" term "by" tacticSeq : argProp
syntax "diff_no_def" bracketedBinder* "by" convSeq : argProp
syntax "diff_no_def" bracketedBinder* : argProp


macro_rules
| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       diff $extraParms:bracketedBinder* := $df:term by $proof:tacticSeq) => do

  generateDifferentialCommands x fId retType parms extraParms (.explicit df proof)

| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       diff $extraParms:bracketedBinder* by $rewrite:convSeq) => do

  generateDifferentialCommands x fId retType parms extraParms (.rewrite rewrite)  

| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       diff $extraParms:bracketedBinder*) => do

  let funId := Lean.mkIdent $ fId.getIdAt 0
  `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       diff $extraParms:bracketedBinder* by unfold $funId; simp)

| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       diff_no_def $extraParms:bracketedBinder* := $df:term by $proof:tacticSeq) => do

  generateDifferentialCommands x fId retType parms extraParms (.explicit df proof) (makeDef := false)

| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       diff_no_def $extraParms:bracketedBinder* by $rw:convSeq) => do

  generateDifferentialCommands x fId retType parms extraParms (.rewrite rw) (makeDef := false)

| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       diff_no_def $extraParms:bracketedBinder*) => do

  let funId := Lean.mkIdent $ fId.getIdAt 0
  `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       diff_no_def $extraParms:bracketedBinder* by unfold $funId; simp)



syntax argProps := "argument" ident argProp,+
syntax "function_properties" declId bracketedBinder* ":" term argProps+ : command

macro "def" id:declId parms:bracketedBinder* ":" retType:term ":=" body:term props:argProps+ : command =>
  `(def $id:declId $parms:bracketedBinder* : $retType := $body
    function_properties $id:declId $parms:bracketedBinder* : $retType $props:argProps*)


-- This seems overly complicated
macro_rules 
| `(function_properties $id:declId $parms:bracketedBinder* : $retType 
    argument $x:ident $prop:argProp) =>   
    `(argument_property $x:ident $id:declId $parms:bracketedBinder* : $retType where $prop)

| `(function_properties $id:declId $parms:bracketedBinder* : $retType 
    argument $x:ident $props:argProp,* , $prop:argProp) => do
    `(function_properties $id:declId $parms:bracketedBinder* : $retType 
      argument $x $props.getElems,*
      argument_property $x:ident $id:declId $parms:bracketedBinder* : $retType where $prop)

| `(function_properties $id:declId $parms:bracketedBinder* : $retType:term
    $aprops:argProps*
    argument $x $prop:argProp) => do
    `(function_properties $id:declId $parms:bracketedBinder* : $retType:term
      $aprops:argProps*
      argument_property $x:ident $id:declId $parms:bracketedBinder* : $retType where $prop)

| `(function_properties $id:declId $parms:bracketedBinder* : $retType:term
    $aprops:argProps*
    argument $x $props:argProp,* , $prop:argProp) => do
    `(function_properties $id:declId $parms:bracketedBinder* : $retType:term
      $aprops:argProps*
      argument $x:ident $props,*
      argument_property $x:ident $id:declId $parms:bracketedBinder* : $retType where $prop)


def myFun (x y z : ℝ) : ℝ := y * x * y * z
argument x
  -- Explicit proof of smoothness
  isSmooth := by unfold myFun; infer_instance,
  -- Automatic proof of linearity
  isLin,
  -- Explicit differential + proof that it is actually a diffrential
  diff     := y * dx * y * z by simp[myFun, diff] done
argument y
  -- Automatic proof of smoothness
  isSmooth, 
  -- Differential by rewriting '∀ x, δ (λ y z => myFun x y z)'
  diff by (simp[myFun])
argument z
  isSmooth,  
  -- Automatic differential
  diff

#check Eq.mp
#check Nat

-- theorem psigma_eq_inj {α} (a b : α) : (PSigma λ x => x = a) = (PSigma λ x => x = b) → a = b := 
-- by
  
example (x : ℝ) : δ (myFun x) = myFun.arg_y.diff x := 
by
  unfold myFun.arg_y.diff
  simp[myFun.arg_y.diff]
--   simp[myFun.arg_x.diff]
--   simp[Eq.mpr, myFun.arg_x.diff.proof_1, AutoImpl.finish, AutoImpl.val, Eq.mp, myFun, AutoImpl, PSigma.fst, AutoExactSolution.exact]
--   -- cases (Eq.mpr _ _); rename_i a' h
--   -- simp[AutoImpl.val, h]
--   -- rw [AutoImpl.impl_eq_spec]
--   done

-- Just having {X Y Z} breaks auto differentiation in x
def comp {X Y Z : Type} [Vec X] [Vec Y] [Vec Z] (f : Y → Z) (g : X → Y) (x : X) : Z := f (g x)
argument f
  isSmooth, isLin, diff_no_def
argument g
  isSmooth [IsSmooth f], diff_no_def [IsSmooth f]
argument x
  isSmooth [IsSmooth f] [IsSmooth g], diff_no_def [IsSmooth f] [IsSmooth g]


-- @[  simp  ]  theorem  comp.arg_x.diff_simp' {X Y Z : Type} [Vec X] [Vec Y] [Vec Z] (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g]  
--   :  (δ  (  fun (x : X)  =>  comp f g x  ))  =  (by  (conv  =>  enter[1]; (simp[comp])); apply  AutoImpl.finish  :  (AutoImpl  (δ  (  fun (x : X)  =>  comp f g x  )))  ).val  
--   := by  apply  (  AutoImpl.impl_eq_spec  _  ) 

function_properties Prod.fst {X Y} [Vec X] [Vec Y] (xy : X × Y) : X
argument xy
  isSmooth, isLin, diff

#print Prod.fst.arg_xy.diff


function_properties Prod.fst {X Y} [SemiHilbert X] [SemiHilbert Y] (xy : X × Y) : X
argument xy
  hasAdjoint, hasAdjDiff

function_properties HMul.hMul (x y : ℝ) : ℝ
argument x
  isSmooth   := by infer_instance,
  isLin      := by infer_instance,
  hasAdjoint := by infer_instance,
  hasAdjDiff := by simp; infer_instance,
  diff       := dx * y by (simp[diff] done)
argument y
  isSmooth   := by infer_instance,
  isLin      := by infer_instance,
  hasAdjoint := by infer_instance,
  hasAdjDiff := by simp; infer_instance,
  diff       := x * dy by (simp[diff] done)


function_properties HAdd.hAdd {X} [SemiHilbert X] (x y : X) : X
argument x
  isSmooth   := by infer_instance,
  -- isLin      := by infer_instance,
  -- hasAdjoint := by infer_instance,
  hasAdjDiff := by simp; infer_instance,
  diff       := dx by (simp[diff] done)
argument y
  isSmooth   := by infer_instance,
  -- isLin      := by infer_instance,
  -- hasAdjoint := by infer_instance,
  hasAdjDiff := by simp; infer_instance,
  diff       := dy by (simp[diff] done)
-- argument x y
--   isLin      := by infer_instance
--   hasAdjoint := by infer_instance

function_properties Function.const {X} [Vec X] (ι : Type) (x : X) (i : ι) : X
argument x
  isSmooth, isLin,
  diff       := dx by simp[Function.const,diff]

function_properties Function.const {X} [Vec X] (Y : Type) [Vec Y] (x : X) (y : Y) : X
argument y
  isSmooth, 
  diff       := 0 by simp[Function.const,diff]

#check @Function.const.arg_y.isSmooth
#check @Function.const.arg_y.diff
#print Function.const.arg_y.diff

function_properties Function.const {X} [SemiHilbert X] (ι : Type) [Enumtype ι] (x : X) : ι → X
argument x
  hasAdjoint, hasAdjDiff

-- #check Prod.fst.arg_xy.hasAdjoint

example {X} [Vec X] (x y : X) : HAdd.hAdd x y = x + y := by rfl

#check myFun.arg_x.isSmooth
#check myFun.arg_x.isLin
#check myFun.arg_y.isSmooth
#check myFun.arg_y.diff
#check myFun.arg_y.diff_simp

#check myFun.arg_x.diff_simp

variable (classProperty is_smooth : Nat)

#check is_smooth

