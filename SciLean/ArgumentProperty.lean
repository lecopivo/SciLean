import Lean.Parser
import SciLean.Basic

open Lean.Parser Lean Syntax

def Lean.Name.decapitalize : Name → Name
  | Name.str p s _ => Name.mkStr p s.decapitalize
  | n              => n

namespace SciLean

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

-- argument_property $x: $prop:argProp $props:argProp,*

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

  -- dbg_trace ""
  -- dbg_trace st.prettyPrint
  -- dbg_trace st
  -- dbg_trace ""

  pure st

syntax (name := argPropIsSmoothAuto) "isSmooth" bracketedBinder* : argProp
syntax (name := argPropIsLinAuto)    "isLin" bracketedBinder* : argProp
syntax (name := argPropHasAdjointAuto) "hasAdjoint" bracketedBinder* : argProp

syntax (name := argPropIsSmooth)   "isSmooth" bracketedBinder* ":=" term : argProp
syntax (name := argPropIsLin)      "isLin" bracketedBinder* ":=" term : argProp
syntax (name := argPropHasAdjoint) "hasAdjoint" bracketedBinder* ":=" term : argProp

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


section ClassPropertyTest

  argument_property x Math.atan2 (x y : ℝ) : ℝ where
    classProperty IsSmooth := sorry

  argument_property y Math.atan2 (x y : ℝ) : ℝ where
    classProperty IsSmooth := sorry

  #check Math.atan2.arg_x.isSmooth
  #check Math.atan2.arg_y.isSmooth

  example : IsSmooth Math.atan2 := by infer_instance
  example (x : ℝ) : IsSmooth (Math.atan2 x) := by infer_instance

end ClassPropertyTest


syntax (name := argPropDiff) "diff" bracketedBinder* ":=" term "by" tactic : argProp
syntax (name := argPropDiff') "diff'" bracketedBinder* ":=" term "by" tactic : argProp

macro_rules
| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       diff $extraParms:bracketedBinder* := $df:term by $proof:tactic) => do

  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]
  let postArgs := getExplicitArgs postParms

  let darg  := Lean.mkIdent $ arg.getId.appendBefore "d"
  let dparm := mkNode ``Lean.Parser.Term.explicitBinder #[parm[0], mkNullNode #[darg], parm[2], parm[3], parm[4]]

  let funName  := fId.getIdAt 0
  let funId    := Lean.mkIdent funName
  let declBase := funName.append $ x.getId.appendBefore "arg_"

  let defId := Lean.mkIdent $ declBase.append "diff"
  let eqId  := Lean.mkIdent $ declBase.append "diffIsValid"

  let equality ← `(SciLean.differential ($funId:ident $preArgs*) = fun $parm $dparm $postParms* => $defId:ident $preArgs* $arg $darg $postArgs*)

  let defSt ← `(def $defId:declId $preParms:bracketedBinder* $parm $dparm $postParms* : $retType:term := $df:term)
  let eqSt  ← `(@[simp] theorem $eqId:declId $preParms:bracketedBinder* $extraParms:bracketedBinder* : $equality:term := by $proof)

  pure $ mkNullNode #[defSt, eqSt]

| `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
       diff' $extraParms:bracketedBinder* := $df:term by $proof:tactic) => do

  let (preParms, parm, postParms) ← splitParms parms x.getId

  let preArgs  := getExplicitArgs preParms
  let arg      := (getExplicitArgs #[parm])[0]
  let postArgs := getExplicitArgs postParms

  let darg  := Lean.mkIdent $ arg.getId.appendBefore "d"
  let dparm := mkNode ``Lean.Parser.Term.explicitBinder #[parm[0], mkNullNode #[darg], parm[2], parm[3], parm[4]]

  let funName  := fId.getIdAt 0
  let funId    := Lean.mkIdent funName
  let declBase := funName.append $ x.getId.appendBefore "arg_"

  let eqId  := Lean.mkIdent $ declBase.append "diffSimplify"

  let equality ← `(SciLean.differential ($funId:ident $preArgs*) = fun $parm $dparm $postParms* => $df)

  `(@[simp] theorem $eqId:declId $preParms:bracketedBinder* $extraParms:bracketedBinder* : $equality:term := by $proof)



@[simp] theorem  asf : δ Math.exp = λ x dx => dx * Math.exp x := sorry

argument_property x Math.exp (x : ℝ) : ℝ where
  diff := dx * Math.exp x  by (sorry)


#check Math.exp.arg_x.diff
#check Math.exp.arg_x.diffIsValid

-- variable (is_smooth diff is_diff is proof: Nat)

-- #check is_smooth
-- #check diff
-- #check is_diff
-- #check proof

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
      argument_property $x:ident $id:declId $parms:bracketedBinder* : $retType where $prop
      )

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



-- syntax "is_smooth" ":=" term : argProp
-- syntax "is_linear" ":=" term : argProp

-- macro_rules
-- | `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
--       is_smooth := $proof:term) =>
-- `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
--       classProperty IsSmooth := $proof:term)
-- | `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
--       is_linear := $proof:term) =>
-- `(argument_property $x:ident $fId:declId $parms:bracketedBinder* : $retType:term where
--       classProperty IsLin := $proof:term)

def myFun (x y : ℝ) : ℝ := y * x * y
argument x
  isSmooth := by simp[myFun] infer_instance,
  isLin := by simp[myFun] infer_instance,
  diff := y * dx * y  by (simp[myFun, diff]) 
argument y
  isSmooth := by simp[myFun] infer_instance,
  diff := dy * x * y + y * x * dy  by (simp[myFun, diff]; done)

def comp {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : Y → Z) (g : X → Y) (x : X) : Z := f (g x)
argument f
  isSmooth, isLin,
  diff'    := df (g x) by (simp[comp])
argument g
  isSmooth [IsSmooth f],
  diff'    [IsSmooth f] := δ f (g x) (dg x) by (simp[comp] done)
argument x
  isSmooth [IsSmooth f] [IsSmooth g],
  diff'    [IsSmooth f] [IsSmooth g] := δ f (g x) (δ g x dx) by (simp[comp]; done)


function_properties Prod.fst {X Y} [Vec X] [Vec Y] (xy : X × Y) : X
argument xy
  isSmooth, isLin,
  diff := dxy.1 by simp[diff]

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
#check myFun.arg_y.diffIsValid

#check myFun.arg_x.diffIsValid

variable (classProperty is_smooth : Nat)

#check is_smooth
