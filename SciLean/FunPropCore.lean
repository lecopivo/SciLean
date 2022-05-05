import Lean.Parser
import Lean.Elab
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

--- Adds a binder `b as far left as possible among `binders
def addBinder (binders : Array Syntax) (b : Syntax) : Array Syntax := Id.run do
  let n := binders.size

  let mut stop := false
  for i in [0:n] do
    for p in binders[n-i-1][1].getArgs do
      match b.find? (λ q => q == p) with
      | some _ => 
        return binders.insertAt (n - i) b
      | none   =>
        continue
    
  binders.push b

def addBinders (binders : Array Syntax) (bs : Array Syntax) : Array Syntax := 
  bs.foldr (λ b binders => addBinder binders b) binders

declare_syntax_cat argProp (behavior := both)

syntax "argument_property" ident bracketedBinder* ident bracketedBinder* ":" term "where" argProp  : command
syntax argProps := "argument" ident bracketedBinder* argProp,+
syntax "function_properties" ident bracketedBinder* ":" term argProps+ : command

-- This seems overly complicated
-- TODO: incorporate `argParms into `parms before calling `argument_property
---      This way you do not have to deal with `argParms when defining cusom `argument_property
macro_rules 
| `(function_properties $id:ident $parms:bracketedBinder* : $retType 
    argument $x:ident $argParms:bracketedBinder* $prop:argProp) =>

    let allParms := addBinders parms argParms
    `(argument_property $x:ident $id:ident $allParms:bracketedBinder* : $retType where $prop)

| `(function_properties $id:ident $parms:bracketedBinder* : $retType 
    argument $x:ident $argParms:bracketedBinder* $props:argProp,* , $prop:argProp) => do

    let allParms := addBinders parms argParms
    `(function_properties $id:ident $parms:bracketedBinder* : $retType 
      argument $x $argParms* $props.getElems:argProp,*
      argument_property $x:ident $id:ident $allParms:bracketedBinder* : $retType where $prop)

| `(function_properties $id:ident $parms:bracketedBinder* : $retType:term
    $aprops:argProps*
    argument $x $argParms:bracketedBinder* $prop:argProp) => do

    let allParms := addBinders parms argParms
    `(function_properties $id:ident $parms:bracketedBinder* : $retType:term
      $aprops:argProps*
      argument_property $x:ident $id:ident $allParms:bracketedBinder* : $retType where $prop)

| `(function_properties $id:ident $parms:bracketedBinder* : $retType:term
    $aprops:argProps*
    argument $x $argParms:bracketedBinder* $props:argProp,* , $prop:argProp) => do

    let allParms := addBinders parms argParms
    `(function_properties $id:ident $parms:bracketedBinder* : $retType:term
      $aprops:argProps*
      argument $x:ident $argParms* $props.getElems:argProp,*
      argument_property $x:ident $id:ident $allParms:bracketedBinder* : $retType where $prop)


macro "def" id:declId parms:bracketedBinder* ":" retType:term ":=" body:term props:argProps+ : command => do
  let funId := mkIdent $ id.getIdAt 0
  `(def $id:declId $parms:bracketedBinder* : $retType := $body
    function_properties $funId:ident $parms:bracketedBinder* : $retType $props:argProps*)
