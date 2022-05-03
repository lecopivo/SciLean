import Lean.Parser
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

syntax "argument_property" ident bracketedBinder* ident bracketedBinder* ":" term "where" argProp  : command
syntax argProps := "argument" ident bracketedBinder* argProp,+
syntax "function_properties" ident bracketedBinder* ":" term argProps+ : command

macro "def" id:declId parms:bracketedBinder* ":" retType:term ":=" body:term props:argProps+ : command =>
  `(def $id:declId $parms:bracketedBinder* : $retType := $body
    function_properties $id:ident $parms:bracketedBinder* : $retType $props:argProps*)


-- This seems overly complicated
macro_rules 
| `(function_properties $id:ident $parms:bracketedBinder* : $retType 
    argument $x:ident $argParms:bracketedBinder* $prop:argProp) =>   
    `(argument_property $x:ident $argParms* $id:ident $parms:bracketedBinder* : $retType where $prop)

| `(function_properties $id:ident $parms:bracketedBinder* : $retType 
    argument $x:ident $argParms:bracketedBinder* $props:argProp,* , $prop:argProp) => do
    `(function_properties $id:ident $parms:bracketedBinder* : $retType 
      argument $x $argParms* $props.getElems:argProp,*
      argument_property $x:ident $argParms* $id:ident $parms:bracketedBinder* : $retType where $prop)

| `(function_properties $id:ident $parms:bracketedBinder* : $retType:term
    $aprops:argProps*
    argument $x $argParms:bracketedBinder* $prop:argProp) => do
    `(function_properties $id:ident $parms:bracketedBinder* : $retType:term
      $aprops:argProps*
      argument_property $x:ident $argParms* $id:ident $parms:bracketedBinder* : $retType where $prop)

| `(function_properties $id:ident $parms:bracketedBinder* : $retType:term
    $aprops:argProps*
    argument $x $argParms:bracketedBinder* $props:argProp,* , $prop:argProp) => do
    `(function_properties $id:ident $parms:bracketedBinder* : $retType:term
      $aprops:argProps*
      argument $x:ident $argParms* $props.getElems:argProp,*
      argument_property $x:ident $argParms* $id:ident $parms:bracketedBinder* : $retType where $prop)


