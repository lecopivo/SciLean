import Lean.Parser

import SciLean.Prelude
import SciLean.Data.Prod
import SciLean.Core.Meta.BracketedBinder

namespace SciLean

open Lean Parser.Term 

syntax trailingArgs := ".." ("(" ident* ")")?  -- TODO: Fix this parser such that you do not have to put the brackets there
syntax mainArg := ident <|> ("(" ident "," ident,+ ")")
syntax argSpec := mainArg (trailingArgs)?

declare_syntax_cat argProp (behavior := both)

syntax "function_property" ident bracketedBinder* (":" term)? "argument" argSpec argProp : command

structure FunctionPropertyData where
  binders : Array BracketedBinder := #[]
  fstMainArg : Nat := 0
  mainArgNum : Nat := 0
  trailingArgs : Array Nat := #[]
  funIdent : Ident := default
  retType : Option Term := none

def FunctionPropertyData.get! (data : FunctionPropertyData) (i:Nat) : BracketedBinder := data.binders.get! i

def FunctionPropertyData.argNum (data : FunctionPropertyData) : Nat := data.binders.size

def FunctionPropertyData.argName! (data : FunctionPropertyData) (i : Nat) : Name := (data.get! i).getIdent.getId

def FunctionPropertyData.argName (data : FunctionPropertyData) (i : Fin data.binders.size) : Name :=
  data.argName! i

def FunctionPropertyData.argType! (data : FunctionPropertyData) (i : Nat) : Syntax := (data.get! i).getType

def FunctionPropertyData.argType (data : FunctionPropertyData) (i : Fin data.binders.size) : Syntax :=
  data.argType! i

def FunctionPropertyData.parseMainArg (data : FunctionPropertyData) (argSpec : TSyntax ``argSpec) 
  : MacroM FunctionPropertyData :=
do
  let mut data := data

  match argSpec with
  | `(argSpec| $arg:mainArg $[$trailing]?) => 

    -- get fst main arg ident and count the number of main arguments
    let (fstIdent, otherIdents) ← 
      match arg with 
      | `(mainArg| $id:ident) => 
        data := {data with mainArgNum := 1}
        pure (id.getId, #[])
      | `(mainArg| ($id:ident, $ids:ident,*)) => 
        data := {data with mainArgNum := 1 + ids.getElems.size}
        pure (id.getId, ids.getElems.map λ i => i.getId)
      | _ => Macro.throwUnsupported


    -- check if the first main argument is valid
    let .some fstId := findIdx? (λ name => name = fstIdent) data.argName 
      | Macro.throwError s!"Main argument {fstIdent} does not exist!"
    
    data := {data with fstMainArg := fstId}
      
    -- check if too many main arguments were specified
    if fstId.1 + data.mainArgNum > data.argNum then 
        Macro.throwError s!"Too many main arguments specified! There are {data.argNum - fstId - 1} arguments after `{fstIdent}` but {data.mainArgNum-1} arguments were specified."

    -- check if other main arguments are valid and consecutive 
    for i in [1:data.mainArgNum] do
      if otherIdents[i-1]! != data.argName! (fstId+i) then
        Macro.throwError s!"Invalid main argument {otherIdents[i-1]!} expected { data.argName! (fstId+i)}. Main arguments have to be consecutitive and in the same order as in the function definition."

    match trailing with 
    | none => pure () -- dbg_trace "rest not specified"
    | some trailing => 
      match trailing with
      | `(SciLean.trailingArgs| ..) => 
        let s := data.fstMainArg + data.mainArgNum
        let e := data.argNum
        data := {data with trailingArgs := .mkEmpty (e-s)}
        for i in [s : e] do
          data := {data with trailingArgs := data.trailingArgs.push i}
      -- | `(restOfArgs| .. ($ids:ident*)) => 
      --   for id in ids do
      --     if let .some idx := data.explicitArgs.findIdx? (λ arg => 
      | _ => Macro.throwUnsupported

  | _ => Macro.throwUnsupported

  return data


def FunctionPropertyData.parse
  (funIdent : Ident)
  (argBinders : Array BracketedBinder)
  (retType : Option Term)
  (argSpec : TSyntax ``argSpec)
  : MacroM FunctionPropertyData :=
do
  let binders ← (argBinders.foldlM (λ a b => do return a.append (← b.split)) #[])
  let mut data : FunctionPropertyData := 
    { 
      funIdent := funIdent
      binders := binders 
      retType := retType
    }

  data.parseMainArg argSpec
  

def FunctionPropertyData.contextBinders 
 (data : FunctionPropertyData) : Array BracketedBinder := 
   data.binders.mapIdx 
     (λ i b => 
      if (data.fstMainArg ≤ i ∧ i < data.fstMainArg + data.mainArgNum) ||
         (data.trailingArgs.any (λ j => j = i)) then
        none
      else
        some b)
   |>.filterMap id

def FunctionPropertyData.mainArgIdent! (data : FunctionPropertyData) (i : Nat) : Ident := 
  data.get! i |>.getIdent

def FunctionPropertyData.mainArgIds (data : FunctionPropertyData) : Array Nat :=
Id.run do
  let mut ids : Array Nat := .mkEmpty data.mainArgNum

  for i in [data.fstMainArg : data.fstMainArg + data.mainArgNum] do
    ids := ids.push i

  ids

def FunctionPropertyData.mainArgNumLit (data : FunctionPropertyData) : NumLit :=
  Syntax.mkNumLit (toString data.mainArgNum)


def FunctionPropertyData.mainBinders (data : FunctionPropertyData) : Array BracketedBinder :=
  data.mainArgIds.map (λ i => data.get! i)

def FunctionPropertyData.mainFunBinders (data : FunctionPropertyData) : MacroM (Array (TSyntax ``funBinder)) :=
  data.mainBinders.mapM (λ b => b.toFunBinder)

def FunctionPropertyData.mainArgType (data : FunctionPropertyData) : MacroM Term :=
  let binders := data.mainBinders
  if binders.size > 1 then
    binders[0:binders.size-1].foldrM (λ X Xs => `($(X.getType) × $Xs)) binders[binders.size-1]!.getType
  else
    pure binders[0]!.getType


def mkProdFunBinder (bs : Array BracketedBinder) : MacroM (TSyntax ``funBinder) :=
  if bs.size = 1 then
    bs.get! 0 |>.toFunBinder
  else if bs.size = 2 then 
    let x := bs.get! 0 |>.getIdent
    let y := bs.get! 1 |>.getIdent
    let X := bs.get! 0 |>.getType
    let Y := bs.get! 1 |>.getType
    `((($x,$y) : $X × $Y))
  else
    panic! "mkUncurriedFunBinder: More then 2 arguments are currnetly unsupported!"

/--
  Returns main argument function binder e.g. for argument specification `(x,y,z)` it returns `((x,y,z) : X×Y×Z))`
 -/
def FunctionPropertyData.mainFunBinder (data : FunctionPropertyData) : MacroM (TSyntax ``funBinder) :=
  mkProdFunBinder data.mainBinders                                       
  
def FunctionPropertyData.funBinders (data : FunctionPropertyData) 
  : MacroM (TSyntaxArray ``Parser.Term.funBinder) := 

  data.mainArgIds.append data.trailingArgs
    |>.mapM (λ id => data.get! id |>.toFunBinder)

def FunctionPropertyData.trailingBinders (data : FunctionPropertyData) : Array BracketedBinder :=
  data.trailingArgs.map (λ i => data.get! i)
def FunctionPropertyData.trailingFunBinders (data : FunctionPropertyData) : MacroM (TSyntaxArray ``funBinder) :=
  data.trailingBinders.mapM (λ b => b.toFunBinder)

def FunctionPropertyData.mkAppContext 
  (data : FunctionPropertyData) (f : Term := data.funIdent) : Term :=

  Syntax.mkApp f (data.contextBinders.filterMap λ b => 
                    if b.isExplicit then some b.getIdent else none)

def FunctionPropertyData.mkApp
  (data : FunctionPropertyData) : MacroM Term := 
do
  let explicitIdents := data.binders.filterMap 
    (λ (b : BracketedBinder) => if b.isExplicit then some b.getIdent else none)

  match data.retType with
  | some T => `(($data.funIdent $explicitIdents* : $T))
  | none => `($data.funIdent $explicitIdents*)
  -- `($data.funIdent $explicitIdents*)

def FunctionPropertyData.mkLambda
  (data : FunctionPropertyData) : MacroM Term := 
do
  `(λ $(← data.funBinders)* => $(← data.mkApp))

def FunctionPropertyData.mkUncurryLambda
  (data : FunctionPropertyData) : MacroM Term := 
do
  if data.mainArgNum > 1 then
    `(uncurryN $data.mainArgNumLit λ $(← data.funBinders)* => $(← data.mkApp))
  else
    data.mkLambda

def FunctionPropertyData.funBinder
 (data : FunctionPropertyData) : TSyntax ``Parser.Term.funBinder := Id.run do
   let mut args : Array Syntax := .mkEmpty data.mainArgNum
   for i in [data.fstMainArg : data.fstMainArg + data.mainArgNum] do
     args := args.push data.binders[i]!

   mkNode ``Parser.Term.funBinder $
     (args.append (data.trailingArgs.map λ i => data.binders[i]!.raw))

def FunctionPropertyData.mainArgString (data : FunctionPropertyData) : String := 
  data.mainArgIds.foldl (λ s id => s ++ (data.get! id |>.getIdent |>.getId |> toString)) ""

def FunctionPropertyData.trailingArgString (data : FunctionPropertyData) : String := 
  data.trailingArgs.foldl (λ s id => s ++ (data.get! id |>.getIdent |>.getId |> toString)) ""

def FunctionPropertyData.funPropNamespace (data : FunctionPropertyData) : Name :=
  let argspec := s!"arg_{data.mainArgString}" ++
    if data.trailingArgs.size > 0 
    then s!"_{data.trailingArgString}" 
    else ""

  data.funIdent.getId |>.append argspec

syntax argumentProperties := "argument" argSpec argProp,+
syntax "function_properties" ident bracketedBinder* (":" term)? argumentProperties+  : command

macro_rules
| `(function_properties $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec $argProp) => do 
  `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec $argProp)
| `(function_properties $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec $argProp , $argProps,*) => do 
  `(function_properties $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec $argProp
    function_properties $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec $argProps,*)
| `(function_properties $id:ident $parms:bracketedBinder* $[: $retType:term]? $ap:argumentProperties $aps:argumentProperties*) => do 
  `(function_properties $id:ident $parms:bracketedBinder* $[: $retType:term]? $ap
    function_properties $id:ident $parms:bracketedBinder* $[: $retType:term]? $aps:argumentProperties*)

