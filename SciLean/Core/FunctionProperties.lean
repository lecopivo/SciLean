import SciLean.Core.AdjDiff
import Lean.Parser.Term
import Lean.Parser

namespace SciLean

declare_syntax_cat argSpec (behavior := both)

syntax restOfArgs := ".." ("(" ident* ")")?  -- TODO: Fix this parser such that you do not have to put the brackets there
syntax mainArg := ident <|> ("(" ident "," ident,+ ")")
syntax mainArg (restOfArgs)? : argSpec

declare_syntax_cat argProp (behavior := both)

syntax "function_property" ident bracketedBinder* (":" term)? "argument" argSpec argProp  : command
-- syntax argProps := "argument" ident bracketedBinder* argProp,+
-- syntax "function_properties" ident bracketedBinder* ":" term argProps+ : command

open Lean


def separateBinders (binders : TSyntaxArray ``Parser.Term.bracketedBinder) : TSyntaxArray ``Parser.Term.bracketedBinder := Id.run do
  let mut binders' : TSyntaxArray ``Parser.Term.bracketedBinder := .mkEmpty binders.size

  for b in binders do
    if b.raw.getKind = ``Lean.Parser.Term.instBinder then
      binders' := binders'.push b
    else
      for arg in b.raw[1].getArgs do
        let binder : TSyntax ``Parser.Term.bracketedBinder := 
          if b.raw.getKind = ``Lean.Parser.Term.explicitBinder then
            ⟨mkNode b.raw.getKind #[b.raw[0]!, mkNullNode #[arg], b.raw[2]!, b.raw[3]!, b.raw[4]!]⟩
          else
            ⟨mkNode b.raw.getKind #[b.raw[0]!, mkNullNode #[arg], b.raw[2]!, b.raw[3]!]⟩
        binders' := binders'.push binder
  pure binders'



abbrev BracketedBinder := TSyntax ``Parser.Term.bracketedBinder

def BracketedBinder.getIdent (b : BracketedBinder) : Ident :=
  b.raw[1]!.getArgs |>.getD 0 default |>.getId |> mkIdent

  -- match b with
  -- | `(Parser.Term.bracketedBinder| ($x $[: $X]?)) => x.raw.getId
  -- | `(Parser.Term.binderIdent| {$x $[: $X]?}) => x.raw.getId  
  -- | `([$x : $X]) => x.raw.getId  
  -- | _ => Name.anonymous

def BracketedBinder.getType (b : BracketedBinder) : TSyntax `term :=
  let b := b.raw
  if b.getKind = ``Lean.Parser.Term.instBinder then
    ⟨b[2]!⟩
  else
    ⟨b[2]![1]!⟩

def BracketedBinder.isExplicit (b : BracketedBinder) : Bool :=
  b.raw.getKind = ``Lean.Parser.Term.explicitBinder


  -- match b with
  -- | `(($x : $X)) => X
  -- | `({$x : $X}) => X
  -- | `([$x : $X]) => X
  -- | `([$X]) => X
  -- | _ => default

  -- if b.raw.getKind = ``Lean.Parser.Term.instBinder then
  --   ⟨b.raw[2]!⟩
  -- else
  --   ⟨b.raw[2]![1]!⟩


def BracketedBinder.toFunBinder (b : BracketedBinder) : TSyntax ``Parser.Term.funBinder :=
  if b.raw.getKind = ``Lean.Parser.Term.instBinder then
    ⟨mkNode ``Parser.Term.instBinder #[Syntax.atom default "[", Lean.mkNullNode, b.getType, Syntax.atom default "]"]⟩ 
    -- `(Parser.Term.funBinder| [$b.getType])
  else if b.raw.getKind = ``Lean.Parser.Term.implicitBinder then
    let typeAscription := (mkNode ``Parser.Term.typeAscription #[Syntax.atom default ":", b.getType])
    ⟨mkNode ``Parser.Term.paren #[Syntax.atom default "{", mkNullNode #[b.getIdent, mkNullNode #[typeAscription] ], Syntax.atom default "}"]⟩
    -- `(Parser.Term.funBinder| {$b.getIdent : $b.getType})
  else
    if b.getType.raw != Syntax.missing then
      let typeAscription := (mkNode ``Parser.Term.typeAscription #[Syntax.atom default ":", b.getType])
      ⟨mkNode ``Parser.Term.paren #[Syntax.atom default "(", mkNullNode #[b.getIdent, mkNullNode #[typeAscription] ], Syntax.atom default ")"]⟩
    else 
      ⟨mkNode ``Parser.Term.paren #[Syntax.atom default "(", mkNullNode #[b.getIdent, mkNullNode], Syntax.atom default ")"]⟩
    -- `(Parser.Term.funBinder| ($b.getIdent : $b.getType))
 
  -- match b with
  -- | `(($x)) => `(($x))
  -- | `(($x : $X)) => `(($x : $X))
  -- | `({$x:ident}) => `({$x:term})
  -- | `({$x : $X}) => `({$x : $X})
  -- | `([$X]) => `([$X])  
  -- | `([$x : $X]) => `([$x : $X])  
  -- | _ => Macro.throwError s!"Invalid bracketed binder `{b}`"



def separateExplicitBinders (binders : TSyntaxArray ``Parser.Term.bracketedBinder) : Array (Ident × Syntax) := Id.run do
  let mut binders' : Array (TSyntax `ident × Syntax) := #[]
  for (b : Syntax) in binders.raw do
    if b.getKind = ``Lean.Parser.Term.explicitBinder then
      let typeAnnotation := b[2]
      for arg in b[1].getArgs do
        binders' := binders'.push (Lean.mkIdent arg.getId, typeAnnotation)
  pure binders'


structure FunctionPropertyData where
  binders : TSyntaxArray ``Parser.Term.bracketedBinder := #[]
  fstMainArg : Nat := 0
  mainArgCount : Nat := 0
  trailingArgs : Array Nat := #[]

def FunctionPropertyData.get! (data : FunctionPropertyData) (i:Nat) : BracketedBinder := data.binders.get! i

def FunctionPropertyData.argNum (data : FunctionPropertyData) : Nat := data.binders.size


def FunctionPropertyData.argName! (data : FunctionPropertyData) (i : Nat) : Name := (data.get! i).getIdent.getId
  -- data.binders.raw[i]![1]!.getArgs |>.getD 0 default |>.getId

def FunctionPropertyData.argName (data : FunctionPropertyData) (i : Fin data.binders.size) : Name :=
  data.argName! i

def FunctionPropertyData.argType! (data : FunctionPropertyData) (i : Nat) : Syntax := (data.get! i).getType
  -- let b := data.binders.raw[i]!
  -- if b.getKind = ``Lean.Parser.Term.instBinder then
  --   b[2]!
  -- else
  --   b[2]![1]!

def FunctionPropertyData.argType (data : FunctionPropertyData) (i : Fin data.binders.size) : Syntax :=
  data.argType! i


  -- dbg_trace data.binders.raw[0]![2]![1]
  -- dbg_trace data.binders.raw[1]![2]!
  -- dbg_trace data.binders.raw[2]![2]![1]

def find? {α ι} [Enumtype ι] (p : α → Bool) (f : ι → α) : Option α := Id.run do
  for (i,_) in Enumtype.fullRange ι do
    let a := f i
    if p a then
      return some a
  return none

def findIdx? {α ι} [Enumtype ι] (p : α → Bool) (f : ι → α) : Option ι := Id.run do
  for (i,_) in Enumtype.fullRange ι do
    let a := f i
    if p a then
      return some i
  return none

def FunctionPropertyData.parseMainArg (data : FunctionPropertyData) (argSpec : TSyntax `argSpec) 
  : MacroM FunctionPropertyData :=
do
  let mut data := data

  match argSpec with
  | `(argSpec| $arg:mainArg $[$trailing]?) => 

    -- get fst main arg ident and count the number of main arguments
    let (fstIdent, otherIdents) ← 
      match arg with 
      | `(mainArg| $id:ident) => 
        data := {data with mainArgCount := 1}
        pure (id.getId, #[])
      | `(mainArg| ($id:ident, $ids:ident,*)) => 
        data := {data with mainArgCount := 1 + ids.getElems.size}
        pure (id.getId, ids.getElems.map λ i => i.getId)
      | _ => Macro.throwUnsupported


    -- check if the first main argument is valid
    let .some fstId := findIdx? (λ name => name = fstIdent) data.argName 
      | Macro.throwError s!"Main argument {fstIdent} does not exist!"
    
    data := {data with fstMainArg := fstId}
      
    -- check if too many main arguments were specified
    if fstId.1 + data.mainArgCount > data.argNum then 
        Macro.throwError s!"Too many main arguments specified! There are {data.argNum - fstId - 1} arguments after `{fstIdent}` but {data.mainArgCount-1} arguments were specified."


    -- check if other main arguments are valid and consecutive 
    for i in [1:data.mainArgCount] do
      if otherIdents[i-1]! != data.argName! (fstId+i) then
        Macro.throwError s!"Invalid main argument {otherIdents[i-1]!} expected { data.argName! (fstId+i)}."

    match trailing with 
    | none => pure () -- dbg_trace "rest not specified"
    | some trailing => 
      match trailing with
      | `(restOfArgs| ..) => 
        let s := data.fstMainArg + data.mainArgCount
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
  (argBinders : TSyntaxArray ``Parser.Term.bracketedBinder)
  (argSpec : TSyntax `argSpec)
  : MacroM FunctionPropertyData :=
do
  let mut data : FunctionPropertyData := { binders := separateBinders argBinders}

  data.parseMainArg argSpec
  

def FunctionPropertyData.contextBinders 
 (data : FunctionPropertyData) : TSyntaxArray ``Parser.Term.bracketedBinder := 
   data.binders.mapIdx 
     (λ i b => 
      if (data.fstMainArg ≤ i ∧ i < data.fstMainArg + data.mainArgCount) ||
         (data.trailingArgs.any (λ j => j = i)) then
        none
      else
        some b)
   |>.filterMap id

def FunctionPropertyData.funBinders 
 (data : FunctionPropertyData) : TSyntaxArray ``Parser.Term.funBinder := Id.run do
   let mut args : Array BracketedBinder := .mkEmpty data.mainArgCount
   for i in [data.fstMainArg : data.fstMainArg + data.mainArgCount] do
     args := args.push data.binders[i]!

   args.append (data.trailingArgs.map λ i => data.binders[i]!) |>.map λ b => b.toFunBinder

def FunctionPropertyData.mkApp
 (data : FunctionPropertyData) (function : Syntax) : TSyntax `term :=
  let explicitIdents := data.binders.filterMap (λ (b : BracketedBinder) => if b.isExplicit then some b.getIdent else none)
  ⟨mkNode ``Parser.Term.app #[function, mkNullNode explicitIdents]⟩


-- def bracketedBinder_to_funBinder (b : TSyntax ``Parser.Term.bracketedBinder) : MacroM (TSyntax ``Parser.Term.funBinder) := do
--   if b.raw.getKind = ``Lean.Parser.Term.instBinder then
--     `(Parser.Term.funBinder| [$xId : Nat])
--   else if b.raw.getKind = ``Lean.Parser.Term.implicit
--     for arg in b.raw[1].getArgs do
--       let binder : TSyntax ``Parser.Term.bracketedBinder := 
--         if b.raw.getKind = ``Lean.Parser.Term.explicitBinder then
--           ⟨mkNode b.raw.getKind #[b.raw[0]!, mkNullNode #[arg], b.raw[2]!, b.raw[3]!, b.raw[4]!]⟩
--         else
--           ⟨mkNode b.raw.getKind #[b.raw[0]!, mkNullNode #[arg], b.raw[2]!, b.raw[3]!]⟩
--       binders' := binders'.push binder
--   pure binders'


def FunctionPropertyData.funBinder
 (data : FunctionPropertyData) : TSyntax ``Parser.Term.funBinder := Id.run do
   let mut args : Array Syntax := .mkEmpty data.mainArgCount
   for i in [data.fstMainArg : data.fstMainArg + data.mainArgCount] do
     args := args.push data.binders[i]!

   mkNode ``Parser.Term.funBinder $
     (args.append (data.trailingArgs.map λ i => data.binders[i]!.raw))

syntax "isLin" : argProp -- auto
syntax "isLin" ":=" term : argProp -- auto
open Lean.Parser.Term
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec isLin := $proof:term) => do

  let data ← FunctionPropertyData.parse parms arg
  dbg_trace data.binders
  dbg_trace data.argName! 0
  dbg_trace data.argName! 1
  dbg_trace data.argName! 2
  dbg_trace data.argName! 3

  dbg_trace data.argType! 0
  dbg_trace data.argType! 1
  dbg_trace data.argType! 2
  dbg_trace data.argType! 3


  dbg_trace data.get! 0 |>.getType
  dbg_trace data.get! 1 |>.getType
  dbg_trace data.get! 2 |>.getType
  dbg_trace data.get! 3 |>.getType
  dbg_trace ( data.get! 0 |>.toFunBinder)
  dbg_trace (data.get! 1 |>.toFunBinder)
  dbg_trace (data.get! 2 |>.toFunBinder)
  dbg_trace (data.get! 3 |>.toFunBinder)

  dbg_trace data.contextBinders
  dbg_trace data.funBinders
  -- let xId := mkIdent `x
  -- let yId := mkIdent `y
  let b0 := data.get! 0 |>.toFunBinder
  let b1 := data.get! 1 |>.toFunBinder

  let b2 := data.get! 2 |>.toFunBinder
  let b3 := data.get! 3 |>.toFunBinder

  -- dbg_trace lem
  -- dbg_trace lam.raw
  -- dbg_trace lam.raw.prettyPrint

  dbg_trace data.contextBinders

  dbg_trace data.mkApp id

  `(variable $data.contextBinders*
    #check λ $data.funBinders* => $(data.mkApp id) )


function_property HAdd.hAdd {X : Type} [Vec X] (x : X) (y : X) : X
argument y ..
  isLin := sorry_proof


-- function_property HAdd.hAdd {X : Type} [Vec X] (x y : X) -- : X 
-- argument (x,y)
--   def diff ∂ := dx + dy by simp


-- function_property HAdd.hAdd {X : Type} [Vec X] (x y : X) -- : X 
-- argument (x,y)
--   def diff 𝒯


-- function_property HAdd.hAdd {X : Type} [Vec X] (x y : X) -- : X 
-- argument (x,y)
--   def diff 𝒯 (dx,dy) := (x + y, xdx + dy) by simp


