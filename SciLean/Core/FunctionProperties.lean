import SciLean.Core.Defs
import SciLean.Core.Meta.FunctionProperty
import SciLean.Core.Meta.RewriteBy

namespace SciLean

--------------------------------------------------------------------------------

syntax "isSmooth" (":=" term)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec isSmooth $[:= $proof:term]?) => do

  let data ← FunctionPropertyData.parse id parms retType arg

  let instanceId := mkIdent $ data.funPropNamespace.append "isSmooth"

  let instanceType ← `(IsSmoothN $data.mainArgNumLit $(← data.mkLambda))
  let finalCommand ←
    match proof with
    | none =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* : $instanceType := by first | infer_instance | (unfold $id; apply IsSmoothN.mk); done)
    | some proof =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* : $instanceType := $proof)
  
  return finalCommand 


--------------------------------------------------------------------------------

syntax "isLin" (":=" term)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec isLin $[:= $proof:term]?) => do

  let data ← FunctionPropertyData.parse id parms retType arg

  let instanceId := mkIdent $ data.funPropNamespace.append "isLin"

  let instanceType ← `(IsLinN $data.mainArgNumLit $(← data.mkLambda))
  let finalCommand ←
    match proof with
    | none =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* : $instanceType := by unfold $id; apply IsLinN.mk; done)
    | some proof =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* : $instanceType := $proof)
  
  return finalCommand 

--------------------------------------------------------------------------------

syntax defOrAbbrev := "def" <|> "abbrev"
syntax termWithProofOrConvTactic := (":=" term "by" term) <|> ("by" term)

--------------------------------------------------------------------------------


syntax defOrAbbrev "∂" (mainArg)? (termWithProofOrConvTactic)? : argProp


open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec $a:defOrAbbrev ∂ $[$dargs:mainArg]? $tpc:termWithProofOrConvTactic) => do

  let data ← FunctionPropertyData.parse id parms retType arg 

  let lhs := Syntax.mkCApp ``differential #[← data.mkUncurryLambda]

  let mainBinder ← data.mainFunBinder
  let diffBinder ← 
    match dargs with
    | none => data.mainBinders.mapM (λ b => b.modifyIdent λ ident => mkIdent <| ident.getId.appendBefore "d") 
              >>= mkProdFunBinder
    | some _ => Macro.throwError "Specifying custom names is currently unsupported!"
  let trailingBinders ← data.trailingFunBinders
  let diffTerm ← 
    match tpc with
    | `(termWithProofOrConvTactic| := $df:term by $proof:term) => pure df
    | `(termWithProofOrConvTactic| by $conv:term) => default
    | _ => Macro.throwUnsupported
  let rhs ← `(λ $mainBinder $diffBinder $trailingBinders* => $diffTerm)

  dbg_trace lhs.raw.prettyPrint
  dbg_trace rhs.raw.prettyPrint

  `(
    #check $lhs
    #check $rhs
    )
  -- let data ← FunctionPropertyData.parse id parms retType arg

  -- let instanceId := mkIdent $ data.funPropNamespace.append "isLin"

  -- let instanceType ← `(IsLinN $data.mainArgNumLit $(← data.mkLambda))
  -- let finalCommand ←
  --   match proof with
  --   | none =>
  --     `(instance (priority:=mid) $instanceId $data.contextBinders* : $instanceType := by unfold $id; apply IsLinN.mk; done)
  --   | some proof =>
  --     `(instance (priority:=mid) $instanceId $data.contextBinders* : $instanceType := $proof)
  
  -- return finalCommand 

variable {X} [Vec X]

function_property Neg.neg (x : X) : X
argument x
  abbrev ∂ := dx by simp

function_property HAdd.hAdd (x y : X) : X
argument (x,y)
  abbrev ∂ := dx + dy by simp

function_property Neg.neg (x : X) : X
argument x
  abbrev ∂ by simp

