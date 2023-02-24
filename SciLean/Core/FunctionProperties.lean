import SciLean.Core.Attributes
import SciLean.Core.Defs
import SciLean.Core.Meta.FunctionProperty
import SciLean.Core.Meta.RewriteBy

import SciLean.Tactic.AutoDiff

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
      `(instance (priority:=mid) $instanceId $data.contextBinders* : $instanceType := by first | infer_instance | apply IsSmoothN.mk | (unfold $id; apply IsSmoothN.mk); done)
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
      `(instance (priority:=mid) $instanceId $data.contextBinders* : $instanceType := by first | infer_instance | apply IsLinN.mk | (unfold $id; apply IsLinN.mk); done)
    | some proof =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* : $instanceType := $proof)
  
  return finalCommand 

--------------------------------------------------------------------------------

syntax "hasAdjoint" (":=" term)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec hasAdjoint $[:= $proof:term]?) => do

  let data ← FunctionPropertyData.parse id parms retType arg

  let instanceId := mkIdent $ data.funPropNamespace.append "hasAdjoint"

  let instanceType ← `(HasAdjointN $data.mainArgNumLit $(← data.mkLambda))
  let finalCommand ←
    match proof with
    | none =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* : $instanceType := by first | infer_instance | apply HasAdjointN.mk | (unfold $id; apply HasAdjointN.mk); done)
    | some proof =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* : $instanceType := $proof)
  
  return finalCommand 

--------------------------------------------------------------------------------

theorem HasAdjDiffN.mk' {X Y : Type} {Xs Y' : Type} [SemiHilbert Xs] [SemiHilbert Y']
  {n : Nat} {f : X → Y} [Prod.Uncurry n (X → Y) Xs Y'] [IsSmoothNT n f]
  : (∀ x, HasAdjointT $ ∂ (uncurryN n f) x) → HasAdjDiffN n f
  := λ h => by 
    have : HasAdjDiffNT n f := by constructor; constructor; infer_instance; apply h
    apply HasAdjDiffN.mk

syntax "hasAdjDiff" (":=" term)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec hasAdjDiff $[:= $proof:term]?) => do

  let data ← FunctionPropertyData.parse id parms retType arg

  let instanceId := mkIdent $ data.funPropNamespace.append "hasAdjDiff"

  let instanceType ← `(HasAdjDiffN $data.mainArgNumLit $(← data.mkLambda))
  let finalCommand ←
    match proof with
    | none =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* : $instanceType := by apply HasAdjDiffN.mk'; symdiff; infer_instance; done)
    | some proof =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* : $instanceType := $proof)
  
  return finalCommand 

--------------------------------------------------------------------------------

open Lean.Parser.Tactic.Conv

syntax defOrAbbrev := "def" <|> "abbrev"
syntax byConvTactic := "by" convSeq
syntax termAndProof := ":=" term "by" tacticSeq
syntax termWithProofOrConvTactic := termAndProof <|> byConvTactic

--------------------------------------------------------------------------------


syntax defOrAbbrev "∂" (mainArg)? (termWithProofOrConvTactic)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec $doa:defOrAbbrev ∂ $[$dargs:mainArg]? $tpc:termWithProofOrConvTactic) => do

  let data ← FunctionPropertyData.parse id parms retType arg 

  let lhs := Syntax.mkCApp ``differential #[← data.mkUncurryLambda]

  let mainBinder ← data.mainFunBinder

  let diffBinder ← 
    match dargs with
    | none => data.mainBinders.mapM (λ b => b.modifyIdent λ ident => mkIdent <| ident.getId.appendBefore "d") 
              >>= mkProdFunBinder
    | some _ => Macro.throwError "Specifying custom names is currently unsupported!"
  let trailingBinders ← data.trailingFunBinders

  let (rhs, proof) ← 
    match tpc with
    | `(termWithProofOrConvTactic| := $df:term by $proof:tacticSeq) =>
      let rhs ← `(λ $mainBinder $diffBinder $trailingBinders* => $df)
      let proof ← `(by $proof)
      pure (rhs, proof)

    | `(termWithProofOrConvTactic| by $c:convSeq) => 
      let rhs ← `($lhs rewrite_by $c)
      let proof ← `(by apply AutoImpl.impl_eq_spec)
      pure (rhs, proof)

    | _ =>  Macro.throwUnsupported

  let definition_name   := mkIdent $ data.funPropNamespace.append "diff"
  let simp_theorem_name := mkIdent $ data.funPropNamespace.append "diff_simp"

  if doa.raw[0].getAtomVal == "def" then
    `(
    def $definition_name $data.contextBinders* := $rhs
    @[diff] theorem $simp_theorem_name $data.contextBinders* : $lhs = $(data.mkAppContext definition_name) := $proof
    #print $definition_name
    #check $simp_theorem_name
    )
  else if doa.raw[0].getAtomVal == "abbrev" then
    `(
    @[diff] theorem $simp_theorem_name $data.contextBinders* : $lhs = $rhs := $proof
    #check $simp_theorem_name
    )
  else
    Macro.throwUnsupported


--------------------------------------------------------------------------------


syntax defOrAbbrev "†" (mainArg)? (termWithProofOrConvTactic)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec $doa:defOrAbbrev † $[$dargs:mainArg]? $tpc:termWithProofOrConvTactic) => do

  let data ← FunctionPropertyData.parse id parms retType arg 

  let lhs := Syntax.mkCApp ``adjoint #[← data.mkUncurryLambda]

  let mainBinder ← data.mainFunBinder

  let x' := mkIdent s!"{data.mainArgString}'"
  let adjBinder : TSyntax ``funBinder ← `(($x'))

  let (rhs, proof) ← 
    match tpc with
    | `(termWithProofOrConvTactic| := $ft:term by $proof:tacticSeq) =>
      let mainType ← data.mainArgType
      let rhs ← `(λ $adjBinder => (($ft) : $mainType))
      let proof ← `(by $proof)
      pure (rhs, proof)

    | `(termWithProofOrConvTactic| by $c:convSeq) => 
      let rhs ← `($lhs rewrite_by $c)
      let proof ← `(by apply AutoImpl.impl_eq_spec)
      pure (rhs, proof)

    | _ =>  Macro.throwUnsupported

  let definition_name   := mkIdent $ data.funPropNamespace.append "adjoint"
  let simp_theorem_name := mkIdent $ data.funPropNamespace.append "adjoint_simp"

  if doa.raw[0].getAtomVal == "def" then
    `(
    def $definition_name $data.contextBinders* := $rhs
    @[diff] theorem $simp_theorem_name $data.contextBinders* : $lhs = $(data.mkAppContext definition_name) := $proof
    #print $definition_name
    #check $simp_theorem_name
    )
  else if doa.raw[0].getAtomVal == "abbrev" then
    `(
    @[diff] theorem $simp_theorem_name $data.contextBinders* : $lhs = $rhs := $proof
    #check $simp_theorem_name
    )
  else
    Macro.throwUnsupported

--------------------------------------------------------------------------------


syntax defOrAbbrev "∂†" (mainArg)? (termWithProofOrConvTactic)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec $doa:defOrAbbrev ∂† $[$dargs:mainArg]? $tpc:termWithProofOrConvTactic) => do

  let data ← FunctionPropertyData.parse id parms retType arg 

  let lhs := Syntax.mkCApp ``adjointDifferential #[← data.mkUncurryLambda]

  let mainBinder ← data.mainFunBinder

  let x' := mkIdent s!"d{data.mainArgString}'"
  let adjBinder : TSyntax ``funBinder ← `(($x'))

  dbg_trace (← data.mainArgType).raw.prettyPrint

  let (rhs, proof) ← 
    match tpc with
    | `(termWithProofOrConvTactic| := $ft:term by $proof:tacticSeq) =>
      let mainType ← data.mainArgType
      let rhs ← `(λ $mainBinder $adjBinder => (($ft) : $mainType))
      let proof ← `(by $proof)
      pure (rhs, proof)

    | `(termWithProofOrConvTactic| by $c:convSeq) => 
      let rhs ← `($lhs rewrite_by $c)
      let proof ← `(by apply AutoImpl.impl_eq_spec)
      pure (rhs, proof)

    | _ =>  Macro.throwUnsupported

  let definition_name   := mkIdent $ data.funPropNamespace.append "adjDiff"
  let simp_theorem_name := mkIdent $ data.funPropNamespace.append "adjDiff_simp"

  dbg_trace lhs.raw.prettyPrint
  dbg_trace rhs.raw.prettyPrint

  if doa.raw[0].getAtomVal == "def" then
    `(
    def $definition_name $data.contextBinders* := $rhs
    @[diff] theorem $simp_theorem_name $data.contextBinders* : $lhs = $(data.mkAppContext definition_name) := $proof
    #print $definition_name
    #check $simp_theorem_name
    )
  else if doa.raw[0].getAtomVal == "abbrev" then
    `(
    @[diff] theorem $simp_theorem_name $data.contextBinders* : $lhs = $rhs := $proof
    #check $simp_theorem_name
    )
  else
    Macro.throwUnsupported


-- variable [SemiHilbert X] [Hilbert X] 
