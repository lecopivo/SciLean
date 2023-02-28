import SciLean.Core.Attributes
import SciLean.Core.Defs
import SciLean.Core.Meta.FunctionProperty
import SciLean.Core.Meta.RewriteBy

import SciLean.Tactic.AutoDiff

namespace SciLean

--------------------------------------------------------------------------------
-- isSmooth
--------------------------------------------------------------------------------

syntax "isSmooth" bracketedBinder* (":=" term)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec isSmooth $extraAssumptions:bracketedBinder* $[:= $proof:term]?) => do

  let data ← FunctionPropertyData.parse id parms retType arg

  let instanceId := mkIdent $ data.funPropNamespace.append "isSmooth"

  let instanceType ← `(IsSmoothN $data.mainArgNumLit $(← data.mkLambda))
  let finalCommand ←
    match proof with
    | none =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* $extraAssumptions* : $instanceType := by first | infer_instance | apply IsSmoothN.mk | (unfold $id; apply IsSmoothN.mk); done)
    | some proof =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* $extraAssumptions* : $instanceType := $proof)
  
  return finalCommand 


--------------------------------------------------------------------------------
-- isLin
--------------------------------------------------------------------------------

syntax "isLin" bracketedBinder* (":=" term)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec isLin $extraAssumptions:bracketedBinder* $[:= $proof:term]?) => do

  let data ← FunctionPropertyData.parse id parms retType arg

  let instanceId := mkIdent $ data.funPropNamespace.append "isLin"

  let instanceType ← `(IsLinN $data.mainArgNumLit $(← data.mkLambda))
  let finalCommand ←
    match proof with
    | none =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* $extraAssumptions* : $instanceType := by first | infer_instance | apply IsLinN.mk | (unfold $id; apply IsLinN.mk); done)
    | some proof =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* $extraAssumptions* : $instanceType := $proof)
  
  return finalCommand 


--------------------------------------------------------------------------------
-- hasAdjoint
--------------------------------------------------------------------------------

syntax "hasAdjoint" bracketedBinder* (":=" term)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $arg:argSpec 
      hasAdjoint $extraAssumptions:bracketedBinder* $[:= $proof:term]?) => do

  let data ← FunctionPropertyData.parse id parms retType arg

  let instanceId := mkIdent $ data.funPropNamespace.append "hasAdjoint"

  let instanceType ← `(HasAdjointN $data.mainArgNumLit $(← data.mkLambda))
  let finalCommand ←
    match proof with
    | none =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* $extraAssumptions* : $instanceType := by first | infer_instance | apply HasAdjointN.mk | (unfold $id; apply HasAdjointN.mk); done)
    | some proof =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* $extraAssumptions* : $instanceType := $proof)
  
  return finalCommand 

--------------------------------------------------------------------------------
-- hasAdjDiff
--------------------------------------------------------------------------------

theorem HasAdjDiffN.mk' {X Y : Type} {Xs Y' : Type} [SemiHilbert Xs] [SemiHilbert Y']
  {n : Nat} {f : X → Y} [Prod.Uncurry n (X → Y) Xs Y'] [IsSmoothNT n f]
  : (∀ x, HasAdjointT $ ∂ (uncurryN n f) x) → HasAdjDiffN n f
  := λ h => by 
    have : HasAdjDiffNT n f := by constructor; constructor; infer_instance; apply h
    apply HasAdjDiffN.mk

syntax "hasAdjDiff" bracketedBinder* (":=" term)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $arg:argSpec 
      hasAdjDiff $extraAssumptions:bracketedBinder* $[:= $proof:term]?) => do

  let data ← FunctionPropertyData.parse id parms retType arg

  let instanceId := mkIdent $ data.funPropNamespace.append "hasAdjDiff"

  let instanceType ← `(HasAdjDiffN $data.mainArgNumLit $(← data.mkLambda))
  let finalCommand ←
    match proof with
    | none =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* $extraAssumptions* : $instanceType := by apply HasAdjDiffN.mk'; symdiff; infer_instance; done)
    | some proof =>
      `(instance (priority:=mid) $instanceId $data.contextBinders* $extraAssumptions* : $instanceType := $proof)
  
  return finalCommand 

--------------------------------------------------------------------------------

open Lean.Parser.Tactic.Conv

syntax defOrAbbrev := "def" <|> "abbrev"
syntax byConvTactic := "by" convSeq
syntax termAndProof := ":=" term "by" tacticSeq
syntax termWithProofOrConvTactic := termAndProof <|> byConvTactic

--------------------------------------------------------------------------------
-- ∂
--------------------------------------------------------------------------------

theorem tangentMap_auto_proof {X Y} [Vec X] [Vec Y] 
  {f : X → Y} {df : X → X → Y} (h : ∂ f = df)
  : 𝒯 f = λ x dx => (f x, df x dx) := by simp[tangentMap, h]; done
  
syntax maybeTangentMap := "𝒯"
syntax defOrAbbrev "∂" (maybeTangentMap)? bracketedBinder* (mainArg)? (termWithProofOrConvTactic)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $arg:argSpec 
      $doa:defOrAbbrev ∂ $[$doTanMap:maybeTangentMap]? $extraAssumptions:bracketedBinder* $[$dargs:mainArg]? $tpc:termWithProofOrConvTactic) => do

  let data ← FunctionPropertyData.parse id parms retType arg 

  let lhs   := Syntax.mkCApp ``differential #[← data.mkUncurryLambda]
  let lhsTM := Syntax.mkCApp ``tangentMap #[← data.mkUncurryLambda]

  let mainBinder ← data.mainFunBinder

  let diffBinder ← 
    match dargs with
    | none => data.mainBinders.mapM (λ b => b.modifyIdent λ ident => mkIdent <| ident.getId.appendBefore "d") 
              >>= mkProdFunBinder
    | some _ => Macro.throwError "Specifying custom names is currently unsupported!"
  let trailingBinders ← data.trailingFunBinders

  let funVal ← data.mkApp

  let (rhs, proof, rhsTM, proofTM) ← 
    match tpc with
    | `(termWithProofOrConvTactic| := $df:term by $prf:tacticSeq) =>
      let rhs ← `(λ $mainBinder $diffBinder $trailingBinders* => $df)
      let proof ← `(by $prf)
      let rhsTM ← 
        if trailingBinders.size = 0 then
          `(λ $mainBinder $diffBinder => ($funVal, $df))
        else
          `(λ $mainBinder $diffBinder => (λ $trailingBinders* => $funVal, λ  $trailingBinders* => $df))      
      let proofTM ← `(by $prf)
      pure (rhs, proof, rhsTM, proofTM)

    | `(termWithProofOrConvTactic| by $c:convSeq) => 
      let rhs ← `($lhs rewrite_by $c)
      let proof ← `(by apply AutoImpl.impl_eq_spec)
      if doTanMap.isSome then
        Macro.throwError "Using conv tactic to generate tangentMap is currently unsupported!"
      let rhsTM ← `($lhs rewrite_by $c)
      let proofTM ← `(by apply AutoImpl.impl_eq_spec)
      pure (rhs, proof, rhsTM, proofTM)

    | _ =>  Macro.throwUnsupported

  let definition_name   := mkIdent $ data.funPropNamespace.append "diff"
  let simp_theorem_name := mkIdent $ data.funPropNamespace.append "diff_simp"

  let diff_command ←   
    if doa.raw[0].getAtomVal == "def" then
    `(def $definition_name $data.contextBinders* := $rhs
      @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $(data.mkAppContext definition_name) := $proof)
  else if doa.raw[0].getAtomVal == "abbrev" then
    `(@[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $rhs := $proof)
  else
    Macro.throwUnsupported

  if doTanMap.isNone then
    return diff_command

  let tangentMapProof := Syntax.mkCApp ``tangentMap_auto_proof #[data.mkAppContext simp_theorem_name]

  let definition_name   := mkIdent $ data.funPropNamespace.append "tangentMap"
  let simp_theorem_name := mkIdent $ data.funPropNamespace.append "tangentMap_simp"

  let tangentMap_command : TSyntax `command ←   
    if doa.raw[0].getAtomVal == "def" then
      `(def $definition_name $data.contextBinders* := $rhsTM
        @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhsTM = $(data.mkAppContext definition_name) := $proof)
    else if doa.raw[0].getAtomVal == "abbrev" then
      `(@[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhsTM = $rhsTM := $tangentMapProof)
    else
      Macro.throwUnsupported

  `($diff_command:command
    $tangentMap_command:command)

--------------------------------------------------------------------------------
-- 𝒯
--------------------------------------------------------------------------------


syntax defOrAbbrev "𝒯" bracketedBinder* (mainArg)? (termWithProofOrConvTactic)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $arg:argSpec 
      $doa:defOrAbbrev 𝒯 $extraAssumptions:bracketedBinder* $[$dargs:mainArg]? $tpc:termWithProofOrConvTactic) => do

  let data ← FunctionPropertyData.parse id parms retType arg 

  let lhs := Syntax.mkCApp ``tangentMap #[← data.mkUncurryLambda]

  let mainBinder ← data.mainFunBinder

  let diffBinder ← 
    match dargs with
    | none => data.mainBinders.mapM (λ b => b.modifyIdent λ ident => mkIdent <| ident.getId.appendBefore "d") 
              >>= mkProdFunBinder
    | some _ => Macro.throwError "Specifying custom names is currently unsupported!"
  let trailingBinders ← data.trailingFunBinders

  let (rhs, proof) ← 
    match tpc with
    | `(termWithProofOrConvTactic| := $Tf:term by $proof:tacticSeq) =>
      let rhs ← 
        `(λ $mainBinder $diffBinder => $Tf)
      let proof ← `(by $proof)
      pure (rhs, proof)

    | `(termWithProofOrConvTactic| by $c:convSeq) => 
      let rhs ← `($lhs rewrite_by $c)
      let proof ← `(by apply AutoImpl.impl_eq_spec)
      pure (rhs, proof)

    | _ =>  Macro.throwUnsupported

  let definition_name   := mkIdent $ data.funPropNamespace.append "tangentMap"
  let simp_theorem_name := mkIdent $ data.funPropNamespace.append "tangentMap_simp"

  if doa.raw[0].getAtomVal == "def" then
    `(
    def $definition_name $data.contextBinders* := $rhs
    @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $(data.mkAppContext definition_name) := $proof
    #print $definition_name
    #check $simp_theorem_name
    )
  else if doa.raw[0].getAtomVal == "abbrev" then
    `(
    @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $rhs := $proof
    #check $simp_theorem_name
    )
  else
    Macro.throwUnsupported


--------------------------------------------------------------------------------
-- †
--------------------------------------------------------------------------------

syntax defOrAbbrev "†" bracketedBinder* (mainArg)? (termWithProofOrConvTactic)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $arg:argSpec 
      $doa:defOrAbbrev † $extraAssumptions:bracketedBinder* $[$dargs:mainArg]? $tpc:termWithProofOrConvTactic) => do

  let data ← FunctionPropertyData.parse id parms retType arg 

  let lhs := Syntax.mkCApp ``adjoint #[← data.mkUncurryLambda]

  let mainBinder ← data.mainFunBinder

  let x' := mkIdent s!"{data.mainArgString}'"
  let adjBinder : TSyntax ``funBinder ← `(($x'))

  let (rhs, proof) ← 
    match tpc with
    | `(termWithProofOrConvTactic| := $ft:term by $prf:tacticSeq) =>
      let mainType ← data.mainArgType
      let rhs ← `(λ $adjBinder => (($ft) : $mainType))
      let proof ← `(by $prf)

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
    @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $(data.mkAppContext definition_name) := $proof
    #print $definition_name
    #check $simp_theorem_name
    )
  else if doa.raw[0].getAtomVal == "abbrev" then
    `(
    @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $rhs := $proof
    #check $simp_theorem_name
    )
  else
    Macro.throwUnsupported

--------------------------------------------------------------------------------

theorem revDiff_auto_proof {X Y} [SemiHilbert X] [SemiHilbert Y] 
  {f : X → Y} {df' : X → Y → X} (h : ∂† f = df')
  : ℛ f = λ x => (f x, λ dy => df' x dy) := by simp[reverseDifferential, h]; done


syntax maybeRevDiff := "ℛ"
syntax defOrAbbrev "∂†" (maybeRevDiff)? bracketedBinder* (mainArg)? (termWithProofOrConvTactic)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $arg:argSpec 
      $doa:defOrAbbrev ∂† $[$doRevDiff:maybeRevDiff]? $extraAssumptions:bracketedBinder* $[$dargs:mainArg]? $tpc:termWithProofOrConvTactic) => do

  let data ← FunctionPropertyData.parse id parms retType arg 

  let lhs := Syntax.mkCApp ``adjointDifferential #[← data.mkUncurryLambda]
  let lhsRD := Syntax.mkCApp ``reverseDifferential #[← data.mkUncurryLambda]

  let mainBinder ← data.mainFunBinder

  let x' := mkIdent s!"d{data.mainArgString}'"
  let adjBinder : TSyntax ``funBinder ← `(($x'))

  let funVal ← data.mkApp

  dbg_trace (← data.mainArgType).raw.prettyPrint

  let (rhs, proof, rhsRD, proofRD) ← 
    match tpc with
    | `(termWithProofOrConvTactic| := $ft:term by $prf:tacticSeq) =>
      let mainType ← data.mainArgType
      let rhs ← `(λ $mainBinder $adjBinder => (($ft) : $mainType))
      let proof ← `(by $prf)

      let rhsRD ← `(λ $mainBinder => ($funVal, λ $adjBinder => (($ft) : $mainType)))
      let proofRD ← `(by $prf)

      pure (rhs, proof, rhsRD, proofRD)

    | `(termWithProofOrConvTactic| by $c:convSeq) => 
      let rhs ← `($lhs rewrite_by $c)
      let proof ← `(by apply AutoImpl.impl_eq_spec)

      if doRevDiff.isSome then
        Macro.throwError "Using conv tactic to generate reverse differential is currently unsupported!"
      let rhsRD ← `($lhs rewrite_by $c)
      let proofRD ← `(by apply AutoImpl.impl_eq_spec)

      pure (rhs, proof, rhsRD, proofRD)

    | _ =>  Macro.throwUnsupported

  let definition_name   := mkIdent $ data.funPropNamespace.append "adjDiff"
  let simp_theorem_name := mkIdent $ data.funPropNamespace.append "adjDiff_simp"

  let adjDiff_command ← 
    if doa.raw[0].getAtomVal == "def" then
      `(def $definition_name $data.contextBinders* := $rhs
        @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $(data.mkAppContext definition_name) := $proof)
    else if doa.raw[0].getAtomVal == "abbrev" then
      `(@[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $rhs := $proof)
    else
      Macro.throwUnsupported


  if doRevDiff.isNone then
    return adjDiff_command


  let revDiffProof := Syntax.mkCApp ``revDiff_auto_proof #[data.mkAppContext simp_theorem_name]

  let definition_name   := mkIdent $ data.funPropNamespace.append "revDiff"
  let simp_theorem_name := mkIdent $ data.funPropNamespace.append "revDiff_simp"

  let revDiff_command ← 
    if doa.raw[0].getAtomVal == "def" then
      `(def $definition_name $data.contextBinders* := $rhsRD
        @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhsRD = $(data.mkAppContext definition_name) := $proofRD)
    else if doa.raw[0].getAtomVal == "abbrev" then
      `(@[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhsRD = $rhsRD := $revDiffProof)
    else
      Macro.throwUnsupported

  `($adjDiff_command:command
    $revDiff_command:command)
--------------------------------------------------------------------------------


syntax defOrAbbrev "ℛ" bracketedBinder* (mainArg)? (termWithProofOrConvTactic)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $arg:argSpec 
      $doa:defOrAbbrev ℛ $extraAssumptions:bracketedBinder* $[$dargs:mainArg]? $tpc:termWithProofOrConvTactic) => do

  let data ← FunctionPropertyData.parse id parms retType arg 

  let lhs := Syntax.mkCApp ``reverseDifferential #[← data.mkUncurryLambda]

  let mainBinder ← data.mainFunBinder

  dbg_trace (← data.mainArgType).raw.prettyPrint

  let (rhs, proof) ← 
    match tpc with
    | `(termWithProofOrConvTactic| := $Rf:term by $proof:tacticSeq) =>
      let mainType ← data.mainArgType
      let rhs ← `(λ $mainBinder => $Rf)
      let proof ← `(by $proof)
      pure (rhs, proof)

    | `(termWithProofOrConvTactic| by $c:convSeq) => 
      let rhs ← `($lhs rewrite_by $c)
      let proof ← `(by apply AutoImpl.impl_eq_spec)
      pure (rhs, proof)

    | _ =>  Macro.throwUnsupported

  let definition_name   := mkIdent $ data.funPropNamespace.append "revDiff"
  let simp_theorem_name := mkIdent $ data.funPropNamespace.append "revDiff_simp"

  dbg_trace lhs.raw.prettyPrint
  dbg_trace rhs.raw.prettyPrint

  if doa.raw[0].getAtomVal == "def" then
    `(
    def $definition_name $data.contextBinders* := $rhs
    @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $(data.mkAppContext definition_name) := $proof
    #print $definition_name
    #check $simp_theorem_name
    )
  else if doa.raw[0].getAtomVal == "abbrev" then
    `(
    @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $rhs := $proof
    #check $simp_theorem_name
    )
  else
    Macro.throwUnsupported



-- variable [SemiHilbert X] [Hilbert X] 
