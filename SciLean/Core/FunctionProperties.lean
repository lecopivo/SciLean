import SciLean.Core.Attributes
import SciLean.Core.Defs
import SciLean.Core.Meta.FunctionProperty
import SciLean.Core.Meta.RewriteBy

import SciLean.Tactic.AutoDiff

namespace SciLean

--------------------------------------------------------------------------------
-- isSmooth
--------------------------------------------------------------------------------

theorem isLin_isSmooth {X Y} [Vec X] [Vec Y] {f : X → Y} [inst : IsLin f] : IsSmooth f := inst.isSmooth

syntax "isSmooth" bracketedBinder* (":=" term)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec isSmooth $extraAssumptions:bracketedBinder* $[:= $proof:term]?) => do

  let data ← FunctionPropertyData.parse id parms retType arg

  let instanceId := mkIdent $ data.funPropNamespace.append "isSmooth"

  let (instanceType, extraBinders) ← 
    match data.mainArgNum with 
    | 0 => Macro.throwError "Must specify at least one argument!" 
    | 1 => pure (← `(IsSmooth  $(← data.mkLambda)), (#[] : Array BracketedBinder))
    | _ => do 
      let (T, mainBinders, lambda) ← data.mkCompositionLambda
      let TBinders : Array BracketedBinder :=  #[← `(bracketedBinderF| {$T : Type _}), ← `(bracketedBinderF| [Vec $T])]
      let mainAssumptions ← mainBinders.mapM (β := BracketedBinder) (λ b => `(bracketedBinderF| [IsSmooth $b.getIdent] ))
      let instType ← `(IsSmooth $lambda)
      pure (instType, TBinders.append (mainBinders.append mainAssumptions))

  let proof ← 
    match proof with
    | none => `(term| by first | apply isLin_isSmooth | infer_instance | (unfold $id; infer_instance); done)
    | some prf =>pure  prf

  let finalCommand ←
      `(@[fun_prop] theorem $instanceId $data.contextBinders* $extraBinders* $extraAssumptions* : $instanceType := $proof)
  
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

  let (instanceType, extraBinders) ← 
    match data.mainArgNum with 
    | 0 => Macro.throwError "Must specify at least one argument!" 
    | 1 => pure (← `(IsLin  $(← data.mkLambda)), (#[] : Array BracketedBinder))
    | _ => do 
      let (T, mainBinders, lambda) ← data.mkCompositionLambda
      let TBinders : Array BracketedBinder :=  #[← `(bracketedBinderF| {$T : Type _}), ← `(bracketedBinderF| [Vec $T])]
      let mainAssumptions ← mainBinders.mapM (β := BracketedBinder) (λ b => `(bracketedBinderF| [IsLin $b.getIdent] ))
      let instType ← `(IsLin $lambda)
      pure (instType, TBinders.append (mainBinders.append mainAssumptions))

  let proof ← 
    match proof with
    | none => `(term| by first | infer_instance | (unfold $id; infer_instance); done)
    | some prf =>pure  prf

  let finalCommand ←
      `(@[fun_prop] theorem $instanceId $data.contextBinders* $extraBinders* $extraAssumptions* : $instanceType := $proof)
  
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

  let (instanceType, extraBinders) ← 
    match data.mainArgNum with 
    | 0 => Macro.throwError "Must specify at least one argument!" 
    | 1 => pure (← `(HasAdjoint  $(← data.mkLambda)), (#[] : Array BracketedBinder))
    | _ => do 
      let (T, mainBinders, lambda) ← data.mkCompositionLambda
      let TBinders : Array BracketedBinder :=  #[← `(bracketedBinderF| {$T : Type _}), ← `(bracketedBinderF| [SemiHilbert $T])]
      let mainAssumptions ← mainBinders.mapM (β := BracketedBinder) (λ b => `(bracketedBinderF| [HasAdjoint $b.getIdent] ))
      let instType ← `(HasAdjoint $lambda)
      pure (instType, TBinders.append (mainBinders.append mainAssumptions))

  let proof ← 
    match proof with
    | none => `(term| by first | infer_instance | (unfold $id; infer_instance); done)
    | some prf =>pure  prf

  let finalCommand ←
      `(@[fun_prop] theorem $instanceId $data.contextBinders* $extraBinders* $extraAssumptions* : $instanceType := $proof)
  
  return finalCommand 

--------------------------------------------------------------------------------
-- hasAdjDiff
--------------------------------------------------------------------------------

syntax "hasAdjDiff" bracketedBinder* (":=" term)? : argProp

open Lean Parser.Term in
macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $arg:argSpec 
      hasAdjDiff $extraAssumptions:bracketedBinder* $[:= $proof:term]?) => do

  let data ← FunctionPropertyData.parse id parms retType arg

  let instanceId := mkIdent $ data.funPropNamespace.append "hasAdjDiff"

  let (instanceType, extraBinders) ← 
    match data.mainArgNum with 
    | 0 => Macro.throwError "Must specify at least one argument!" 
    | 1 => pure (← `(HasAdjDiff  $(← data.mkLambda)), (#[] : Array BracketedBinder))
    | _ => do 
      let (T, mainBinders, lambda) ← data.mkCompositionLambda
      let TBinders : Array BracketedBinder :=  #[← `(bracketedBinderF| {$T : Type _}), ← `(bracketedBinderF| [SemiHilbert $T])]
      let mainAssumptions ← mainBinders.mapM (β := BracketedBinder) (λ b => `(bracketedBinderF| [HasAdjDiff $b.getIdent] ))
      let instType ← `(HasAdjDiff $lambda)
      pure (instType, TBinders.append (mainBinders.append mainAssumptions))

  let proof ← 
    match proof with
    | none => `(term| by apply HasAdjDiff.mk; infer_instance; symdiff; infer_instance; done)
    | some prf =>pure  prf

  let finalCommand ←
      `(@[fun_prop] theorem $instanceId $data.contextBinders* $extraBinders* $extraAssumptions* : $instanceType := $proof)
  
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
/-- Define differental and/or tangentMap


  Example 1, elementary function
  ```
  function_properties Real.exp (x : ℝ) : ℝ
  argument x
    abbrev ∂ := dx * x.exp by <proof>
  ```
  Using `abbrev ∂` will simplify `∂ Real.exp x dx` to `dx * x.exp`.

  Using `abbrev ∂` is usefull when we stating derivatives of elementary functions as they are usually expressible in terms of other elementary functions.

  Example 2, custom compilcated function
  ```
  def foo (x : ℝ ) : ℝ := x + x.exp
  argument x
    def ∂ by symdiff
  ```
  Using `def ∂` will simplify `∂ foo x dx` to foo.arg_x.diff` which is equal to `dx + dx * x.exp`.

  Using `def ∂` is usefull when we state derivatives of more complicated functions, as the derivative can be rather compilcated. On the other hand the derivative 


  -/
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

  let (rhs, proof, rhsTM) ← 
    match tpc with
    | `(termWithProofOrConvTactic| := $df:term by $prf:tacticSeq) =>
      let rhs ← `(λ $mainBinder $diffBinder $trailingBinders* => $df)
      let proof ← `(by $prf)
      let rhsTM ← 
        if trailingBinders.size = 0 then
          `(λ $mainBinder $diffBinder => ($funVal, $df))
        else
          `(λ $mainBinder $diffBinder => (λ $trailingBinders* => $funVal, λ  $trailingBinders* => $df))      
      pure (rhs, proof, rhsTM)

    | `(termWithProofOrConvTactic| by $c:convSeq) => 
      let rhs ← `($lhs rewrite_by $c)
      let proof ← `(by apply AutoImpl.impl_eq_spec)
      if doTanMap.isSome then
        Macro.throwError "Using conv tactic to generate tangentMap is currently unsupported!"
      let rhsTM ← `($lhs rewrite_by $c)
      pure (rhs, proof, rhsTM)

    | _ =>  Macro.throwUnsupported

  let definition_name   := mkIdent $ data.funPropNamespace.append "diff"
  let simp_theorem_name := mkIdent $ data.funPropNamespace.append "diff_simp"

  let diff_command ←   
    match doa with
    | `(defOrAbbrev| def) => 
      `(def $definition_name $data.contextBinders* := $rhs
        @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $(data.mkAppContext definition_name) := $proof)
    | `(defOrAbbrev| abbrev) =>
      `(@[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $rhs := $proof)
    | _ => Macro.throwUnsupported

  if doTanMap.isNone then
    return diff_command

  let tangentMapProof := Syntax.mkCApp ``tangentMap_auto_proof #[data.mkAppContext simp_theorem_name]

  let definition_name   := mkIdent $ data.funPropNamespace.append "tangentMap"
  let simp_theorem_name := mkIdent $ data.funPropNamespace.append "tangentMap_simp"

  let tangentMap_command : TSyntax `command ← 
    match doa with
    | `(defOrAbbrev| def) =>
      `(def $definition_name $data.contextBinders* := $rhsTM
        @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhsTM = $(data.mkAppContext definition_name) := $proof)
    | `(defOrAbbrev| abbrev) =>
      `(@[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhsTM = $rhsTM := $tangentMapProof)
    | _ => Macro.throwUnsupported

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

  match doa with
  | `(defOrAbbrev| def) =>
    `(
    def $definition_name $data.contextBinders* := $rhs
    @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $(data.mkAppContext definition_name) := $proof
    #print $definition_name
    #check $simp_theorem_name
    )
  | `(defOrAbbrev| abbrev) =>
    `(
    @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $rhs := $proof
    #check $simp_theorem_name
    )
  | _ => Macro.throwUnsupported


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

  match doa with
  | `(defOrAbbrev| def) =>
    `(
    def $definition_name $data.contextBinders* := $rhs
    @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $(data.mkAppContext definition_name) := $proof
    #print $definition_name
    #check $simp_theorem_name
    )
  | `(defOrAbbrev| abbrev) =>    
    `(
    @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $rhs := $proof
    #check $simp_theorem_name
    )
  | _ => Macro.throwUnsupported

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
  let adjBinder : TSyntax ``funBinder ← 
    match retType with 
    | .some T => `(($x' : $T))
    | .none => `(($x'))

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
    match doa with
    | `(defOrAbbrev| def) =>
      `(def $definition_name $data.contextBinders* := $rhs
        @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $(data.mkAppContext definition_name) := $proof)
    | `(defOrAbbrev| abbrev) =>      
      `(@[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $rhs := $proof)
    | _ => Macro.throwUnsupported 


  if doRevDiff.isNone then
    return adjDiff_command


  let revDiffProof := Syntax.mkCApp ``revDiff_auto_proof #[data.mkAppContext simp_theorem_name]

  let definition_name   := mkIdent $ data.funPropNamespace.append "revDiff"
  let simp_theorem_name := mkIdent $ data.funPropNamespace.append "revDiff_simp"

  let revDiff_command ← 
    match doa with
    | `(defOrAbbrev| def) => 
      `(def $definition_name $data.contextBinders* := $rhsRD
        @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhsRD = $(data.mkAppContext definition_name) := $proofRD)
    | `(defOrAbbrev| abbrev) =>      
      `(@[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhsRD = $rhsRD := $revDiffProof)
    | _ => Macro.throwUnsupported 

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

  match doa with
  | `(defOrAbbrev| def) =>
    `(
    def $definition_name $data.contextBinders* := $rhs
    @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $(data.mkAppContext definition_name) := $proof
    #print $definition_name
    #check $simp_theorem_name
    )
  | `(defOrAbbrev| abbrev) =>
    `(
    @[diff] theorem $simp_theorem_name $data.contextBinders* $extraAssumptions* : $lhs = $rhs := $proof
    #check $simp_theorem_name
    )
  | _ => Macro.throwUnsupported


-- variable [SemiHilbert X] [Hilbert X] 
