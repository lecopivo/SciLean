import Lean
import Qq

import Std.Data.RBMap.Alter
import SciLean.Lean.Array
import SciLean.Lean.MergeMapDeclarationExtension

open Lean Meta Elab Elab.Term Qq


namespace SciLean

-- namespace FunctionTransformation

initialize registerTraceClass `Meta.Tactic.fun_trans
initialize registerTraceClass `Meta.Tactic.fun_trans.step
initialize registerTraceClass `Meta.Tactic.fun_trans.missing_rule
initialize registerTraceClass `Meta.Tactic.fun_trans.normalize_let
initialize registerTraceClass `Meta.Tactic.fun_trans.rewrite
initialize registerTraceClass `Meta.Tactic.fun_trans.lambda_special_cases

initialize registerTraceClass `Meta.Tactic.fun_trans_rule

register_simp_attr fun_trans

initialize funTransDefAttr : TagAttribute ←
  registerTagAttribute
    `fun_trans_def
    "Attribute to tag the definition of a function transformation."
    (validate := fun _ => pure () /- TODO: Check if it is a valid definition. Get a first explicit argument and check that it has type of `α → β` and return another function. -/)

inductive FunTransRuleType where
  | id    -- T (λ x => x)
  | const -- T (λ y => x)
  | comp  -- T (λ x => f (g x))

  | swap  -- T (λ y x => f x y)    -- this should produce a expression containing only `T (λ y => f x y)`

  | eval       -- T (λ f => f x)
  | piMap      -- T (λ g a => f a (g a))
  | piMapComp  -- T (λ g a => f a (g (h a)) g)  where (g : X → Y), (f : X → Y → (X → Y) → Z)

  | prodMap   -- T (λ x => (f x, g x))

  | letBinop  -- T (λ x => let y := g x; f x y)
  | letComp   -- T (λ x => let y := g x; f y)

  -- | fst       -- T (λ xy => xy.1)
  -- | snd       -- T (λ xy => xy.2)
deriving BEq, Hashable, Repr, Ord

instance : ToString FunTransRuleType := ⟨λ x => toString (repr x)⟩

def FunTransRuleType.expectedForm (ruleType : FunTransRuleType) : String :=
  match ruleType with
  | id    => "∀ (X : Type), T (fun (x : X) => x) = ..."
  | const => "∀ (Y : Type) (x : X), T (fun (y : Y) => x) = ..."
  | comp  => "∀ (f : Y → Z) (g : X → Y), T (fun (x : X) => f (g x)) = ..."
  | swap  => "∀ (f : α → X → Y), T (fun (x : X) (a : α) => f a x) = ..."
  | eval    => "∀ (X : Type) (a : α), T (fun (f : α → X) => f a) = ..."
  | piMap => "∀ (f : α → X → Y), T (fun (g : α → X) (a : α) => f a (g a)) = ..."
  | piMapComp => "∀ (f : α → X → (β → X) → Y) (h : α → β), T (fun (g : β → X) (a : α) => f a (g (h a)) g = ..."
  | prodMap => "∀ (f : X → Y) (g : X → Z), T (fun (x : X) => (f x, g x)) = ..."
  | letBinop    => "∀ (f : X → Y → Z) (g : X → Y), T (fun (x : X) => let y := g x; f x y) = ..."
  | letComp => "∀ (f : Y → Z) (g : X → Y), T (fun (x : X) => let y := g x; f y) = ..."

  -- | fst     => "T (fun (xy : X×Y) => xy.1) = ..."
  -- | snd     => "T (fun (xy : X×Y) => xy.2) = ..."

def FunTransRuleType.all : List FunTransRuleType := [.id,.const,.comp,.swap,.eval,.piMap,.piMapComp,.prodMap,.letComp,.letBinop]

private def merge (transName : Name) (as bs : RBMap FunTransRuleType Name compare) : RBMap FunTransRuleType Name compare :=
  as.mergeBy (t₂ := bs) (λ type ruleName ruleName' =>
    if ruleName == ruleName' then
      ruleName
    else
      panic! s!"Two incopatible `{type}` rules for `{transName}`.\nKeep only one of `{ruleName}` or `{ruleName'}` and remove the other!")

abbrev FunTransRuleMap := RBMap FunTransRuleType Name compare

initialize FunTransRuleExt : MergeMapDeclarationExtension FunTransRuleMap ← mkMergeMapDeclarationExtension ⟨merge, sorry⟩

variable {m} [Monad m] [MonadEnv m]

def insertFunTransRule (transName : Name) (type : FunTransRuleType) (ruleName : Name) : m Unit := do
  let m : FunTransRuleMap := {}
  FunTransRuleExt.insert transName (m.insert type ruleName)

def findFunTransRule? (transName : Name) (type : FunTransRuleType) : m (Option Name) := do
  if let .some m ← FunTransRuleExt.find? transName then
    return m.find? type
  else
    return none

def printFunTransRules : CoreM Unit := do
  let map := FunTransRuleExt.getState (← getEnv)
  for (trans, rules) in map do
    IO.println s!"Transformation `{trans}`"
    for (type, thrm) in rules do
      IO.println s!"  rule: {type} | theorem: `{thrm}`"



/-- Assuming `eq` in the form `T f = rhs` return `(T,f)` where `T` is a function transformaion. -/
def getFunTransEq (eq : Expr) : MetaM (Name × Expr) := do
    if eq.isEq then

      let env ← getEnv
      let lhs := eq.getArg! 1

      if let .some funTransName := lhs.getAppFn.constName? then

        if ¬(funTransDefAttr.hasTag env funTransName) then
          throwError s!"Constant `{funTransName}` is not a valid function transformation. Maybe it is missing an attribute, fix by adding `attribute [fun_trans_def] {funTransName}`"

        if let .some F := lhs.getAppRevArgs[0]? then
          return (funTransName,F)

    throwError "Function transfromation rule has to be of the form `T f = g`"



/-- Is `rule` equal to (modulo implicit arguments) `∀ (X : Type), T λ (x : X) => x = ...`? -/
def isIdRule (rule : Expr) : MetaM Bool :=

  forallTelescope rule λ contextVars eq => do

    let (_, F) ← getFunTransEq eq

    lambdaTelescope F λ xs b => do

      if xs.size ≠ 1 then
        return false

      let x := xs[0]!
      let X ← inferType x

      if b != x then
        return false

      let explicitArgs ← contextVars.filterM (λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)

      if explicitArgs.size≠1 ||
         explicitArgs[0]! != X then
         throwError "Id rule expects exacly one explicit argument `{← ppExpr X}`!"

      return true

/-- Is `rule` equal to (modulo implicit arguments) `∀ (Y : Type) (x : X), T λ (y : Y) => x = ...`? -/
def isConstRule (rule : Expr) : MetaM Bool :=

  forallTelescope rule λ contextVars eq => do

    let (_, F) ← getFunTransEq eq

    lambdaTelescope F λ xs b => do

      if xs.size ≠ 1 then
        return false

      let y := xs[0]!
      let Y ← inferType y
      let x := b
      if (b.containsFVar y.fvarId!) then
        return false

      let explicitArgs ← contextVars.filterM (λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)

      if explicitArgs.size≠2 ||
         explicitArgs[0]! != Y ||
         explicitArgs[1]! != x then
         throwError "Const rule expects exacly two explicit arguments `{← ppExpr Y}` and `{← ppExpr x}`!"

      return true

/-- Is `rule` equal to (modulo implicit arguments) `∀ (f : Y → Z) (g : X → Y), T λ (x : X) => f (g x) = ...`? -/
def isCompRule (rule : Expr) : MetaM Bool :=

  forallTelescope rule λ contextVars eq => do

    let (_, F) ← getFunTransEq eq

    lambdaTelescope F λ xs b => do

      if xs.size ≠ 1 then
        return false

      let x := xs[0]!
      let X : Q(Type) ← inferType x
      let Z : Q(Type) ← inferType b
      let f := b.getAppFn
      let some ((Y : Q(Type)), _) := (← inferType f).arrow?
        | return false
      let x : Q($X) := x
      let f : Q($Y → $Z) := f
      let g : Q($X → $Y) := (b.getArg! 0).getAppFn

      try
        let b' := q($f ($g $x))

        if ¬(← isDefEq b' b) then
          return false

      catch _ =>
        return false

      let explicitArgs ← contextVars.filterM (λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)

      if explicitArgs.size≠2 ||
         explicitArgs[0]! != f ||
         explicitArgs[1]! != g then
         throwError "Comp rule expects exacly two explicit arguments `{← ppExpr f}` and `{← ppExpr g}`!"

      return true


/-- Is `rule` equal to (modulo implicit arguments) `∀ (f : X → Y → Z), T λ (y : Y) (x : X) => f x y = ...`? -/
def isSwapRule (rule : Expr) : MetaM Bool :=

  forallTelescope rule λ contextVars eq => do

    let (_, F) ← getFunTransEq eq

    lambdaTelescope F λ xs b => do

      if xs.size ≠ 2 then
        return false

      let y := xs[0]!
      let x := xs[1]!
      let X : Q(Type) ← inferType x
      let Y : Q(Type) ← inferType y
      let Z : Q(Type) ← inferType b
      let f : Q($X → $Y → $Z) := b.getAppFn
      let y : Q($Y) := y
      let x : Q($X) := x

      let b' := q($f $x $y)

      try
        if ¬(← isDefEq b' b) then
          return false
      catch _ =>
        return false

      let explicitArgs ← contextVars.filterM (λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)

      if explicitArgs.size≠1 ||
         explicitArgs[0]! != f then
         throwError "Const rule expects exacly one explicit argument `{← ppExpr f}`!"

      return true


/-- Is `rule` equal to (modulo implicit arguments) `∀ (X : Type) (a : α), T λ (f : α → X) => f a = ...`? -/
def isEvalRule (rule : Expr) : MetaM Bool :=

  forallTelescope rule λ contextVars eq => do

    let (_, F) ← getFunTransEq eq

    lambdaTelescope F λ xs b => do

      if xs.size ≠ 1 then
        return false

      let f := xs[0]!
      let some ((α : Q(Type)), (X : Q(Type))) := (← inferType f).arrow?
        | return false
      let a : Q($α) := b.getArg! 0
      let f : Q($α → $X) := f

      let b' := q($f $a)

      try
        if ¬(← isDefEq b' b) then
          return false
      catch _ =>
        return false

      let explicitArgs ← contextVars.filterM (λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)

      if explicitArgs.size≠2 ||
         explicitArgs[0]! != X ||
         explicitArgs[1]! != a then
         throwError "Comp rule expects exacly two explicit arguments `{← ppExpr X}` and `{← ppExpr a}`!"

      return true

/-- Is `rule` equal to (modulo some implicit arguments) `∀ (f : α → X → Y), T (fun (g : α → X) (a : α) => f a (g a) = ...` ?
  On success returns `f, h` -/
def isPiMapRule (rule : Expr) : MetaM Bool := do

  forallTelescope rule λ contextVars eq => do

    let (_, F) ← getFunTransEq eq

    lambdaTelescope F λ xs b => do

      if xs.size ≠ 2 then
        return false

      let g := xs[0]!
      let a := xs[1]!

      let α : Q(Type)← inferType a
      let some (_, (X : Q(Type))) := (← inferType g).arrow?
        | return false
      let Y : Q(Type) ← inferType b

      let g : Q($α → $X) := g
      let a : Q($α) := a

      let f : Q($α → $X → $Y) := b.getAppFn

      let b' := q($f $a ($g $a))

      try
        if ¬(← isDefEq b' b) then
          return false
      catch _ =>
        return false

      let explicitArgs ← contextVars.filterM (λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)

      if explicitArgs.size≠1 ||
         explicitArgs[0]! != f then
         throwError "PiMap rule expects exacly one explicit argument `{← ppExpr f}`!"

      return true


/-- Is `rule` equal to (modulo some implicit arguments) `∀ (f : α → (β → X) → X → Y) (h : α → β), T (fun (g : β → X) (a : α) => f a g (g (h a)) = ...` ?
  On success returns `f, h` -/
def isPiMapCompRule (rule : Expr) : MetaM Bool := do

  forallTelescope rule λ contextVars eq => do

    let (_, F) ← getFunTransEq eq

    lambdaTelescope F λ xs b => do

      if xs.size ≠ 2 then
        return false

      let g := xs[0]!
      let a := xs[1]!

      let α : Q(Type)← inferType a
      let βX ← inferType g
      let some ((β : Q(Type)), (X : Q(Type))) := βX.arrow?
        | return false
      let Y : Q(Type) ← inferType b

      let g : Q($β → $X) := g
      let a : Q($α) := a

      let f : Q($α → ($β → $X) → $X → $Y) := b.getAppFn
      let h : Q($α → $β) := b.getArg! 2 |>.getArg! 0 |>.getAppFn

      let b' := q($f $a $g ($g ($h $a)))

      try
        if ¬(← isDefEq b' b) then
          return false
      catch _ =>
        return false

      let explicitArgs ← contextVars.filterM (λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)

      if explicitArgs.size≠2 ||
         explicitArgs[0]! != f ||
         explicitArgs[1]! != h then
         throwError "PiMapComp rule expects exacly two explicit arguments `{← ppExpr f}` and `{← ppExpr h}`!"

      return true


/-- Is `rule` equal to (modulo implicit arguments) `∀ (f : X → Y) (g : X → X), T λ (x : X) => (f x, g x) = ...`? -/
def isProdMapRule (rule : Expr) : MetaM Bool :=

  forallTelescope rule λ contextVars eq => do

    let (_, F) ← getFunTransEq eq

    lambdaTelescope F λ xs b => do

      if xs.size ≠ 1 then
        return false

      let x := xs[0]!
      let X : Q(Type 0) ← inferType x
      let some ((Y : Q(Type 0)), (Z : Q(Type 0))) := (← inferType b).app2? ``Prod
        | return false

      let f : Q($X → $Y) := (b.getArg! 2).getAppFn
      let g : Q($X → $Z) := (b.getArg! 3).getAppFn
      let x : Q($X) := x

      let b' := q(($f $x, $g $x))

      try
        if ¬(← isDefEq b' b) then
          return false
      catch _ =>
        return false

      let explicitArgs ← contextVars.filterM (λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)

      if explicitArgs.size≠2 ||
         explicitArgs[0]! != f ||
         explicitArgs[1]! != g then
         throwError "ProdMap rule expects exacly two explicit arguments `{← ppExpr f}` and `{← ppExpr g}`!"

      return true


/-- Is `rule` equal to (modulo implicit arguments) `∀ (f : Y → Z) (g : X → Y), T λ (x : X) => let y := g x; f y = ...`? -/
def isLetCompRule (rule : Expr) : MetaM Bool :=

  forallTelescope rule λ contextVars eq => do

    let (_, F) ← getFunTransEq eq

    lambdaTelescope F λ xs b => do

      if xs.size ≠ 1 then
        return false

      let x := xs[0]!
      let X : Q(Type) ← inferType x
      let Z : Q(Type) ← inferType b
      let f := b.letBody!.getAppFn
      let some ((Y : Q(Type)), _) := (← inferType f).arrow?
        | return false
      let x : Q($X) := x
      let f : Q($Y → $Z) := f
      let g : Q($X → $Y) := b.letValue!.getAppFn

      let b' := q(let y := $g $x; $f y)

      dbg_trace s!"b: {← ppExpr b} | b': {← ppExpr b'}"

      try
        if ¬(← isDefEq b' b) then
          return false
      catch _ =>
        return false

      dbg_trace s!"b is def eq to b'"


      let explicitArgs ← contextVars.filterM (λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)

      if explicitArgs.size≠2 ||
         explicitArgs[0]! != f ||
         explicitArgs[1]! != g then
         throwError "LetComp rule expects exacly two explicit arguments `{← ppExpr f}` and `{← ppExpr g}`!"

      return true

/-- Is `rule` equal to (modulo implicit arguments) `∀ (f : Y → Z) (g : X → Y), T λ (x : X) => let y := g x; f x y = ...`? -/
def isLetBinopRule (rule : Expr) : MetaM Bool :=

  forallTelescope rule λ contextVars eq => do

    let (_, F) ← getFunTransEq eq

    lambdaTelescope F λ xs b => do

      if xs.size ≠ 1 then
        return false

      let x := xs[0]!
      let X : Q(Type) ← inferType x
      let Z : Q(Type) ← inferType b
      let g := b.letValue!.getAppFn
      let some (_, (Y : Q(Type))) := (← inferType g).arrow?
        | return false
      let x : Q($X) := x
      let f : Q($X → $Y → $Z) := b.letBody!.getAppFn
      let g : Q($X → $Y) := g

      let b' := q(let y := $g $x; $f $x y)

      try
        if ¬(← isDefEq b' b) then
          return false
      catch _ =>
        return false

      let explicitArgs ← contextVars.filterM (λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)

      if explicitArgs.size≠2 ||
         explicitArgs[0]! != f ||
         explicitArgs[1]! != g then
         throwError "LetBinop rule expects exacly two explicit arguments `{← ppExpr f}` and `{← ppExpr g}`!"

      return true

open Lean Qq Meta Elab Term in
initialize funTransRuleAttr : TagAttribute ←
  registerTagAttribute
    `fun_trans_rule
    "Attribute to tag the basic rules for a function transformation."
    (validate := fun name => do
      let env ← getEnv
      let .some info := env.find? name
        | throwError s!"Can't find a constant named `{name}`!"

      let rule := info.type

      MetaM.run' do

        let funTransName ← forallTelescope rule λ _ eq => do
          pure (← getFunTransEq eq).fst

        if ← isIdRule rule then
          insertFunTransRule funTransName .id name
          return ()

        if ← isConstRule rule then
          insertFunTransRule funTransName .const name
          return ()

        if ← isCompRule rule then
          insertFunTransRule funTransName .comp name
          return ()

        if ← isSwapRule rule then
          insertFunTransRule funTransName .swap name
          return ()

        if ← isEvalRule rule then
          insertFunTransRule funTransName .eval name
          return ()

        if ← isPiMapRule rule then
          insertFunTransRule funTransName .piMap name
          return ()

        if ← isPiMapCompRule rule then
          insertFunTransRule funTransName .piMapComp name
          return ()

        if ← isProdMapRule rule then
          insertFunTransRule funTransName .prodMap name
          return ()

        if ← isLetCompRule rule then
          insertFunTransRule funTransName .letComp name
          return ()

        if ← isLetBinopRule rule then
          insertFunTransRule funTransName .letBinop name
          return ()

        throwError s!"Unrecognised function transformation rule!\nPossible forms of a rule are:\n{FunTransRuleType.all.map (λ rule => ("  " ++ toString funTransName ++ " " ++ rule.expectedForm ++ '\n'.toString)) |> String.join}"
      )


-- Function propositions are currently solved via type class resolutio
macro "fun_prop" : attr => `(attr|instance)
macro "fun_prop_def" : attr => `(attr|class)
macro "fun_prop_rule" : attr => `(attr|instance)
