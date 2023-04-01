import Lean
import Qq

open Lean Meta Elab Elab.Term


namespace SciLean


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

  | forallMap -- T (λ g x => f x (g x))
  | eval      -- T (λ f => f x)

  | prodMap   -- T (λ x => (f x, g x))

  | letBinop      -- T (λ x => let y := g x; f x y)
  | letComp   -- T (λ x => let y := g x; f y)
  -- | fst       -- T (λ xy => xy.1)
  -- | snd       -- T (λ xy => xy.2)
deriving BEq, Hashable, Repr

instance : ToString FunTransRuleType := ⟨λ x => toString (repr x)⟩

def FunTransRuleType.expectedForm (ruleType : FunTransRuleType) : String :=
  match ruleType with
  | id    => "(fun (x : X) => x) = ..."
  | const => "(fun (y : Y) => x) = ..."
  | comp  => "(fun (x : X) => f (g x)) = ..."
  | swap  => "(fun (x : X) (a : α) => f a x) = ..."
  | forallMap => "(fun (g : α → X) (a : α) => f a (g a)) = ..."
  | eval    => "(fun (f : α → X) => f a) = ..."
  | prodMap => "(fun (x : X) => (f x, g x)) = ..."
  | letBinop    => "(fun (x : X) => let y := g x; f x y) = ..."
  | letComp => "(fun (x : X) => let y := g x; f y) = ..."
  -- | fst     => "T (fun (xy : X×Y) => xy.1) = ..."
  -- | snd     => "T (fun (xy : X×Y) => xy.2) = ..."

def FunTransRuleType.all : List FunTransRuleType := [.id,.const,.comp,.swap,.forallMap,.eval,.prodMap,.letBinop,.letComp]

/-- 
  Contains a map from a name of function transformation to 
  -/
initialize funTransRulesMapRef : IO.Ref (PersistentHashMap (Name×FunTransRuleType) Name) ← IO.mkRef {}

/-- Is `F` equal to `λ (x : X) => x`?
  On success returns `X` -/
def isId (F : Expr) : MetaM (Option Expr) :=
  lambdaTelescope F λ xs b => 
    if xs.size = 1 then
      let x := xs[0]!
      if x == b then
        return (← inferType x)
      else 
        return none
    else 
      return none


/-- Is `F` equal to `λ (y : Y) => x` ?
  On success returns `(Y,x)` -/
def isConst (F : Expr) : MetaM (Option (Expr×Expr)) :=
  lambdaTelescope F λ xs b => 
    if xs.size = 1 then
      let y := xs[0]!
      if ¬(b.containsFVar y.fvarId!) then
        return ((← inferType y), b)
      else 
        return none
    else 
      return none


/-- Is `F` equal to `λ (x : X) => f (g x)` ?
  On success returns `(f,g)` -/
def isComp (F : Expr) : MetaM (Option (Expr×Expr)) :=
  lambdaTelescope F λ xs b => do
    if xs.size = 1 then
      let x := xs[0]!
      let xId := x.fvarId!

      if let .app f gx := b then
        if let .app g x' := gx then
          if (x == x') && ¬(f.containsFVar xId) && ¬(g.containsFVar xId) then
            return (f,g)

      return none
    else
      return none

/-- Is `F` equal to `λ (y : Y) (x : Y) => f x y` ?
  On success returns `f` -/
def isSwap (F : Expr) : MetaM (Option Expr) :=
  lambdaTelescope F λ xs b => do
    if xs.size = 2 then
      let y := xs[0]!
      let x := xs[1]!

      if let .app fx y' := b then
        if let .app f x' := fx then
          if (x == x') && (y == y') then
            return f

      return none
    else
      return none

/-- Is `F` equal to `λ (g : α → X) (a : α) => f a (g a)` ?
  On success returns `f` -/
def isForallMap (F : Expr) : MetaM (Option Expr) :=
  lambdaTelescope F λ xs b => do
    if xs.size = 2 then
      let g := xs[0]!
      let a := xs[1]!

      if let .app fa ga := b then
        if let .app f a' := fa then
          if let .app g' a'' := ga then
            if (g == g') && (a == a') && (a == a'') then
              return f

      return none
    else
      return none

/-- Is `F` equal to `λ (f : X → Y) => f x` ?
  On success returns `(Y,x)` -/
def isEval (F : Expr) : MetaM (Option (Expr×Expr)) :=
  lambdaTelescope F λ xs b => do
    if xs.size = 1 then
      let f := xs[0]!
      let Y ← inferType b

      if let .app f' x := b then
        if (f == f') then 
          return (Y, x)

      return none
    else
      return none


/-- Is `F` equal to `λ (x : X) => (f x, g x)` ?
  On success returns `(f,g)` -/
def isProdMap (F : Expr) : MetaM (Option (Expr×Expr)) :=
  lambdaTelescope F λ xs b => do
    if xs.size = 1 then
      let x := xs[0]!

      if let .some (_, _, fx, gx) := b.app4? ``Prod.mk then
        if let .app f x' := fx then
          if let .app g x'' := gx then
            if (x == x') && (x == x'') then
              return (f,g)

      return none
    else
      return none

/-- Is `F` equal to `λ (x : X) => let y := g x; f x y` ?
  On success returns `(f,g)` -/
def isLetBinop (F : Expr) : MetaM (Option (Expr×Expr)) :=
  lambdaLetTelescope F λ xs b => do
    if xs.size = 2 then
      let x := xs[0]!
      let y := xs[1]!

      if let .some gx ← y.fvarId!.getValue? then
        if let .app g x' := gx then
          if let .app fx y' := b then
            if let .app f x'' := fx then
              if (x == x') && (x == x'') && (y == y') then
                return (f,g)

      return none
    else
      return none


/-- Is `F` equal to `λ (x : X) => let y := g x; f y` ?
  On success returns `(f,g)` -/
def isLetComp (F : Expr) : MetaM (Option (Expr×Expr)) :=
  lambdaLetTelescope F λ xs b => do
    if xs.size = 2 then
      let x := xs[0]!
      let y := xs[1]!

      if let .some gx ← y.fvarId!.getValue? then
        if let .app g x' := gx then
          if let .app f y' := b then
            if (x == x') && (y == y') then
              return (f,g)

      return none
    else
      return none

open Lean Qq Meta Elab Term in
/-- Mark function transformation rule, possible forms are:
  - id:    T (λ x => x)
  - const: T (λ y => x)
  - comp:  T (λ x => f (g x))
  - swap:  T (λ y x => f x y)
  - eval:  T (λ f => f x)
  - forallMap: T (λ g x => f x (g x))
  - prodMap:   T (λ x => (f x, g x))
  - letBinop:  T (λ x => let y := g x; f x y)
  - letComp:   T (λ x => let y := g x; f y)
  -/
initialize funTransRuleAttr : TagAttribute ← 
  registerTagAttribute 
    `fun_trans_rule
    "Attribute to tag the basic rules for a function transformation." 
    (validate := fun name => do
      let env ← getEnv 
      let .some info := env.find? name 
        | throwError s!"Can't find a constant named `{name}`!"

      MetaM.run' do
        forallTelescope info.type λ xs b => do

        if ¬(b.isAppOf ``Eq) || b.getAppNumArgs ≠ 3 then
          throwError "Function transfromation rule has to be of the form `T f = g`"
  
        let lhs := b.getAppArgs[1]!
        -- let rhs := b.getAppArgs[2]!

        let .some funTransName := lhs.getAppFn.constName?
          | throwError "Function transfromation rule has to be of the form `T f = g`"
  
        if ¬(funTransDefAttr.hasTag env funTransName) then
          throwError s!"Constant `{funTransName}` is not a valid function transformation. Maybe it is missing an attribute, fix by adding `attribute [fun_trans_def] {funTransName}`"
        
        let .some F := lhs.getAppRevArgs[0]?
          | throwError "Function transfromation rule has to be of the form `T f = g`"

          let explicitArgs ← xs.filterM (λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)

          -- TODO: convert dbg_trace to trace

          -- identity
          if let .some X ← isId F then
            dbg_trace s!"Identity rule for `{funTransName}` detected!"

            if (explicitArgs.size ≠1) then
              throwError "Identity rule is expecting exactly one explicit argument `{← ppExpr X}`!"

            if (explicitArgs[0]! == X) then
              funTransRulesMapRef.modify (λ m => m.insert (funTransName, .id) name)
              return ()
            else
              throwError "Identity rule is expecting exactly one explicit argument `{← ppExpr X}`!"

          -- constant
          if let .some (Y,x) ← isConst F then
            dbg_trace s!"Constant rule for `{funTransName}` detected!"

            if (explicitArgs.size ≠ 2) then
              throwError "Constant rule is expecting exactly two explicit arguments `{← ppExpr Y}` and `{← ppExpr x}`!"
  
            if (explicitArgs[0]! == Y) &&
               (explicitArgs[1]! == x) then
              funTransRulesMapRef.modify (λ m => m.insert (funTransName, .const) name)
              return ()
            else
              throwError "Constant rule is expecting exactly two explicit arguments `{← ppExpr Y}` and `{← ppExpr x}`!"

          -- composition
          if let .some (f,g) ← isComp F then
            dbg_trace s!"Composition rule for `{funTransName}` detected!"

            if (explicitArgs.size ≠ 2) then
              throwError "Composition rule is expecting exactly two explicit arguments `{← ppExpr f}` and `{← ppExpr g}`!"
  
            if (explicitArgs[0]! == f) &&
               (explicitArgs[1]! == g) then
              funTransRulesMapRef.modify (λ m => m.insert (funTransName, .comp) name)
              return ()
            else
              throwError "Composition rule is expecting exactly two explicit arguments `{← ppExpr f}` and `{← ppExpr g}`!"

          -- swap
          if let .some f ← isSwap F then
            dbg_trace s!"Swap arguments rule for `{funTransName}` detected!"

            if (explicitArgs.size ≠ 1) then
              throwError "Swap arguments rule is expecting exactly one explicit argument `{← ppExpr f}`!"
  
            if (explicitArgs[0]! == f) then
              funTransRulesMapRef.modify (λ m => m.insert (funTransName, .swap) name)
              return ()
            else
              throwError "Swap arguments rule is expecting exactly one explicit argument `{← ppExpr f}`!"

          -- forallMap
          if let .some f ← isForallMap F then
            dbg_trace s!"Forall map rule for `{funTransName}` detected!"

            if (explicitArgs.size ≠ 1) then
              throwError "Forall map rule is expecting exactly one explicit argument `{← ppExpr f}`!"
  
            if (explicitArgs[0]! == f) then
              funTransRulesMapRef.modify (λ m => m.insert (funTransName, .forallMap) name)
              return ()
            else
              throwError "Forall map rule is expecting exactly one explicit argument `{← ppExpr f}`!"


          -- eval
          if let .some (Y,x) ← isEval F then
            dbg_trace s!"Eval rule for `{funTransName}` detected!"

            if (explicitArgs.size ≠ 2) then
              throwError "Eval rule is expecting exactly two explicit arguments `{← ppExpr Y}` and `{← ppExpr x}`!"
  
            if (explicitArgs[0]! == Y) &&
               (explicitArgs[1]! == x) then
              funTransRulesMapRef.modify (λ m => m.insert (funTransName, .eval) name)
              return ()
            else
              throwError "Eval rule is expecting exactly two explicit arguments `{← ppExpr Y}` and `{← ppExpr x}`!"

          -- prodMap
          if let .some (f,g) ← isProdMap F then
            dbg_trace s!"Prod map rule for `{funTransName}` detected!"

            if (explicitArgs.size ≠ 2) then
              throwError "Prod map rule is expecting exactly two explicit arguments `{← ppExpr f}` and `{← ppExpr g}`!"
  
            if (explicitArgs[0]! == f) &&
               (explicitArgs[1]! == g) then
              funTransRulesMapRef.modify (λ m => m.insert (funTransName, .prodMap) name)
              return ()
            else
              throwError "Prod map rule is expecting exactly two explicit arguments `{← ppExpr f}` and `{← ppExpr g}`!"

          -- letBinop
          if let .some (f,g) ← isLetBinop F then
            dbg_trace s!"LetBinop rule for `{funTransName}` detected!"

            if (explicitArgs.size ≠ 2) then
              throwError "LetBinop rule is expecting exactly two explicit arguments `{← ppExpr f}` and `{← ppExpr g}`!"
  
            if (explicitArgs[0]! == f) &&
               (explicitArgs[1]! == g) then
              funTransRulesMapRef.modify (λ m => m.insert (funTransName, .letBinop) name)
              return ()
            else
              throwError "LetBinop rule is expecting exactly two explicit arguments `{← ppExpr f}` and `{← ppExpr g}`!"

          -- letComp
          if let .some (f,g) ← isLetComp F then
            dbg_trace s!"LetComp rule for `{funTransName}` detected!"

            if (explicitArgs.size ≠ 2) then
              throwError "LetComp rule is expecting exactly two explicit arguments `{← ppExpr f}` and `{← ppExpr g}`!"
  
            if (explicitArgs[0]! == f) &&
               (explicitArgs[1]! == g) then
              funTransRulesMapRef.modify (λ m => m.insert (funTransName, .letComp) name)
              return ()
            else
              throwError "LetComp rule is expecting exactly two explicit arguments `{← ppExpr f}` and `{← ppExpr g}`!"


          throwError s!"Unrecognised function transformation rule!\nPossible forms of a rule are:\n{FunTransRuleType.all.map (λ rule => ("  " ++ toString funTransName ++ " " ++ rule.expectedForm ++ '\n'.toString)) |> String.join}"
      )           



-- Function propositions are currently solved via type class resolutio
macro "fun_prop" : attr => `(attr|instance)
macro "fun_prop_def" : attr => `(attr|class)
macro "fun_prop_rule" : attr => `(attr|instance)
