import Lean
import Qq
import Batteries.Lean.Expr
import Mathlib.Lean.Expr
import Mathlib.Tactic.FunProp.ToBatteries

namespace Lean.Expr


@[match_pattern]
def mkAppB (f a b : Expr) := mkApp (mkApp f a) b
@[match_pattern]
def mkApp2 (f a b : Expr) := mkAppB f a b
@[match_pattern]
def mkApp3 (f a b c : Expr) := mkApp (mkAppB f a b) c
@[match_pattern]
def mkApp4 (f a b c d : Expr) := mkAppB (mkAppB f a b) c d
@[match_pattern]
def mkApp5 (f a b c d e : Expr) := mkApp (mkApp4 f a b c d) e
@[match_pattern]
def mkApp6 (f a b c d e₁ e₂ : Expr) := mkAppB (mkApp4 f a b c d) e₁ e₂
@[match_pattern]
def mkApp7 (f a b c d e₁ e₂ e₃ : Expr) := mkApp3 (mkApp4 f a b c d) e₁ e₂ e₃
@[match_pattern]
def mkApp8 (f a b c d e₁ e₂ e₃ e₄ : Expr) := mkApp4 (mkApp4 f a b c d) e₁ e₂ e₃ e₄
@[match_pattern]
def mkApp9 (f a b c d e₁ e₂ e₃ e₄ e₅ : Expr) := mkApp5 (mkApp4 f a b c d) e₁ e₂ e₃ e₄ e₅
@[match_pattern]
def mkApp10 (f a b c d e₁ e₂ e₃ e₄ e₅ e₆ : Expr) := mkApp6 (mkApp4 f a b c d) e₁ e₂ e₃ e₄ e₅ e₆

def explicitArgIds (e : Expr) : Array Nat :=
  run e #[] 0
where run (e : Expr) (ids : Array Nat) (i : Nat) : Array Nat :=
  match e with
  | .forallE _ _ e' bi =>
    if bi.isExplicit then
      run e' (ids.push i) (i+1)
    else
      run e' ids (i+1)
  | .lam _ _ e' bi =>
    if bi.isExplicit then
      run e' (ids.push i) (i+1)
    else
      run e' ids (i+1)
  | _ => ids

partial def flattenLet? (e : Expr) : Option Expr := do
  match e with
  | .letE xName xType xVal xBody _ =>
    match xVal with
    | .letE yName yType yVal yBody _ =>

      let e' :=
        .letE yName yType yVal
          (.letE xName xType yBody (xBody.liftLooseBVars 1 1) default) default

      return (flattenLet? e').getD e'

    | _ => do
      return (.letE xName xType xVal (← flattenLet? xBody) default)
  | _ => none


partial def flattenLet (e : Expr) : Expr := e.flattenLet?.getD e


partial def splitLetProd? (e : Expr) : Option Expr := do
  match e with
  | .letE xyName xyType xyVal xyBody _ =>
    if let .some (X,Y,x,y) := xyVal.app4? ``Prod.mk then

      let xy := mkApp4 xyVal.getAppFn X Y (.bvar 1) (.bvar 0)
      let e' :=
        Expr.letE (xyName.appendAfter "₁") X x
          (.letE (xyName.appendAfter "₂") Y y ((xyBody.liftLooseBVars 1 2).instantiate1 xy) default) default

      return (splitLetProd? e').getD e'
    else do
      return (.letE xyName xyType xyVal (← splitLetProd? xyBody) default)
  | _ => none

partial def splitLetProd (e : Expr) : Option Expr := e.splitLetProd?.getD e


def mapLooseBVarIds (e : Expr) (f : Nat → Option Nat) (offset : Nat := 0) : Expr :=
  if e.looseBVarRange ≤ offset then
    e
  else
    match e with
    | .bvar i =>
      if offset ≤ i then
        match f (i-offset) with
        | .some i' => .bvar (i' + offset)
        | .none => .bvar i
      else
        .bvar i
    | .proj typeName idx e => .proj typeName idx (e.mapLooseBVarIds f offset)
    | .letE name type val body d =>
      .letE name (type.mapLooseBVarIds f offset) (val.mapLooseBVarIds f offset) (body.mapLooseBVarIds f (offset+1)) d
    | .forallE name type body bi =>
      .forallE name (type.mapLooseBVarIds f offset) (body.mapLooseBVarIds f (offset+1)) bi
    | .lam name type body bi =>
      .lam name (type.mapLooseBVarIds f offset) (body.mapLooseBVarIds f (offset+1)) bi
    | .app f' x =>
      .app (f'.mapLooseBVarIds f offset) (x.mapLooseBVarIds f offset)
    | .mdata data e =>
      .mdata data (e.mapLooseBVarIds f offset)
    | e => e


inductive ReplaceStep where
| noMatch
| done (e : Expr)
| yield (e : Expr)

inductive ReplaceResult where
| done (e : Expr)
| yield (e : Expr)


@[specialize]
def replaceM {m} [Monad m] (f : Expr → m ReplaceStep) (e : Expr) : m Expr := do
  match ← run e with
  | .done e => pure e
  | .yield e => pure e
where
  run (e : Expr) : m ReplaceResult := do
  match ← f e with
  | .done eNew => return (.done eNew)
  | .yield eNew => return (.yield eNew)
  | .noMatch    => match e with
    | .forallE _ d b _ =>
      match ← run d with
      | .done d => return .done (e.updateForallE! d b)
      | .yield d =>
      match ← run b with
      | .done b => return .done (e.updateForallE! d b)
      | .yield b => return .yield (e.updateForallE! d b)

    | .lam _ d b _     =>
      match ← run d with
      | .done d => return .done (e.updateLambdaE! d b)
      | .yield d =>
      match ← run b with
      | .done b => return .done (e.updateLambdaE! d b)
      | .yield b => return .yield (e.updateLambdaE! d b)

    | .mdata _ b       =>
      match ← run b with
      | .done b => return .done (e.updateMData! b)
      | .yield b => return .yield (e.updateMData! b)

    | .letE _ t v b _  =>
      match ← run t with
      | .done t => return .done (e.updateLet! t v b)
      | .yield t =>
      match ← run v with
      | .done v => return .done (e.updateLet! t v b)
      | .yield v =>
      match ← run b with
      | .done b => return .done (e.updateLet! t v b)
      | .yield b => return .yield (e.updateLet! t v b)

    | .app f a         =>
      match ← run f with
      | .done f => return .done (e.updateApp! f a)
      | .yield f =>
      match ← run a with
      | .done a => return .done (e.updateApp! f a)
      | .yield a => return .yield (e.updateApp! f a)

    | .proj _ _ b      =>
      match ← run b with
      | .done b => return .done (e.updateProj! b)
      | .yield b => return .yield (e.updateProj! b)

    | e                => return .yield e


/-- Replaces `xᵢ` with `yᵢ`, subterms of e with loose bvars are ignored. -/
def replaceExprs (e : Expr) (xs ys : Array Expr) : MetaM Expr :=
  e.replaceM (fun e' => do
    if e'.hasLooseBVars then
      return .noMatch
    else
      for x in xs, y in ys do
        if (← Meta.isDefEq x e') then
          return .yield y
      return .noMatch)

/-- Replace `nth`-th occurance of bound variable i in `e` with `v`.

Returns `.inl e'` if succesfully replaced or `.inr n` if `n` occurances, `n < nth`, of `i`-th bound variables have been found in `e`.

WARRNING: Currently it ignores types.
-/
def instantiateOnceNth (e v : Expr) (i : Nat) (nth : Nat) : Expr ⊕ Nat :=
  match e with
  | .bvar j =>
    if i = j then
      if nth = 0 then
        .inl v
      else
        .inr 1
    else
      .inr 0

  | .app f x =>
    match instantiateOnceNth x v i nth with
    | .inl x' => .inl (.app f x')
    | .inr a =>
    match instantiateOnceNth f v i (nth-a) with
    | .inl f' => .inl (.app f' x)
    | .inr b => .inr (a+b)

  | .letE n t y b _ =>
    match instantiateOnceNth y v i nth with
    | .inl y' => .inl (.letE n t y' b false)
    | .inr a =>
    match instantiateOnceNth b v (i+1) (nth-a) with
    | .inl b' => .inl (.letE n t y b' false)
    | .inr b => .inr (a+b)

  | .lam n t b bi =>
    match instantiateOnceNth b v (i+1) nth with
    | .inl b' => .inl (.lam n t b' bi)
    | .inr a => .inr a

  | .mdata _ x => instantiateOnceNth x v i nth

  | _ => .inr 0


/-- Replace bound variable with index `i` in `e` with `v` only once.

You can specify that you want to replace `nth`-th occurance of that bvar.

WARRNING: Currently it ignores types.
-/
def instantiateOnce (e v : Expr) (i : Nat) (nth := 0) : Expr :=
  match instantiateOnceNth e v i nth with
  | .inl e' => e'
  | _ => e


def myPrint : Expr → String
| .const n _ => n.toString
| .bvar n => s!"[{n}]"
| .app f x => f.myPrint ++ " " ++ x.myPrint
| .lam n _ x _ => s!"fun {n} => {x.myPrint}"
| .letE n _ v x _ => s!"let {n} := {v.myPrint}; {x.myPrint}"
| _ => "??"

/-- Remove all mdata for an expression -/
def purgeMData : Expr → Expr
| .app f x => .app f.purgeMData x.purgeMData
| .lam n t b bi => .lam n t.purgeMData b.purgeMData bi
| .letE n t v b d => .letE n t.purgeMData v.purgeMData b.purgeMData d
| .forallE n t b bi => .forallE n t.purgeMData b.purgeMData bi
| .mdata _ e => e.purgeMData
| e => e



/-- Returns number of leading lambda binders of an expression

Note: ignores meta data -/
def getLamBinderNum (e : Expr) : Nat :=
  go 0 e
where
  go (n : Nat) : Expr → Nat
  | .lam _ _ b _ => go (n+1) b
  | .mdata _ e => go n e
  | _ => n

/-- Returns number of leading forall binders of an expression

Note: ignores meta data -/
def getForallBinderNum (e : Expr) : Nat :=
  go 0 e
where
  go (n : Nat) : Expr → Nat
  | .forallE _ _ b _ => go (n+1) b
  | .mdata _ e => go n e
  | _ => n


/-- Get body of multiple bindings

Note: ignores meta data -/
def bindingBodyRec : Expr → Expr
| .lam _ _ b _ => b.bindingBodyRec
| .forallE _ _ b _ => b.bindingBodyRec
| .mdata _ e => e.bindingBodyRec
| e => e


def letBodyRec' (e : Expr) : Expr :=
  match e with
  | .letE _ _ _ b _ => b.letBodyRec'
  | .mdata _ e => e.letBodyRec'
  | e => e


/-- Is `e` function type with no dependent types?
-/
def isSimpleFunType (e : Expr) : Bool :=
  if ¬e.consumeMData.isForall then false else go e
where
  go (e : Expr) : Bool :=
    match e with
    | .forallE _ t b _ =>
      if t.hasLooseBVars || b.hasLooseBVars then
        false
      else
        go b
    | .mdata _ e => go e
    | _ => true


/--
Apply the given arguments to `f`, introduce let binding for every argument
that beta-reduces.

Examples:
- `betaWithLet (fun x y => t x y) #[]` ==> `fun x y => t x y`
- `betaWithLet (fun x y => t x y) #[a]` ==> `let x:=a; fun y => t x y`
- `betaWithLet (fun x y => t x y) #[a, b]` ==> `let x:=a; let y:=b; t x y`
- `betaWithLet (fun x y => t x y) #[a, b, c, d]` ==> `let x:=a; let y:=b; t x y c d`

TODO: maybe introduce let binding only if the variable appears multiple times
-/
partial def betaWithLet (f : Expr) (args : Array Expr) : Expr :=
  go f 0
where
  go (e : Expr) (i : Nat) : Expr :=
    if h : i<args.size then
      match e with
      | .lam n t b _ => .letE n t (args[i]'h) (go b (i+1)) false
      | .letE n t v b dep => .letE n t v (go b i) dep
      | .mdata _ e => (go e i)
      | _ => mkAppN e args[i:]
    else
      e

/-- `(fun x => e) a` ==> `e[x/a]`. -/
def headBetaWithLet (e : Expr) : Expr :=
  let f := e.getAppFn
  if f.isHeadBetaTargetFn false then betaWithLet f e.getAppArgs else e
