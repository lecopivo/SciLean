import SciLean.Core.Tactic.FunctionTransformation.AttribInit
import SciLean.Core.Tactic.FunctionTransformation.Core

import SciLean.Core
import SciLean.Data.ArrayType
import SciLean.Data.DataArray

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Instances.Real

import Qq

namespace SciLean

#check LinearMap

infixr:25 " =>[C] " => ContinuousMap

open Lean.TSyntax.Compat in
macro "λ"   xs:Lean.explicitBinders " =>[C] " b:term : term =>
  Lean.expandExplicitBinders ``ContinuousMap.mk xs b

open Lean Meta

variable [MonadControlT MetaM n] [Monad n]

inductive FunType where
  | normal                    -- normal function
  | map (funSpaceName : Name) -- special kind of map like linear, smooth, continuous etc.
deriving Repr, BEq, Inhabited

instance : ToString FunType := ⟨λ t => toString (repr t)⟩

/-- Makes a function out of lambda expression `f` -/
def FunType.mkFun (funType : FunType) (f : Expr) : MetaM Expr :=
  match funType with
  | normal => pure f
  | map funSpaceName =>
    if funSpaceName == ``SmoothMap then
      mkAppOptM ``SmoothMap.mk #[none,none,none,none,f,none]
    else if funSpaceName == ``LinMap then
      mkAppOptM ``LinMap.mk #[none,none,none,none,f,none]
    else if funSpaceName == ``PowType then
      mkAppM ``introPowElem #[f]
    else if funSpaceName == ``ContinuousMap then
      mkAppM ``ContinuousMap.mk #[f]
    else
      throwError s!"Unknown function type `{funSpaceName}`"

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

def isFunLambda? (e : Expr) : Option (FunType × Name × Expr × Expr × BinderInfo) := 
  match e with
  | .lam n d b bi => 
    return (.normal, n, d, b, bi)
  | mkApp6 (.const ``SmoothMap.mk _) _ _ _ _ (.lam n d b bi) _ => 
    return (.map ``SmoothMap, n, d, b, bi)
  | mkApp6 (.const ``LinMap.mk _) _ _ _ _ (.lam n d b bi) _ => 
    return (.map ``LinMap, n, d, b, bi)
  | mkApp6 (.const ``introPowElem _) _ _ _ _ _ (.lam n d b bi) => 
    return (.map ``PowType, n, d, b, bi)
  | mkApp6 (.const ``ContinuousMap.mk _) _ _ _ _ (.lam n d b bi) _ => 
    return (.map ``ContinuousMap, n, d, b, bi)
  | _ => none

def isFunApp? (e : Expr) : Option (FunType × Expr × Expr) :=
  match e with
  | mkApp6 (.const ``SmoothMap.val _) _ _ _ _ f x => 
    return (.map ``SmoothMap, f ,x)
  | mkApp6 (.const ``LinMap.val _) _ _ _ _ f x => 
    return (.map ``LinMap, f ,x)
  | mkApp6 (.const ``FunLike.coe _) (mkApp4 (.const ``ContinuousMap _) _ _ _ _) _ _ _ f x => 
    return (.map ``ContinuousMap, f, x)
  | mkApp8 (.const ``getElem _) _ _ _ _ _ f x _ =>
    return (.map ``PowType, f ,x) -- should we double check that it is indeed PowType ? 
  | .app f x => 
    return (.normal, f, x)
  | _ => none

partial def getFunAppFn (e : Expr) : Expr := 
  if let .some (_, f, _) := isFunApp? e then
    getFunAppFn f
  else
    e

-- TODO: implement version that does not create reversed array
private partial def getFunAppArgsRevAux (e : Expr) (args : Array Expr) : Expr × Array Expr := 
  if let .some (_, f, x) := isFunApp? e then
    getFunAppArgsRevAux f (args.push x)
  else
    (e, args)

def getFunAppArgs (e : Expr) : Array Expr := 
  (getFunAppArgsRevAux e #[]).2.reverse

def isFunSpace? (e : Expr) : MetaM (Option FunType) := 
  match e with  
  | .forallE .. => return some .normal
  | mkApp4 (.const ``SmoothMap _) _ _ _ _ => return some (.map ``SmoothMap)
  | mkApp4 (.const ``LinMap _) _ _ _ _ => return some (.map ``LinMap)
  | mkApp4 (.const ``ContinuousMap _) _ _ _ _ => return some (.map ``ContinuousMap)
  | e => do
    let X? ← Meta.mkFreshExprMVar (mkSort levelOne)
    let Y? ← Meta.mkFreshExprMVar (mkSort levelOne)
    let arrayType := mkApp3 (.const ``ArrayType [.zero, .zero, .zero]) e X? Y?

    -- synthesizing ArrayType fills in X? and Y?
    let .some _ ← trySynthInstance arrayType 
      | return none

    -- -- make sure that it is indeed PowType
    -- if ¬(← isDefEq e (← mkAppOptM ``PowTypeCarrier #[X?, Y?, none, none])) then
    --   return none

    return some (.map ``PowType)

def mkFunSpace (funType : FunType) (X Y : Expr) : MetaM Expr :=
  match funType with
  | .normal => mkArrow X Y
  | .map ``SmoothMap => mkAppM ``SmoothMap #[X,Y]
  | .map ``LinMap => mkAppM ``LinMap #[X,Y]
  | .map ``ContinuousMap => mkAppM ``ContinuousMap #[X,Y]
  | .map ``PowType => mkAppM ``PowTypeCarrier #[X,Y]
  | .map n => throwError "Error in `mkFunSpace`, unrecognized function type `{n}`"

def mkFunApp1M (f x : Expr) : MetaM Expr := do
  let F ← inferType f
  let .some funType ← isFunSpace? F
    | throwError "Error in `mkFunAppM`: `{← ppExpr f}` is not a function!"
  match funType with
  | .normal => return .app f x
  | .map ``SmoothMap => mkAppM ``SmoothMap.val #[f, x]
  | .map ``LinMap => mkAppM ``LinMap.val #[f, x]
  | .map ``ContinuousMap => mkAppM ``FunLike.coe #[f, x]
  | .map ``PowType => do
    let fx ← mkAppM ``getElem #[f, x]
    mkAppM' fx #[(.const ``True.intro [])]
  | .map n => throwError "Error in `mkFunSpace`, unrecognized function type `{n}`"

def mkFunAppM (f : Expr) (xs : Array Expr) : MetaM Expr := 
  xs.foldlM (init := f) λ f x => mkFunApp1M f x

-- There is probably a better implementation
def funHeadBeta (e : Expr) : MetaM Expr := 
  let f := getFunAppFn e
  let args := getFunAppArgs e
  args.foldlM (init := f) λ f arg => do
    if let .some (_, _, _, b, _) := isFunLambda? f then
      pure (b.instantiate1 arg)
    else
      mkFunApp1M f arg


private partial def funTelescopeImp (e : Expr) (maxArg? : Option Nat) (k : Array (Expr × FunType) → Expr → MetaM α) : MetaM α := do
  process (← getLCtx) #[] #[] false e
where
  process (lctx : LocalContext) (fvars : Array Expr) (funTypes : Array FunType) (stop : Bool) (e : Expr) : MetaM α := do
    if let .some (funType, n, d, b, bi) := isFunLambda? e then
      if ¬stop then 
        let stop := 
          match maxArg? with
          | some maxArg => fvars.size + 1 = maxArg 
          | none => false
        let d := d.instantiateRevRange 0 fvars.size fvars
        let fvarId ← mkFreshFVarId
        let lctx := lctx.mkLocalDecl fvarId n d bi
        let fvar := mkFVar fvarId
        return ← (process lctx (fvars.push fvar) (funTypes.push funType) stop b)

    let e := e.instantiateRevRange 0 fvars.size fvars
    withReader (fun ctx => { ctx with lctx := lctx }) do
      -- withNewLocalInstancesImp fvars j do -- no clue what this does
        k (fvars.zip funTypes) e

def funTelescope (e : Expr) (k : Array (Expr × FunType) → Expr → n α) : n α := 
  map2MetaM (fun k => funTelescopeImp e none k) k

/-- Same as `funTelescope` but you can limit the number of consumed arguments -/
def funTelescope' (e : Expr) (maxArg : Nat) (k : Array (Expr × FunType) → Expr → n α) : n α := 
  map2MetaM (fun k => funTelescopeImp e (some maxArg) k) k

def mkFunFVars (xs : Array (Expr × FunType)) (e : Expr) : MetaM Expr := do
  xs.foldrM (init := e) λ (x, funType) e => do pure (← funType.mkFun (← mkLambdaFVars #[x] e))

-- There is probably a better implementation
def funEta (e : Expr) : MetaM Expr := do
  funTelescope e λ xs b => do
    let mut b := b
    let mut j := xs.size
    for _ in [0:xs.size] do
      let (x,funType) := xs[j-1]!
      if let .some (funType', f, x') := isFunApp? b then
        if (funType == funType') && (x == x') then
          j := j - 1
          b := f
      else
        break
    mkFunFVars xs[0:j] b


def bar : (ℝ ⟿ ℝ) ⟿ ℝ ⟿ ℝ ⊸ ℝ := sorry

open Qq
#eval show MetaM Unit from do
  let f := q(λ (n : Nat) => λ (x : ℝ) ⟿ λ (z : ℝ) ⊸ z)
  let f := q(λ (n : Nat) => λ (x : ℝ) ⟿ ⊞ (i : Fin n), (x:ℝ))
  
  IO.println s!"original function:  {← ppExpr f}"
  
  funTelescope' f 2 λ xs b => do
    let f' ← mkFunFVars xs b
    IO.println s!"arguments: {← xs.mapM λ (x,_) => ppExpr x}"
    IO.println s!"body: {← ppExpr b}"
    IO.println s!"recovered function: {← ppExpr f'}"

  IO.println s!"`ℝ → ℝ` is function space: {(← isFunSpace? q(ℝ→ℝ)).isSome}"
  IO.println s!"`ℝ ⟿ ℝ` is function space: {(← isFunSpace? q(ℝ⟿ℝ)).isSome}"
  IO.println s!"`ℝ ⊸ ℝ` is function space: {(← isFunSpace? q(ℝ⊸ℝ)).isSome}"
  IO.println s!"`ℝ^{3}` is function space: {(← isFunSpace? q(ℝ^{3})).isSome}"
  IO.println s!"`Vec3 ℝ` is function space: {(← isFunSpace? q(Vec3 ℝ)).isSome}"
  IO.println s!"`Array ℝ` is function space: {(← isFunSpace? q(Array ℝ)).isSome}"

  let n := q(10 : Nat)
  let x := q(42 : ℝ)
  let i := q(5 : Fin 10)

  let fnxi ← mkFunAppM f #[n,x,i]
  let fnxi' ← funHeadBeta fnxi

  IO.println s!"test application: {← ppExpr fnxi}"
  IO.println s!"beta red: {← ppExpr fnxi'}"
  let f'   := getFunAppFn fnxi
  let nxi' := getFunAppArgs fnxi
  IO.println s!"Function of application: {← ppExpr f'}"
  IO.println s!"Args of application: {← (nxi'.mapM ppExpr)}"

  let fst := q(λ xy : Nat × Nat => xy.fst)
  let add := q(λ (x y : ℝ) ⟿ (λ x y ⟿ x + y) x y)
  IO.println s!"eta reduced fst: {← ppExpr (← funEta fst)}"
  IO.println s!"eta reduced add: {← ppExpr (← funEta add)}"

  let f := q(λ (x : ℝ) ⟿ x + x)
  let x : Q(ℝ) := q(1)

  IO.println s!"{← ppExpr (← mkFunApp1M f x)}"
  IO.println s!"{← ppExpr (← funHeadBeta (← (mkFunApp1M f x)))}"

  let f := q(λ (x : _root_.Real) =>[C] x + x)
  let x := q(1 : _root_.Real)
  IO.println s!"{← ppExpr (← mkFunApp1M f x)}"
  IO.println s!"{← ppExpr (← funHeadBeta (← (mkFunApp1M f x)))}"
