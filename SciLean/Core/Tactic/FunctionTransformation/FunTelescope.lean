import SciLean.Core.Tactic.FunctionTransformation.AttribInit
import SciLean.Core.Tactic.FunctionTransformation.Core

import SciLean.Core
import SciLean.Data.ArrayType
import SciLean.Data.DataArray
import Qq

namespace SciLean

open Lean Meta


variable [MonadControlT MetaM n] [Monad n]

inductive FunType where
  | normal                    -- normal function
  | map (funSpaceName : Name) -- special kind of map like linear, smooth, continuous etc.
deriving Repr, BEq

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
  | _ => none

def isApp? (e : Expr) : Option (FunType × Expr × Expr) :=
  match e with
  | .app (.lam ..) x => 
    return (.normal, e.getAppFn, x)
  | mkApp6 (.const ``SmoothMap.val _) _ _ _ _ f x => 
    return (.map ``SmoothMap, f ,x)
  | mkApp6 (.const ``LinMap.val _) _ _ _ _ f x => 
    return (.map ``LinMap, f ,x)
  | mkApp8 (.const ``getElem _) _ _ _ _ _ f x _ =>
    return (.map ``PowType, f ,x) -- should we double check that it is indeed PowType ? 
  | _ => none

def isFunSpace? (e : Expr) : MetaM (Option (FunType × Expr × Expr)) := 
  match e with  
  | .forallE _ X Y _ => if !Y.hasLooseBVars then return some (.normal, X, Y) else return none
  | mkApp4 (.const ``SmoothMap _) X Y _ _ => return some (.map ``SmoothMap, X, Y)
  | mkApp4 (.const ``LinMap _) X Y _ _ => return some (.map ``LinMap, X, Y)
  | e => do
    let X? ← Meta.mkFreshExprMVar (mkSort levelOne)
    let Y? ← Meta.mkFreshExprMVar (mkSort levelOne)
    let arrayType := mkApp3 (.const ``ArrayType [.zero, .zero, .zero]) e X? Y?

    -- synthesizing ArrayType fills in X? and Y?
    let .some _ ← trySynthInstance arrayType 
      | return none

    -- -- make sure that it is indeed PowType
    -- let .some _ ← trySynthInstance (mkApp3 (.const ``PowType []) e X? Y?)
    --   | return none

    return some (.map ``PowType, X?, Y?)

def mkFunSpace (funType : FunType) (X Y : Expr) : MetaM Expr :=
  match funType with
  | .normal => mkArrow X Y
  | .map ``SmoothMap => mkAppM ``SmoothMap #[X,Y]
  | .map ``LinMap => mkAppM ``LinMap #[X,Y]
  | .map ``PowType => mkAppM ``PowTypeCarrier #[X,Y]
  | .map n => throwError "Error in `mkFunSpace`, unrecognized function type `{n}`"

def mkFunAppM (f x : Expr) : MetaM Expr := do
  let F ← inferType f
  let .some (funType, X, Y) ← isFunSpace? F
    | throwError "Error in `mkFunAppM`: `{← ppExpr f}` is not a function!"
  match funType with
  | .normal => return .app f x
  | .map ``SmoothMap => mkAppM ``SmoothMap.val #[f, x]
  | .map ``LinMap => mkAppM ``LinMap.val #[f, x]
  | .map ``PowType => mkAppOptM ``getElem #[none, none, none, none, none, f, x, some (.const ``True.intro [])]
  | .map n => throwError "Error in `mkFunSpace`, unrecognized function type `{n}`"

-- This does not work as expecteed
def funHeadBeta1 (e : Expr) : Expr := 
  if let .some (funType, f, x) := isApp? e then
    if let .some (funType', _, _, b, _) := isFunLambda? f then
      if funType == funType' then
        b.instantiate1 x
      else 
        e
    else
      e
  else
    e

private partial def funTelescopeImp (e : Expr) (k : Array (Expr × FunType) → Expr → MetaM α) : MetaM α := do
  process (← getLCtx) #[] #[] 0 e
where
  process (lctx : LocalContext) (fvars : Array Expr) (funTypes : Array FunType) (j : Nat) (e : Expr) : MetaM α := do
    if let .some (funType, n, d, b, bi) := isFunLambda? e then
      let d := d.instantiateRevRange j fvars.size fvars
      let fvarId ← mkFreshFVarId
      let lctx := lctx.mkLocalDecl fvarId n d bi
      let fvar := mkFVar fvarId
      process lctx (fvars.push fvar) (funTypes.push funType) j b
    else
      let e := e.instantiateRevRange j fvars.size fvars
      withReader (fun ctx => { ctx with lctx := lctx }) do
        -- withNewLocalInstancesImp fvars j do -- no clue what this does
          k (fvars.zip funTypes) e

def funTelescope (e : Expr) (k : Array (Expr × FunType) → Expr → n α) : n α := 
  map2MetaM (fun k => funTelescopeImp e k) k

#check mkLambdaFVars

def mkFunFVars (xs : Array (Expr × FunType)) (e : Expr) : MetaM Expr := do
  xs.foldrM (init := e) λ (x, funType) e => do pure (← funType.mkFun (← mkLambdaFVars #[x] e))


open Qq
#eval show MetaM Unit from do
  let f := q(λ (n : Nat) => λ (x : ℝ) ⟿ λ (z : ℝ) ⊸ z)
  let f := q(λ (n : Nat) => λ (x : ℝ) ⟿ ⊞ (i : Fin n), (x:ℝ))
  
  IO.println s!"original function:  {← ppExpr f}"
  
  funTelescope f λ xs b => do
    let f' ← mkFunFVars xs b
    IO.println s!"arguments: {← xs.mapM λ (x,_) => ppExpr x}"
    IO.println s!"recovered function: {← ppExpr f'}"

  IO.println s!"`ℝ → ℝ` is function space: {(← isFunSpace? q(ℝ→ℝ)).isSome}"
  IO.println s!"`ℝ ⟿ ℝ` is function space: {(← isFunSpace? q(ℝ⟿ℝ)).isSome}"
  IO.println s!"`ℝ ⊸ ℝ` is function space: {(← isFunSpace? q(ℝ⊸ℝ)).isSome}"
  IO.println s!"`ℝ^{3}` is function space: {(← isFunSpace? q(ℝ^{3})).isSome}"
  IO.println s!"`Vec3 ℝ` is function space: {(← isFunSpace? q(Vec3 ℝ)).isSome}"
  IO.println s!"`Array ℝ` is function space: {(← isFunSpace? q(Array ℝ)).isSome}"

  let f := q(λ (x : ℝ) ⟿ x + x)
  let x : Q(ℝ) := q(1)

  IO.println s!"{← ppExpr (← mkFunAppM f x)}"
  IO.println s!"{← ppExpr (funHeadBeta1 (← (mkFunAppM f x)))}"

set_option pp.all true in
#check ArrayType (ℝ^{3}) (Fin 3) ℝ

