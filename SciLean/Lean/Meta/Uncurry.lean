import Lean
import Batteries.Lean.Expr

import SciLean.Lean.Expr
import SciLean.Lean.Array
import SciLean.Lean.Meta.Basic
import SciLean.Util.RewriteBy

import Mathlib.Logic.Function.Basic

set_option linter.unusedVariables false

namespace Lean.Meta


/-- Returns `#[x.1, x.2.1, x.2.2.1, ..., x.2....2]` with `n` elements.
Where `·.1` and `·.2` are `Prod` projections. -/
def mkProdSplitElem' (x : Expr) (n : Nat) : Array Expr :=
  if n = 0 then
    #[]
  else if n = 1 then
    #[x]
  else
    go n x #[]
where
  go (n : Nat) (x : Expr) (xs : Array Expr) : Array Expr :=
    match n with
    | 0 => xs
    | 1 => xs.push x
    | n+1 => go n (x.proj ``Prod 1) (xs.push (x.proj ``Prod 0))


/-- Takes expression `b` with free vars `xs = #[x₁, ..., xₙ]` and returns lambda function in one
argument of the form:
```
fun x =>
  let x₁ := x.1
  let x₂ := x.2.1
  ...
  let xₙ := x.2....2
  b
``` -/
def mkUncurryLambdaFVars (xs : Array Expr) (b : Expr) (withLet:=true) : MetaM Expr := do

  if xs.size = 1 then return ← mkLambdaFVars xs b

  let x ← mkProdElem xs
  let X ← inferType x

  let xnames ← xs.mapM (fun x => x.fvarId!.getUserName)

  withLocalDeclD `x X fun xvar => do

    let xvals := mkProdSplitElem' xvar xs.size

    if withLet then
      withLetDecls xnames xvals fun xvars => do
        let b := b.replaceFVars xs xvars
        mkLambdaFVars (#[xvar] ++ xvars) b
    else
      let b := b.replaceFVars xs xvals
      mkLambdaFVars #[xvar] b


/-- Takes function of `n` arguments and returns uncurried version of `f` in specific form:
```
fun x =>
  let x₁ := x.1
  let x₂ := x.2.1
  ...
  let xₙ := x.2....2
  f x₁ ... xₙ
``` -/
def mkUncurryFun' (n : Nat) (f : Expr) (withLet := true) : MetaM Expr := do
  if n ≤ 1 then
    return f
  else
    lambdaBoundedTelescope f n fun xs b => do
      mkUncurryLambdaFVars xs b (withLet := withLet)


private def _root_.Lean.Expr.isProjOf (x y : Expr) : Bool :=
  if (x == (.proj ``Prod 0 y)) ||
     (x == (.proj ``Prod 1 y)) then
    true
  else
    match x with
    | .proj ``Prod _ x' => isProjOf x' y
    | _ => false


private partial def uncurryBodyTelescope (e : Expr) (x : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  go e x #[]
where
  go (b : Expr) (x' : Expr) (fvars : Array Expr) := do
    match b with
    | .letE n t xi b ndep => do

      -- expected all nice, keep on going
      -- let xi := x.2. ... .1
      if xi == (.proj ``Prod 0 x') then
        withLocalDeclD n t fun xivar => do
          go (b.instantiate1 xivar) (.proj ``Prod 1 x') (fvars.push xivar)

      -- terminating argument, we are done
      -- let xi := x.2. ... .2
      else if xi == x' then
        if b.containsFVar x.fvarId! then
          k #[x] e
        else
          withLocalDeclD n t fun xivar => do
            let b := b.instantiate1 xivar
            k (fvars.push xivar) b

      -- looks like we skipped argument
      -- let xi := x.2. ...  but not what we expected
      else if xi.isProjOf x' then
        let x' := (.proj ``Prod 1 x')
        withLocalDeclD `x (← inferType x') fun xivar => do
          -- here we do not instantiate!
          -- but call again with updated `x'`
          go (.letE n t xi b ndep) x' (fvars.push xivar)

      -- completely differente let binding
      -- we are done with instantiating variables
      else
        let b := (.letE n t xi b ndep)
        if b.containsFVar x.fvarId! then
          k #[x] e
        else
          withLocalDeclD `x (← inferType x') fun xivar => do
            k (fvars.push xivar) b
    | _ =>
      if fvars.size = 0 then
        k #[x] e
      else
        withLocalDeclD `x (← inferType x') fun xivar => do
          k (fvars.push xivar) b


/-- Lamda telescope for uncurried functions. This version peels off only one lambda.

For input function
```
fun x =>
  let x₁ := x.1
  let x₂ := x.2.1
  ...
  let xₙ := x.2....2
  f x₁ ... xₙ
```
call
```
k #[y₁, ..., yₙ] (f y₁ ... yₙ)
```
where `yᵢ` are fresh free variables. -/
def uncurryLambdaTelescopeOnceImpl [Inhabited α] (f : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  forallBoundedTelescope (← inferType f) (some 1) fun xs b => do
    if xs.size = 0 then
      throwError "function expected in `uncurryLambdaTelescopeOnce` got {f}"

    let x := xs[0]!
    uncurryBodyTelescope (f.beta #[x]) x k

/-- Simproc that replaces `↿f` with `f` in uncurried lambda form. -/
dsimproc_decl hasUncurryNormalize (↿_) := fun e => do

  match e.getAppFnArgs with
  | (``Function.HasUncurry.uncurry, #[F,_,Y,_,f]) =>
    forallTelescope F fun Xs' Y' => do

      -- right now we assume that function is always fully uncurried
      -- TODO: generalize this
      unless ← isDefEq Y Y' do return .continue
      let arity := Xs'.size
      return .visit (← mkUncurryFun' arity f)
  | _ => return .continue


/-- Simproc that replaces `Function.uncurry` with `f` in uncurried lambda form. -/
dsimproc_decl uncurryNormalize (Function.uncurry _) := fun e => do

  match e.getAppFnArgs with
  | (``Function.uncurry, #[_,_,_,f]) =>
      return .visit (← mkUncurryFun' 2 f)
  | _ => return .continue
