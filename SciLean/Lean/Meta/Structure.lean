import SciLean.Lean.Expr
import SciLean.Lean.Meta.Basic

namespace SciLean

open Lean Meta


private def buildMk (mk : Expr) (mks : List Expr) (vars vals : Array Expr) : MetaM Expr :=
  match mks with
  | [] => mkLambdaFVars vars (mkAppN mk vals)
  | mk' :: mks' =>
    lambdaTelescope mk' fun xs b =>
      buildMk mk mks' (vars++xs) (vals.push b)


/-- Decomposes an element `e` that is a nested application of constructors

For example, calling this function on `((a,b),c)` returns
 - list of elements `#[a, b, c]`
 - list of projections `#[fun x => x.1.1, fun x => x.1.2, fun x => x.2]`
 - function to build the structure back up `fun a b c => ((a,b),c))`
-/
private partial def splitByCtorsImpl (e : Expr) : MetaM (Array Expr × Array Expr × Expr) := do

  let fn := e.getAppFn
  let args := e.getAppArgs'
  let E ← inferType e
  let idE := Expr.lam `x E (.bvar 0) default

  let .const structName _ := E.getAppFn'
    | return (#[e], #[idE], idE)

  -- not structure
  let .some _ := getStructureInfo? (← getEnv) structName
    | return (#[e], #[idE], idE)

  let ctorVal := getStructureCtor (← getEnv) structName

  -- not application of ctor
  if fn.constName? ≠ .some ctorVal.name then
    return (#[e], #[idE], idE)

  -- not fully applied ctor
  if args.size ≠ ctorVal.numParams + ctorVal.numFields then
    return (#[e], #[idE], idE)

  let mk := mkAppN fn args[0:ctorVal.numParams]

  let fields : Array _ := args[ctorVal.numParams : ctorVal.numParams + ctorVal.numFields]
  let (eis, tmp) := (← fields.mapM splitByCtorsImpl).unzip
  let (projs, mks) := tmp.unzip

  let mk ← buildMk mk mks.toList #[] #[]

  let projs := projs
    |>.mapIdx (fun idx projs' =>
       projs'.map (fun proj' => Expr.lam `x E (proj'.app (Expr.proj structName idx (.bvar 0))).headBeta default))
    |>.flatten

  return (eis.flatten, projs, mk)


/-- Decomposes an element `e` that is a nested application of constructors

For example, calling this function on `x : (Nat×Nat)×Nat` returns `(#[x.1.1, x.1.2, x.1], fun a b c => ((a,b),c))`
-/
def splitByCtors? (e : Expr) : MetaM (Option (Array Expr × Array Expr × Expr)) := do
  withTraceNode `splitByCtors (fun _ => do pure s!"splitByCtors") do
  let r ← splitByCtorsImpl e
  if r.1.size = 1 then
    return none
  else
    return r
