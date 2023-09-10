import SciLean.Lean.Expr
import SciLean.Lean.Meta.Basic

namespace SciLean

set_option linter.unusedVariables false

open Lean Meta Qq

set_option pp.funBinderTypes true 

/-- Decomposes an element `e` of possible nested structure and returns a function put it back together.

For example, calling this function on `x : (Nat×Nat)×Nat` returns `(#[x.1.1, x.1.2, x.1], fun a b c => ((a,b),c))`
-/
partial def decomposeStructure (e : Expr) : MetaM (Array Expr × Expr) := do
  let E ← inferType e
  let idE := .lam `x E (.bvar 0) default

  let .const structName lvls := E
    | return (#[e], idE)

  let .some info := getStructureInfo? (← getEnv) structName
    | return (#[e], idE)

  let ctorVal := getStructureCtor (← getEnv) structName

  if E.getAppNumArgs != ctorVal.numParams then
    return (#[e], idE)

  if ctorVal.numFields ≤ 1 then
    return (#[e], idE)
  
  let eis ← info.fieldNames.mapM (fun fname => do
    let projFn := getProjFnForField? (← getEnv) structName fname |>.get!
    mkAppM projFn #[e] >>= reduceProjOfCtor)

  let (eis,mks) := (← eis.mapM decomposeStructure).unzip

  -- this implementation of combining `mks` together works but it is probably not very efficient
  let mk := mkAppN (.const ctorVal.name lvls) E.getAppArgs
  let mk ← mks.foldlM (init:=mk)
    (fun mk mki => do
      forallTelescope (← inferType mki) fun xs _ => do
        let mk ← mkAppM' mk #[(←mkAppM' mki xs).headBeta]
        forallTelescope (← inferType mk) fun ys _ => do
          mkLambdaFVars (ys++xs) (←mkAppM' mk ys).headBeta)
  
  return (eis.flatten, mk)


/-- Takes a type `X` of a nested structure  and splits it into two `X₁` and `X₂`. 
Returns function `p₁ : X → X₁`, `p₂ : X → X₂` and `q : X₁ → X₂ → X` that are inverse of each other.

Example:
```
split ((u,v),(w,x),y) (fun i => i%2==0)
```
returns
```
p₁ := fun ((a,b),(c,d),e) => (a,c,e)
p₂ := fun ((a,b),(c,d),e) => (b,d)
q  := fun ((a,c,e),(b,d)) => ((a,b),(c,d),e)
```
-/
def splitStructure (e : Expr) (split : Nat → Expr → Bool) : MetaM (Option (Expr × Expr × Expr)) := do
  let X ← inferType e
  withLocalDecl `x default X fun x => do
    let (xis, xmk) ← decomposeStructure x
    let (eis, _) ← decomposeStructure e

    let (xis₁, xis₂, ids) := xis.splitIdx (fun i _ => split i.1 eis[i.1]!)

    if xis₁.size = 0 || xis₂.size = 0 then
      return none
    
    let x₁ ← mkProdElem xis₁
    let x₂ ← mkProdElem xis₂
    let p₁ ← mkLambdaFVars #[x] x₁
    let p₂ ← mkLambdaFVars #[x] x₂

    withLocalDecl `x₁ default (← inferType x₁) fun x₁' => do
    withLocalDecl `x₂ default (← inferType x₂) fun x₂' => do
      let (xis₁', _) ← decomposeStructure x₁'
      let (xis₂', _) ← decomposeStructure x₂'

      let x' := (← mkAppM' xmk (ids.mergeSplit xis₁' xis₂')).headBeta
      let q ← mkLambdaFVars #[x₁',x₂'] x'

      return (p₁,p₂,q)


/-- Takes a function `f : X → Y` and find projections `p₁ : X → X₁`, `p₂ : X → X₂` and function `f' : X₁ → Y` such that `h : f = f' ∘ p₁`

returns `(f, p₁, p₂, h)`
-/
def factorDomainThroughProjections (f : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let f ← instantiateMVars f
  match f with 
  | .lam xName xType xBody xBi => 
    withLocalDecl `x xBi xType fun x => do
      let b := xBody.instantiate1 x
      let xId := x.fvarId!

      let (xis, xmk) ← decomposeStructure x

      if xis.size == 1 then
        return none

      -- introduce new free variable for each `xi`
      let decls := (xis.mapIdx fun i xi => (xName.appendAfter (toString i), xBi, fun _ => inferType xi))
      withLocalDecls decls fun xiVars => do

        let xiSet : FVarIdSet := RBTree.fromArray (xiVars.map fun xi => xi.fvarId!) _

        let xVar := (← mkAppM' xmk xiVars).headBeta

        -- replace `x` with new free variables `xiVars`
        let b ← transform b 
          (pre := fun e => 
            match e with
            | .fvar id => pure (.done (if xId == id then xVar else .fvar id)) -- replace
            | e' => pure .continue)
          (post := fun e => do pure (.done (← reduceProjOfCtor e))) -- clean up projections

        let usedXi : FVarIdSet := -- collect which xi's are used
          (← (b.collectFVars.run {})) 
          |>.snd.fvarSet.intersectBy (fun _ _ _ => ()) xiSet 

        let notUsedXi : FVarIdSet := (xiSet.diff usedXi)

        if notUsedXi.size = 0 then
          return none

        let .some (p₁,p₂,_) ← splitStructure (← mkAppM' xmk xiVars).headBeta (fun i xi => usedXi.contains xi.fvarId!)
          | return none

        let xiVars' := xiVars.filter (fun xi => usedXi.contains xi.fvarId!)
        let f' ← mkUncurryFun xiVars'.size (← mkLambdaFVars xiVars' b)

        let rhs := .lam xName xType (f'.app (p₁.app (.bvar 0))) xBi
        let proof ← mkFreshExprMVar (← mkEq f rhs)
        proof.mvarId!.applyRefl -- this should succeed 

        return (f',p₁,p₂,proof)

  | _ => throwError "Error in `factorDomainThroughProjections`, not a lambda function!"


/-- Takes a function `f : X → Y` and finds decomposition `q : Y₁ → Y₂ → Y`, element `y : Y₂` and function `f' : X → Y₁` such that `h : f = fun x => q (f' x) y`

returns `(f', q, y, h)`
-/
def factorCodomainThroughProjections (f : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let f ← instantiateMVars f
  match f with 
  | .lam xName xType xBody xBi => 
    withLocalDecl `x xBi xType fun x => do
      let b := xBody.instantiate1 x
      let xId := x.fvarId!

      let .some (p₁,p₂,q) ← splitStructure b (fun _ bi => bi.containsFVar xId)
        | return none

      let reduceProj : Expr → MetaM Expr := fun e => 
        transform e (post := fun x => do pure (.done (← reduceProjOfCtor x)))
      let y ← reduceProj (← mkAppM' p₂ #[b]).headBeta
      let f' ← mkLambdaFVars #[x] (← reduceProj (← mkAppM' p₁ #[b]).headBeta)

      let rhs := .lam xName xType ((q.app (f'.app (.bvar 0))).app y) xBi
      let proof ← mkFreshExprMVar (← mkEq f rhs)
      proof.mvarId!.applyRefl

      return (f', q, y, proof)

  | _ => throwError "Error in `factorCodomainThroughProjections`, not a lambda function!"
