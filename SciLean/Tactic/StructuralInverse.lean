import SciLean.Lean.Expr
import SciLean.Lean.Meta.Basic

import Mathlib.Logic.Function.Basic

namespace SciLean

set_option linter.unusedVariables false

open Lean Meta Qq

/-- Decomposes an element `e` of possible nested structure and returns a function put it back together.

For example, calling this function on `x : (Nat×Nat)×Nat` returns `(#[x.1.1, x.1.2, x.1], fun a b c => ((a,b),c))`
-/
partial def decomposeStructure (e : Expr) : MetaM (Array Expr × Expr) := do
  let E ← inferType e
  let idE := .lam `x E (.bvar 0) default

  let .const structName lvls := E.getAppFn'
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

structure IsDecomposition (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) : Prop where
  proj_mk  : ∀ x, q (p₁ x) (p₂ x) = x
  mk_proj₁ : ∀ x₁ x₂, p₁ (q x₁ x₂) = x₁
  mk_proj₂ : ∀ x₁ x₂, p₂ (q x₁ x₂) = x₂

structure StructureDecomposition where
  {u v w : Level}
  X  : Q(Type u)
  X₁ : Q(Type v)
  X₂ : Q(Type w)
  p₁ : Q($X → $X₁)
  p₂ : Q($X → $X₂)
  q  : Q($X₁ → $X₂ → $X)
  proof : Q(IsDecomposition $p₁ $p₂ $q)


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


structure DomainDecomposition where
  {u : Level}
  Y : Q(Type u)
  dec : StructureDecomposition 
  f  : Q($dec.X → $Y)
  f' : Q($dec.X₁ → $Y)
  proof : Q(∀ x, $f' ($dec.p₁ x) = $f x) -- proof of `∀ x, f' (domDec.p₁ x) = f x`

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

structure CodomainDecomposition where
  {u : Level}
  X : Q(Type u)
  dec : StructureDecomposition 
  f  : Q($X → $dec.X)
  f' : Q($X → $dec.X₁)
  y₂ : Q($dec.X₂)
  proof : Q(∀ x, ($dec.q ($f' x) $y₂) = $f x)

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



/-- Given equations `yᵢ = val x₁ ... xₙ`, express `xᵢ` as functions of `yᵢ`, where `xs = #[x₁,...,xₙ]`, `ys = #[y₁,...,yₙ]` are free variables and `vals = #[val₁,...,valₙ]` are value depending on `xs`

The system of equations has to be of triangular nature, i.e. there is one equation that depends only one one `xᵢ`, next equation can depend only on two `xᵢ`, and so on.
-/
partial def invertValues (xs ys : Array Expr) (vals : Array Expr) : MetaM (Option Expr) := do

  let xIdSet : FVarIdSet := .fromArray (xs.map (fun x => x.fvarId!)) _

  let mut vals ← vals.mapIdxM fun i val => do
    let varSet : FVarIdSet := -- collect which xi's are used
      (← (val.collectFVars.run {})) 
      |>.snd.fvarSet.intersectBy (fun _ _ _ => ()) xIdSet
    pure (i.1,val,varSet)

  let .some x ← call vals {} | return none
  
  return x[0]!.1
where
  call (vals : Array (Nat×Expr×FVarIdSet)) (lets : Array (Expr × Expr)) : MetaM (Option (Array (Expr × Expr))) := do

    if (lets.size = xs.size) then
      let (pxs, xs') := lets.unzip
      let x := (← mkProdElem xs).replaceFVars pxs xs'
      let x ← mkLambdaFVars xs' x
      return .some #[(x,default)]

    -- find value that depends only on one variable
    let .some (i,val,varSet) := vals.find? (fun (_,_,varSet) => varSet.size == 1)
      | -- probably turn this into a trace and return none
        throwError "can't find a value to resolve w.r.t. one of the variables {← xs.mapM ppExpr} \nvalues: \n {← (vals.filterMap (fun (_,val,set) => if set.size > 0 then val else none) |>.mapM ppExpr)})"
        -- return none

    let varId := varSet.toArray[0]!
    let var := .fvar varId

    -- invert this value
    let x' := 
      if val.isFVar then
        ys[i]!
      else
        ← mkAppM ``Function.invFun #[← mkLambdaFVars #[var] val, ys[i]!]

    withLetDecl ((←varId.getUserName).appendAfter "'") (←varId.getType) x' fun var' => do

      -- remove the variable `var` from all the vales
      let mut vals := vals
      for (j,jval,jvarSet) in vals do 
        if j ≠ i then
          vals := vals.set! j (j, jval.replaceFVar var var', jvarSet.erase var.fvarId!)
        else
          vals := vals.set! i (i, default, {})

      call vals (lets.push (var, var'))



/-- 
-/
def invertFunction (f : Expr) : MetaM (Option Expr) := do
  let f ← instantiateMVars f
  match f with 
  | .lam xName xType xBody xBi => 
    withLocalDecl `x xBi xType fun x => do
      let b := xBody.instantiate1 x
      let xId := x.fvarId!
      let yType ← inferType b
      withLocalDecl `y xBi yType fun y => do
      
      let (xis, xmk) ← decomposeStructure x
      let (yis, ymk) ← decomposeStructure y

      if xis.size == 1 then
        return none

      -- introduce new free variable for each `xi`
      let decls := (xis.mapIdx fun i xi => (xName.appendAfter (toString i), xBi, fun _ => inferType xi))
      withLocalDecls decls fun xiVars => do

        let xVar := (← mkAppM' xmk xiVars).headBeta

        -- replace `x` with new free variables `xiVars`
        let b ← transform b 
          (pre := fun e => 
            match e with
            | .fvar id => pure (.done (if xId == id then xVar else .fvar id)) -- replace
            | e' => pure .continue)
          (post := fun e => do pure (.done (← whnfR e))) -- clean up projections

        let (bs,_) ← decomposeStructure b

        let .some b' ← invertValues xiVars yis bs
          | return none

        lambdaLetTelescope b' fun lets xs' => do
          let (xs', _) ← decomposeStructure xs'
          mkLambdaFVars (#[y] ++ lets) (← mkAppM' xmk xs').headBeta
  | _ => throwError "asdf"



#eval show MetaM Unit from do

  -- let e := q(fun x : Int × Int × Int => (x.snd.fst+2 + x.fst, x.fst*2, x.1 + x.2.1 + x.2.2))
  let e := q(fun ((x,y,z) : Int × Int × Int) => (y+2 + x, x*2, x + y + z))

  let .some f ← invertFunction e
    | return ()
  IO.println s!"inverse of {← ppExpr f}"
      
      
open Qq in
#eval show MetaM Unit from do

  let e := q(fun (x y : Nat) => (x + y, y))

  lambdaTelescope e fun xs b => do

    let (bs, _) ← decomposeStructure b

    let decls := bs.mapIdx (fun i bi => (Name.appendAfter `y (toString i),default,fun _ => inferType bi))

    withLocalDecls decls fun ys => do

      let (vals, _) ← decomposeStructure b

      let .some x ← invertValues xs ys vals
        | return ()
      IO.println (← ppExpr x)



#eval show MetaM Unit from do

  let e := q(fun xy : Int × Int × Int × Int => ((xy.snd.snd.snd, 2 * xy.fst), 3*xy.snd.fst))
  let .some (f',p₁,p₂,h) ← factorDomainThroughProjections e
    | return ()
  IO.println (← ppExpr e)
  IO.println (← ppExpr f')
  IO.println (← ppExpr p₁)
  IO.println (← ppExpr p₂)



#eval show MetaM Unit from do

  let e := q(fun xy : Int × Int => (xy.fst, xy.snd, 1, 3))
  let .some (f',q,y,h) ← factorCodomainThroughProjections e
    | return ()
  IO.println (← ppExpr e)
  IO.println (← ppExpr f')
  IO.println (← ppExpr q)
  IO.println (← ppExpr y)



#eval show MetaM Unit from do

  let e := q(fun xy : Int × Int => (xy.snd, 1))
  let .some (f',q,y,h) ← factorCodomainThroughProjections e
    | return ()
  IO.println (← ppExpr e)
  IO.println (← ppExpr f')
  IO.println (← ppExpr q)
  IO.println (← ppExpr y)

  let .some (f'',p₁,p₂,h) ← factorDomainThroughProjections f'
    | return ()
  IO.println (← ppExpr f'')
  IO.println (← ppExpr p₁)
  IO.println (← ppExpr p₂)



