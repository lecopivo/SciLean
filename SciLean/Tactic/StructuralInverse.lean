import SciLean.Lean.Expr
import SciLean.Lean.Meta.Basic

import SciLean.Tactic.LetNormalize
import SciLean.Util.RewriteBy
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
def splitStructure (e : Expr) (split : Nat → Expr → Bool) : MetaM (Option StructureDecomposition) := do
  let ⟨u,X,_⟩ ← inferTypeQ e
  withLocalDecl `x default X fun x => do
    let (xis, xmk) ← decomposeStructure x
    let (eis, _) ← decomposeStructure e

    let (xis₁, xis₂, ids) := xis.splitIdx (fun i _ => split i.1 eis[i.1]!)

    if xis₁.size = 0 || xis₂.size = 0 then
      return none
    
    let x₁ ← mkProdElem xis₁
    let x₂ ← mkProdElem xis₂

    let ⟨v,X₁,x₁⟩ ← inferTypeQ x₁
    let ⟨w,X₂,x₂⟩ ← inferTypeQ x₂

    let p₁ : Q($X → $X₁) ← mkLambdaFVars #[x] x₁
    let p₂ : Q($X → $X₂) ← mkLambdaFVars #[x] x₂

    withLocalDecl `x₁ default X₁ fun x₁' => do
    withLocalDecl `x₂ default X₂ fun x₂' => do
      let (xis₁', _) ← decomposeStructure x₁'
      let (xis₂', _) ← decomposeStructure x₂'

      let x' := (← mkAppM' xmk (ids.mergeSplit xis₁' xis₂')).headBeta
      let q : Q($X₁ → $X₂ → $X) ← mkLambdaFVars #[x₁',x₂'] x'

      let proof ← mkFreshExprMVarQ q(IsDecomposition $p₁ $p₂ $q)

      let l ← proof.mvarId!.constructor
      l.forM fun m => do
        let (_,m') ← m.intros
        m'.applyRefl
      
      return .some {u:=u, v:=v, w:=w, X:=X, X₁:=X₁, X₂:=X₂, p₁:=p₁, p₂:=p₂, q:=q, proof := proof}

/-- Decomposition of the domain of a function `f : X → Y` as `X ≃ X₁×X₂` and provides `f' : X₁ → Y` such that `f = f' ∘ p₁` where `p₁ : X → X₁` is the projection onto the first component.
`
In other words, this claims that `f` does not use the `X₂` part of `X`.
-/
structure DomainDecomposition where
  {u : Level}
  Y : Q(Type u)
  dec : StructureDecomposition 
  f  : Q($dec.X → $Y)
  f' : Q($dec.X₁ → $Y)
  proof : Q(∀ x, $f' ($dec.p₁ x) = $f x)

/-- Take a function `f : X → Y` and find projections `p₁ : X → X₁`, `p₂ : X → X₂` and function `f' : X₁ → Y` such that `h : f = f' ∘ p₁`
-/
def factorDomainThroughProjections (f : Expr) : MetaM (Option DomainDecomposition) := do
  let f ← instantiateMVars f
  match f with 
  | .lam xName xType xBody xBi => 
    withLocalDecl `x xBi xType fun x => do
      let b := xBody.instantiate1 x
      let xId := x.fvarId!

      let ⟨u, Y, _⟩ ← inferTypeQ b

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

        let .some dec ← splitStructure (← mkAppM' xmk xiVars).headBeta (fun i xi => usedXi.contains xi.fvarId!)
          | return none

        let xiVars' := xiVars.filter (fun xi => usedXi.contains xi.fvarId!)
        let f' : Q($dec.X₁ → $Y) ← mkUncurryFun xiVars'.size (← mkLambdaFVars xiVars' b)
        let f : Q($dec.X → $Y) := f

        let proof ← mkFreshExprMVarQ q(∀ x, $f' ($dec.p₁ x) = $f x)
        proof.mvarId!.intros >>= fun (_,m) => m.applyRefl

        return .some {u:= u, Y:=Y, dec:=dec, f:=f, f':=f', proof:=proof}

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
def factorCodomainThroughProjections (f : Expr) : MetaM (Option CodomainDecomposition) := do
  let f ← instantiateMVars f
  match f with 
  | .lam xName xType xBody xBi => 
    withLocalDecl `x xBi xType fun x => do
      let b := xBody.instantiate1 x
      let xId := x.fvarId!

      let ⟨u, X, x⟩ ← inferTypeQ x

      let .some dec ← splitStructure b (fun _ bi => bi.containsFVar xId)
        | return none

      let reduceProj : Expr → MetaM Expr := fun e => 
        transform e (post := fun x => do pure (.done (← whnfR x)))
      let y₂ : Q($dec.X₂) ← reduceProj (← mkAppM' dec.p₂ #[b]).headBeta
      let f' : Q($X → $dec.X₁) ← mkLambdaFVars #[x] (← reduceProj (← mkAppM' dec.p₁ #[b]).headBeta)
      let f : Q($X → $dec.X) := f

      let proof ← mkFreshExprMVarQ q(∀ x, $dec.q ($f' x) $y₂ = $f x)
      proof.mvarId!.intros >>= fun (_,m) => m.applyRefl

      return .some {u:=u, X:=X, dec:=dec, f:=f, f':=f', y₂:=y₂, proof:=proof}

  | _ => throwError "Error in `factorCodomainThroughProjections`, not a lambda function!"


/--
This comparison is used to select the FVarIdSet with the least number of element but non-empty one! Thus zero size sets are bigger then everything else
-/
local instance : Ord (Nat×Expr×FVarIdSet) where
  compare := fun (_,_,x) (_,_,y) =>
    match x.size, y.size with
    | 0, 0 => .eq
    | 0, _ => .gt
    | _, 0 => .lt
    | _, _ => compare x.size y.size


open Qq
structure EquationsInverse where
  {u v : Level}
  {X : Q(Type u)}
  {Y : Q(Type v)}
  (f  : Q($X → $Y))
  (f' : Q($Y → $X))

open Qq
structure EquationsLeftInverse where
  {u v u₁ u₂ : Level}
  {X : Q(Type u)}
  {Y  : Q(Type v)}
  {X₁ : Q(Type u₁)}
  {X₂ : Q(Type u₂)}
  (f  : Q($X → $Y))
  (f' : Q($X₁ → $Y → $X₂))
  (q : Q($X₁ → $X₂ → $X))
  (p₁ : Q($X → $X₁))
  (p₂ : Q($X → $X₂))
  (right_inv : Q(∀ x₁ y, ($f ($q x₁ ($f' x₁ y))) = y))
  (left_inv : Q(∀ x, $f' ($p₁ x) ($f x) = $p₂ x))


/-- Given equations `yᵢ = valᵢ x₁ ...  xₙ`, express `xᵢ` as functions of `yᵢ`, where `xs = #[x₁,...,xₙ]`, `ys = #[y₁,...,yₙ]` are free variables and `vals = #[val₁,...,valₙ]` are value depending on `xs`
-/
partial def invertValues (xs ys : Array Expr) (vals : Array Expr) : MetaM (Option Expr) := do

  let xIdSet : FVarIdSet := .fromArray (xs.map (fun x => x.fvarId!)) _

  let mut vals ← vals.mapIdxM fun i val => do
    let varSet : FVarIdSet := -- collect which xi's are used
      (← (val.collectFVars.run {})) 
      |>.snd.fvarSet.intersectBy (fun _ _ _ => ()) xIdSet
    pure (i.1,val,varSet)

  let .some x ← call vals {} | return none
  
  return x
where

  resolve (lets : Array (Expr × Expr × Expr)) (zs : Array (Expr × Expr)) : MetaM Expr := do

    if zs.size = lets.size then
      let lets := lets.reverse
      let (_, tmp) := lets.unzip
      let (xs', _) := tmp.unzip
      let (pxs, zs') := zs.unzip

      let xIdSet : FVarIdSet := .fromArray (xs.map (fun x => x.fvarId!)) _
      let resolvedIdSet : FVarIdSet := .fromArray (pxs.map (fun x => x.fvarId!)) _
      let unresolvedIdSet := xIdSet.diff resolvedIdSet
      let uxs := unresolvedIdSet.toArray.map Expr.fvar

      if uxs.size = 0 then
        let x := (← mkProdElem xs).replaceFVars pxs zs'
        let x ← mkLambdaFVars (xs' ++ zs') x
        return x
      else
        let x := (← mkProdElem xs).replaceFVars pxs zs'
        let x ← mkLambdaFVars (uxs ++ xs' ++ zs') x
        let x ← mkUncurryFun uxs.size x
        return x

    let i := zs.size 

    let (x,x',val) := lets[i]!

    let (z,z') := zs.unzip
    let val := val.replaceFVars z z'

    withLetDecl ((← x.fvarId!.getUserName).appendAfter "''") (← inferType val) val fun z' => do

      resolve lets (zs.push (x, z'))


  call (vals : Array (Nat×Expr×FVarIdSet)) 
       (lets : Array (Expr × Expr × Expr))  -- #[(fvar xi, new fvar xi' resolving xi, new value of xi)]
    : MetaM (Option Expr) := do

    -- find value that depends only on one variable
    let (i,val,varSet) := vals.minI

    -- not valid value to resolve anymore 
    if varSet.size = 0 then
      return (← resolve lets.reverse #[])
    
    let varArr := varSet.toArray.map Expr.fvar
    let var := varArr[0]!

    -- invert this value
    let x' := 
      if val.isFVar then
        ys[i]!
      else
        ← mkAppM ``Function.invFun #[← mkLambdaFVars #[var] val, ys[i]!]
  
    let x' ← mkLambdaFVars varArr[1:] x'

    withLetDecl ((←var.fvarId!.getUserName).appendAfter "'") (← inferType x') x' fun var' => do

      let val' ← mkAppM' var' varArr[1:]
      -- let val' := var'

      let varSet := varSet.erase var.fvarId!

      -- remove the variable `var` from all the vales
      let mut vals := vals
      for (j,jval,jvarSet) in vals do 
        if j ≠ i then
          if jval.containsFVar var.fvarId! then
            vals := vals.set! j (j, jval.replaceFVar var val', jvarSet.erase var.fvarId! |>.union varSet)
          else
            vals := vals.set! j (j, jval.replaceFVar var val', jvarSet.erase var.fvarId!)
        else
          vals := vals.set! i (i, default, {})

      call vals (lets.push (var, var', val'))


structure SystemInverse where
  lctx : LocalContext
  /-- array of new let fvars -/
  letVars : Array Expr 
  /-- array of xVars that have been succesfully eliminated and replaced by yVars -/
  resolvedXVars : Array Expr 
  /-- array of xVars that have not been succesfully eliminated and still appear in xVals -/
  unresolvedXVars : Array Expr
  xVals : Array Expr


/-- Given equations `yᵢ = valᵢ x₁ ...  xₙ`, express `xᵢ` as functions of `yᵢ`, where `xs = #[x₁,...,xₙ]`, `ys = #[y₁,...,yₙ]` are free variables and `vals = #[val₁,...,valₙ]` are value depending on `xs`
-/
partial def invertValues' (xVars yVars yVals : Array Expr) : MetaM (Option Expr) := do

  let xIdSet : FVarIdSet := .fromArray (xVars.map (fun x => x.fvarId!)) _

  -- data is and array of (yId, value, set of xId aprearing in value)
  let mut eqs ← yVals.mapIdxM fun i val => do
    let varSet : FVarIdSet := -- collect which xi's are used
      (← (val.collectFVars.run {})) 
      |>.snd.fvarSet.intersectBy (fun _ _ _ => ()) xIdSet
    pure (i.1,val,varSet)

  let mut xVars' : Array Expr := #[]
  let mut xVals' : Array Expr := #[]
  
  -- forward pass
  for i in [0:yVals.size] do

    -- find the yVal with the minimal number of xVals in it
    let (j,yVal,varSet) := eqs.minI

    -- not valid value to resolve anymore 
    if varSet.size = 0 then
      throwError "can't invert value {← ppExpr yVal} as it does not depend on any x"

    let varArr := varSet.toArray.map Expr.fvar

    -- pick x we want to resolve, taking the first one might not be the best ides
    let xVar' := varArr[0]!

    -- new value of x but it can still depend on x that have not been resolved
    let xVal' := 
      if yVal.isFVar then
        yVars[j]!
      else
        ← mkAppM ``Function.invFun #[← mkLambdaFVars #[xVar'] yVal, yVars[j]!]

    xVars' := xVars'.push xVar'
    xVals' := xVals'.push xVal'

    let varSet := varSet.erase xVar'.fvarId!

    -- remove the variable `var` from all the vales
    for (k,kval,kvarSet) in eqs do 
      if j ≠ k then
        if kval.containsFVar xVar'.fvarId! then
          eqs := eqs.set! k (k, kval.replaceFVar xVar' xVal', kvarSet.erase xVar'.fvarId! |>.union varSet)
        else
          eqs := eqs.set! k (k, kval.replaceFVar xVar' xVal', kvarSet.erase xVar'.fvarId!)
      else
        eqs := eqs.set! j (j, default, {})

  let mut lctx ← getLCtx
  let  instances ← getLocalInstances

  xVars' := xVars'.reverse
  xVals' := xVals'.reverse

  let mut zVars : Array Expr := #[]

  for i in [0:xVars'.size] do

    let xVar' := xVars'[i]!
    let xVal' := xVals'[i]!
    let xId := xVar'.fvarId!
    
    let zId ← withLCtx lctx instances mkFreshFVarId
    let zVar := Expr.fvar zId
    let zVal := xVal'.replaceFVars xVars' zVars
    zVars := zVars.push zVar

    lctx := lctx.mkLetDecl zId (← xId.getUserName) (← xId.getType) zVal
    
    pure ()

  let xVals := xVars.map (fun xVar => xVar.replaceFVars xVars' zVars)
  return none


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

      -- can't have more equations then unknowns
      -- such system is overdetermined
      if xis.size < yis.size then
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
          let i₁ := lets[0]!
          let lets := lets[1:]
          let (xs', _) ← decomposeStructure xs'
          let f' ← mkLambdaFVars (#[i₁,y] ++ lets) (← mkAppM' xmk xs').headBeta 
          let f' ← Meta.LetNormalize.letNormalize f' {removeLambdaLet:=false}
          return f'
  | _ => throwError "Error in `invertFunction`, not a lambda function!"



#eval show MetaM Unit from do

  let e := q(fun ((x,y,z) : Int × Int × Int) => (x+y+z))

  let .some f ← invertFunction e
    | return ()
  IO.println s!"inverse of {← ppExpr f}"

def swap (xy : Int×Int) : Int × Int := (xy.2, xy.1)

#eval show MetaM Unit from do

  let e := q(fun (xyz : Int × Int × Int) => (xyz.1+2 + xyz.2.1 + xyz.2.2, swap xyz.2))

  let .some f ← invertFunction e
    | return ()
  IO.println s!"inverse of {← ppExpr f}"
      
      
open Qq in
#eval show MetaM Unit from do

  let e := q(fun (x y z : Nat) => (x + z, x + y + z, y))

  lambdaTelescope e fun xs b => do

    let (bs, _) ← decomposeStructure b

    let decls := bs.mapIdx (fun i bi => (Name.appendAfter `y (toString i), default, fun _ => inferType bi))

    withLocalDecls decls fun ys => do

      let (vals, _) ← decomposeStructure b

      let .some x ← invertValues xs ys vals
        | return ()
      IO.println (← ppExpr x)



#eval show MetaM Unit from do

  let e := q(fun xy : Int × Int × Int × Int => ((xy.snd.snd.snd, 2 * xy.fst), 3*xy.snd.fst))
  let .some ff ← factorDomainThroughProjections e
    | return ()
  IO.println (← ppExpr e)
  IO.println (← ppExpr ff.f')
  IO.println (← ppExpr ff.dec.p₁)
  IO.println (← ppExpr ff.dec.p₂)



#eval show MetaM Unit from do

  let e := q(fun ((x,y) : Int × Int) => (x, y, 1, 3))
  let .some ff ← factorCodomainThroughProjections e
    | return ()
  IO.println (← ppExpr e)
  IO.println (← ppExpr ff.f')
  IO.println (← ppExpr ff.dec.q)
  IO.println (← ppExpr ff.y₂)



#eval show MetaM Unit from do

  let e := q(fun xy : Int × Int => (xy.snd, 1))
  let .some ff ← factorCodomainThroughProjections e
    | return ()
  IO.println (← ppExpr e)
  IO.println (← ppExpr ff.f')
  IO.println (← ppExpr ff.dec.q)
  IO.println (← ppExpr ff.y₂)

  let .some ff ← factorDomainThroughProjections ff.f'
    | return ()
  IO.println (← ppExpr ff.f')
  IO.println (← ppExpr ff.dec.p₁)
  IO.println (← ppExpr ff.dec.p₂)


#eval show MetaM Unit from do

  let e := q(fun xy : Int × Int => let a := 2 * xy.1; let b := 2 + xy.1; a + b)

  let .some ff ← factorDomainThroughProjections e
    | return ()
  IO.println (← ppExpr ff.f')
  IO.println (← ppExpr ff.dec.p₁)
  IO.println (← ppExpr ff.dec.p₂)



example : 
  ∀ (x : Int × Int × Int × Int),
    ((x.fst, x.snd.fst, x.snd.snd.snd).fst, (x.fst, x.snd.fst, x.snd.snd.snd).snd.fst, x.snd.snd.fst,
      (x.fst, x.snd.fst, x.snd.snd.snd).snd.snd) = x
  :=
by
  intro x; rfl


#eval show MetaM Unit from do

  let e := q(fun x y z : Int => (y+2 + x + z, x*2 + y*2 + z, x + y + z))

  lambdaTelescope e fun xs b => do
    let (bs,_) ← decomposeStructure b

    let decls := bs.mapIdx fun i bi => 
      (Name.appendAfter `y (toString i),
       default,
       fun _ => inferType bi)

    withLocalDecls decls fun ys => do

      let .some zs ← invertValues xs ys bs
        | throwError "failed"
      
      IO.println (← ppExpr zs)

      pure ()



syntax (name := invert_fun_conv) "invert_fun" : conv

open Lean Elab Tactic Conv in
@[tactic invert_fun_conv] 
def convInvertFun : Tactic
| `(conv| invert_fun) => do
  (← getMainGoal).withContext do

    let lhs ← getLhs

    let .some lhs' ← invertFunction lhs
      | return ()

    updateLhs lhs' (← mkSorry (← mkEq lhs lhs') false)

| _ => Lean.Elab.throwUnsupportedSyntax



example 
  : (fun ((x,y,z) : Float × Float × Float) => (y+2 + x + z, x*2 + y*2 + z, x+y+z))
    =
    fun x => x :=
by
  conv => 
    lhs
    invert_fun
  sorry
