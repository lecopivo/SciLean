import SciLean.Lean.Expr
import SciLean.Lean.Meta.Basic

namespace SciLean.Meta

set_option linter.unusedVariables false

open Lean Meta Qq

/-- Is it structure containing only plain data i.e. no propositions, no types, no dependent types, no functions
-/
def simpleDataStructure (structName : Name) : MetaM Bool := do

  let ctor := getStructureCtor (← getEnv) structName

  let .some info := getStructureInfo? (← getEnv) structName
    | return false

  for finfo in info.fieldInfo do
    let pinfo ← getConstInfo finfo.projFn
    let stop ← forallTelescope pinfo.type fun xs b => do
      if xs.size ≠ ctor.numParams + 1 then -- functions
        pure true
      else if b.isSort then -- types
        pure true
      else if (← isProp b) then -- proposition
        pure true
      else if (b.containsFVar xs[ctor.numParams]!.fvarId!) then -- dependent types
        pure true
      else
        pure false

    if stop then
      return false

  return true


private def buildMk (mk : Expr) (mks : List Expr) (vars vals : Array Expr) : MetaM Expr :=
  match mks with
  | [] => mkLambdaFVars vars (mkAppN mk vals)
  | mk' :: mks' =>
    lambdaTelescope mk' fun xs b =>
      buildMk mk mks' (vars++xs) (vals.push b)


/-- Decomposes an element `e` of possible nested structure and returns a function put it back together.

For example, calling this function on `x : (Nat×Nat)×Nat` returns `(#[x.1.1, x.1.2, x.1], fun a b c => ((a,b),c))`
-/
partial def splitStructureElem (e : Expr) : MetaM (Array Expr × Expr) := do
  let E ← inferType e
  let idE := .lam `x E (.bvar 0) default

  let .const structName lvls := E.getAppFn'
    | return (#[e], idE)

  let .some info := getStructureInfo? (← getEnv) structName
    | return (#[e], idE)

  if ¬(← simpleDataStructure structName) then
    return (#[e], idE)

  let ctorVal := getStructureCtor (← getEnv) structName

  if E.getAppNumArgs != ctorVal.numParams then
    return (#[e], idE)

  if ctorVal.numFields ≤ 1 then
    return (#[e], idE)

  let eis ← info.fieldNames.mapM (fun fname => do
    let projFn := getProjFnForField? (← getEnv) structName fname |>.get!
    mkAppM projFn #[e] >>= reduceProjOfCtor)

  let (eis,mks) := (← eis.mapM splitStructureElem).unzip

  -- this implementation of combining `mks` together works but it is probably not very efficient
  let mk := mkAppN (.const ctorVal.name lvls) E.getAppArgs
  let mk ← buildMk mk mks.toList #[] #[]

  return (eis.flatten, mk)



/-- Decomposes an element `e` that is a nested application of constructors

For example, calling this function on `x : (Nat×Nat)×Nat` returns `(#[x.1.1, x.1.2, x.1], fun a b c => ((a,b),c))`
-/
partial def splitByCtors (e : Expr) : MetaM (Array Expr × Array Expr × Expr) := do

  let E ← inferType e
  let idE := .lam `x E (.bvar 0) default

  let .const structName lvls := E.getAppFn'
    | return (#[e], #[idE], idE)

  let .some info := getStructureInfo? (← getEnv) structName
    | return (#[e], #[idE], idE)

  let ctorVal := getStructureCtor (← getEnv) structName

  let fn := e.getAppFn
  let args := e.getAppArgs'

  if fn.constName? ≠ .some ctorVal.name then
    return (#[e], #[idE], idE)

  if args.size ≠ ctorVal.numParams + ctorVal.numFields then
    return (#[e], #[idE], idE)

  let mk := mkAppN fn args[0:ctorVal.numParams]

  let fields : Array _ := args[ctorVal.numParams : ctorVal.numParams + ctorVal.numFields]
  let (eis, tmp) := (← fields.mapM splitByCtors).unzip
  let (projs, mks) := tmp.unzip

  let projs := projs
    |>.mapIdx (fun idx projs' =>
       projs'.map (fun proj' => Expr.lam `x E (proj'.app (Expr.proj structName idx (.bvar 0))).headBeta default))
    |>.flatten

  let mk ← buildMk mk mks.toList #[] #[]

  return (eis.flatten, projs, mk)


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
deriving Inhabited

/-- Takes a type `X` of a nested structure  and splits it into two `X₁` and `X₂`. Elements `x` for which `split i x` is true are gatherd in `X₁` and rest is in `X₂`.
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
def decomposeStructure (e : Expr) (split : Nat → Expr → Bool) : MetaM (Option StructureDecomposition) := do
  let ⟨u,X,_⟩ ← inferTypeQ e
  withLocalDecl `x default X fun x => do
    let (xis, xmk) ← splitStructureElem x
    let (eis, _) ← splitStructureElem e

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
      let (xis₁', _) ← splitStructureElem x₁'
      let (xis₂', _) ← splitStructureElem x₂'

      let x' := (← mkAppM' xmk (ids.mergeSplit xis₁' xis₂')).headBeta
      let q : Q($X₁ → $X₂ → $X) ← mkLambdaFVars #[x₁',x₂'] x'

      let proof ← mkFreshExprMVarQ q(IsDecomposition $p₁ $p₂ $q)

      let l ← proof.mvarId!.constructor
      l.forM fun m => do
        let (_,m') ← m.intros
        m'.refl

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

      let (xis, xmk) ← splitStructureElem x

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

        let .some dec ← decomposeStructure (← mkAppM' xmk xiVars).headBeta (fun i xi => usedXi.contains xi.fvarId!)
          | return none

        let xiVars' := xiVars.filter (fun xi => usedXi.contains xi.fvarId!)
        let f' : Q($dec.X₁ → $Y) ← mkUncurryFun xiVars'.size (← mkLambdaFVars xiVars' b)
        let f : Q($dec.X → $Y) := f

        let proof ← mkFreshExprMVarQ q(∀ x, $f' ($dec.p₁ x) = $f x)
        proof.mvarId!.intros >>= fun (_,m) => m.refl

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

      let .some dec ← decomposeStructure b (fun _ bi => bi.containsFVar xId)
        | return none

      let reduceProj : Expr → MetaM Expr := fun e =>
        transform e (post := fun x => do pure (.done (← whnfR x)))
      let y₂ : Q($dec.X₂) ← reduceProj (← mkAppM' dec.p₂ #[b]).headBeta
      let f' : Q($X → $dec.X₁) ← mkLambdaFVars #[x] (← reduceProj (← mkAppM' dec.p₁ #[b]).headBeta)
      let f : Q($X → $dec.X) := f

      let proof ← mkFreshExprMVarQ q(∀ x, $dec.q ($f' x) $y₂ = $f x)
      proof.mvarId!.intros >>= fun (_,m) => m.refl

      return .some {u:=u, X:=X, dec:=dec, f:=f, f':=f', y₂:=y₂, proof:=proof}

  | _ => throwError "Error in `factorCodomainThroughProjections`, not a lambda function!"
