import SciLean

open SciLean

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
split Q((Nat×Int)×(Nat×Int)×Float) (fun i => i%2==0)
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



/-- Result for computin structural inverse of a function

For function `f : X → Y`

1. `.bijection g` holds inverse `g : Y → X`
2. `.surjection g f'` holds inverse `g : Y×Y'→X` to `(fun x => (f x, f' x)) : X→Y×Y'`
3. `.surjectionRestriction p q f' g` holds inverse `g : Y→X₁` to `f'` such that `f = fun x => (p (f' x)).1` and `p : X → X₁×X₂` `q : X₁ → X₂ → X` inverse of each other

-- 3. `.injection g f'` hold inverse `g : Y' → X` and to `p ∘ f`
-/
inductive StructuralInverseResult where
  | bijection  (g : Expr)
  | surjection (g f' : Expr)
deriving Inhabited

def StructuralInverseResult.invFun : StructuralInverseResult → Expr
  | .bijection g => g
  | .surjection g _ => g

def StructuralInverseResult.funCompl : StructuralInverseResult → Expr
  | .bijection _ => default
  | .surjection _ f' => f'


def structuralInverse (e : Expr) : MetaM StructuralInverseResult := do
  let e ← instantiateMVars e
  match e with
  | .lam xName xType xBody xBi =>
    withLocalDecl `x xBi xType fun x => do
      let b := xBody.instantiate1 x
      let xId := x.fvarId!
      let yType ← inferType b
      withLocalDecl `y xBi yType fun y => do

        let (xis, xmk) ← decomposeStructure x
        let (yjs, ymk) ← decomposeStructure y

        -- introduce new free variable for each `xi`
        let decls := (xis.mapIdx fun i xi => (xName.appendAfter (toString i),xBi, fun _ => inferType xi))
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

            let (bjs, _) ← decomposeStructure b

            let mut bjxSet : Array FVarIdSet := #[] -- set of x fvars used in j-th equation
            for j in [0:bjs.size] do
              let bj := bjs[j]!
              let bjFVars : FVarIdSet := -- collect which xi's
                (← (bj.collectFVars.run {}))
                |>.snd.fvarSet.intersectBy (fun _ _ _ => ()) xiSet
              bjxSet := bjxSet.push bjFVars
              if bjFVars.size ≠ 1 then
                throwError "can't invert as the expression {← ppExpr bj} depends on multiple components of the input {← (bjFVars.toArray.map (.fvar)).mapM ppExpr}"

            let usedXi : FVarIdSet := bjxSet.foldl (init:={}) (fun x y => x.mergeBy (fun _ _ _ => ()) y)
            let notUsedXi : FVarIdSet := (xiSet.diff usedXi)

            if notUsedXi.size ≠ 0 then
              let .some (p₁,p₂,q) ← splitStructure (← mkAppM' xmk xiVars).headBeta (fun i xi => usedXi.contains xi.fvarId!)
                | throwError "asdfeawfe"

              let xiVars' := xiVars.filter (fun xi => usedXi.contains xi.fvarId!)

              let yType ← inferType b
              withLocalDecl `y default yType fun y => do
                let (yjs, ymk) ← decomposeStructure y

                let f' ← mkUncurryFun xiVars'.size (← mkLambdaFVars xiVars' (← mkAppM' ymk bjs).headBeta)

                let mut gjs : Array (Name × Expr) := #[]
                for j in [0:bjs.size] do
                  let bj := bjs[j]!
                  let xi := Expr.fvar bjxSet[j]!.toArray[0]!
                  let gj ←
                    if bj.isFVar then
                      pure yjs[j]!
                    else
                      mkAppM ``Function.invFun #[← mkLambdaFVars #[xi] bj, yjs[j]!]
                  gjs := gjs.push (xi.fvarId!.name, gj)

                -- !!!WARNING: this step is assuming that lambdaTelescope creates free variables with ascending fvarId!!!
                gjs := gjs.qsort (fun (n,_) (n',_) => (Name.quickCmp n n').isLT)

                let g ← mkLambdaFVars #[y] (← mkProdElem gjs.unzip.2)

                IO.println (← ppExpr f')
                IO.println (← ppExpr g)
                IO.println (← ppExpr (← whnf (← mkAppM ``Function.comp #[f', g])))

            -- record occurencse of `xi` in `bj`
            let mut itoj : Array (Nat×Nat) := #[]
            for i in [0:xiVars.size] do
              for j in [0:bjs.size] do
                if bjs[j]!.containsFVar xiVars[i]!.fvarId! then
                  itoj := itoj.push (i,j)

            -- ordered by j's
            let itoj' := itoj.qsort (fun (_,j) (_,j') => j < j')

            -- 'missing_is' lists unused components of the input
            let missing_is : Array Nat ← do
              -- this block assumes that `itoj` has i's in increasing order
              let mut missing_is := #[]
              let mut i := 0
              for (i',j') in itoj do
                if i > i' then
                  throwError "can't invert as the expression {← ppExpr xis[i']!} occures multiple times in {← ppExpr b}"
                else if i = i' then
                  i := i + 1
                  continue
                else
                  for i'' in [i:i'] do
                    missing_is := missing_is.push i''
                  i := i' + 1
                  continue
              for i'' in [i:xis.size] do
                missing_is := missing_is.push i''

              pure missing_is

            -- `missing_js` lists components of the output that do not depend on the input
            let missing_js : Array Nat ← do
              -- this block assumes that `itoj'` has j's in increasing order
              let mut missing_js : Array Nat := #[]
              let mut j := 0
              for (i',j') in itoj' do
                if j > j' then
                  throwError "can't invert as the expression {← ppExpr bjs[j']!} depends on multiple components of the input"
                else if j = j' then
                  j := j + 1
                  continue
                else
                  for j'' in [j:j'] do
                    missing_js := missing_js.push j''
                  j := j' + 1
                  continue
              for j'' in [j:bjs.size] do
                missing_js := missing_js.push j''
              pure missing_js

            if missing_is.size != 0 && missing_js.size != 0 then
              throwError "function can't be inverted"

            if missing_js.size != 0 then
              throwError "function is injection, not implemented yet"

            -- surjection
            if missing_is.size != 0 then do
              let bjs' := missing_is.map (fun i => xiVars[i]!)
              let bjs := bjs.append bjs'
              let itoj'' := itoj.append (missing_is.mapIdx (fun idx i => (i, yjs.size+idx)))
              let yyType ← inferType (← mkProdElem #[y, ← mkProdElem bjs'])
              return ← withLocalDecl `y xBi yyType fun yy' => do

                let (yjs, _) ← decomposeStructure yy'

                let xis' ← itoj''.mapM (fun (i,j) => do
                  let bj := bjs[j]!
                  if bj.isFVar then
                    pure yjs[j]!
                  else
                    let gj ← mkLambdaFVars #[xiVars[i]!] bj
                    mkAppM ``Function.invFun #[gj, yjs[j]!])

                let invf ← mkLambdaFVars #[yy'] (← mkAppM' xmk xis').headBeta

                let f' ← mkLambdaFVars #[x] (← mkProdElem (missing_is.map (fun i => xis[i]!)))
                return .surjection invf f'


            -- bijection
            if missing_is.size == 0 then
              let xis' ← itoj.mapM (fun (i,j) => do
                let bj := bjs[j]!
                if bj.isFVar then
                  pure yjs[j]!
                else
                  let gj ← mkLambdaFVars #[xiVars[i]!] bj
                  mkAppM ``Function.invFun #[gj, yjs[j]!])

              let invf ← mkLambdaFVars #[y] (← mkAppM' xmk xis').headBeta
              return .bijection invf

            unreachable!

  | _ => throwError "Error in `structuralInverse`, not a lambda function!"



#eval show MetaM Unit from do
  let e := q(fun xy : Int × Int => (xy.fst, xy.snd))
  let f' ← structuralInverse e
  IO.println s!"inverse of \n{←ppExpr e}\nis\n{← ppExpr f'.invFun}"


#eval show MetaM Unit from do
  let e := q(fun xy : Int × Int => (xy.snd, xy.fst))
  let f' ← structuralInverse e
  IO.println s!"inverse of \n{←ppExpr e}\nis\n{← ppExpr f'.invFun}"


#eval show MetaM Unit from do

  let e := q(fun xy : Int × Int => (xy.snd+2, xy.fst*2))
  let f' ← structuralInverse e
  IO.println s!"inverse of \n{←ppExpr e}\nis\n{← ppExpr f'.invFun}"

  IO.println s!""

  let e := q(fun x : Int × (Int × Int) × Int => ((1 * x.1, 2 * x.2.1.1), (3 * x.2.1.2, 4 * x.2.2)))
  let f' ← structuralInverse e
  IO.println s!"inverse of \n{←ppExpr e}\nis\n{← ppExpr f'.invFun}"

  IO.println s!""

  let e := q(fun x : (Int × Int) × (Int × Int) => ((1 * x.1.1, 2 * x.2.1), (3 * x.1.2, 4 * x.2.2)))
  let f' ← structuralInverse e
  IO.println s!"inverse of \n{←ppExpr e}\nis\n{← ppExpr f'.invFun}"



#eval show MetaM Unit from do

  let e := q(fun xy : Int × Int => (xy.fst+2, xy.snd*2))
  let f' ← structuralInverse e
  IO.println s!"inverse of \n{←ppExpr e}\nis\n{← ppExpr f'.invFun}"



#eval show MetaM Unit from do

  let e := q(fun xy : Int × Int => (xy.fst+xy.snd, 2))
  let f' ← structuralInverse e
  IO.println s!"inverse of \n{←ppExpr e}\nis\n{← ppExpr f'.invFun}"



#eval show MetaM Unit from do

  let e := q(fun xy : Int × Int × Int × Int => ((xy.snd.snd.snd, 2 * xy.fst), 3*xy.snd.fst))
  let f' ← structuralInverse e
  IO.println s!"inverse of \n{←ppExpr e}\nis\n{← ppExpr f'.invFun}"
  IO.println s!"surjection complement \n{←ppExpr f'.funCompl}"



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

  let .some (f'',p₁,p₂) ← factorDomainThroughProjections f'
    | return ()
  IO.println (← ppExpr f'')
  IO.println (← ppExpr p₁)
  IO.println (← ppExpr p₂)




-- X → Y

-- X ≃ X₁×X₂

-- X₁×X₂ → Y, p₁ : X → X₁, p₂ : X → X₂, g : Y → X₁

-- ∑ ij, x[ij.1] * y[ij] = ∑ i, x[i] ∑ j,
