import SciLean.Tactic.StructureDecomposition
import SciLean.Tactic.LetNormalize
import SciLean.Data.Function

namespace SciLean.Meta

set_option linter.unusedVariables false

open Lean Meta Qq

initialize registerTraceClass `Meta.Tactic.structuralInverse.step

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


private structure SystemInverse where
  /-- context holding additional let fvars that have been introduced during solving -/
  lctx : LocalContext
  /-- array of new let fvars -/
  letVars : Array Expr
  /-- array of xVars that have been succesfully eliminated and replaced by yVals -/
  resolvedXVars : Array Expr
  /-- array of xVars that have not been succesfully eliminated and still appear in xVals -/
  unresolvedXVars : Array Expr
  /-- values of xVars in terms of yVals and potentialy few xVars that have not been eliminated -/
  xVals : Array Expr


private def equationsToString (yVals fVals : Array Expr) : MetaM String :=
  yVals.zip fVals
    |>.joinlM (fun (y,val) => do pure s!"{← ppExpr y} = {← ppExpr val}")
              (fun s s' => pure (s ++ "\n" ++ s'))


private def partiallyResolvedSystemToString
  (lctx : LocalContext) (xResVars' yVals : Array Expr)
  (eqs : Array (Nat × Expr × FVarIdSet)) : MetaM String := do
  withLCtx lctx (← getLocalInstances) do
    let lets ← xResVars'.joinlM (fun var => do pure s!"let {← var.fvarId!.getUserName} := {← ppExpr (← var.fvarId!.getValue?).get!}")
                                 (fun s s' => pure (s ++ "\n" ++ s'))
    let (yVals', fVals') := eqs.filterMap (fun (i,val,idset) => if idset.size = 0 then none else .some (yVals[i]!, val))
         |>.unzip
    pure s!"{lets}\n{← equationsToString yVals' fVals'}"

private def afterBackwardPassSystemToString
  (lctx : LocalContext) (xResVars' xVars'' xVars xVals : Array Expr) := do
  withLCtx lctx (← getLocalInstances) do
    let lets ← (xResVars' ++ xVars'').joinlM (fun var => do pure s!"let {← var.fvarId!.getUserName} := {← ppExpr (← var.fvarId!.getValue?).get!}")
                                 (fun s s' => pure (s ++ "\n" ++ s'))
    pure s!"{lets}\n{← equationsToString xVars xVals}"


/--
Solves the system of m-equations in n-variables
```
y₁ = f₁ x₁ ... xₙ
...
yₘ = fₘ x₁ ... xₙ
```

Returns values of `xᵢ` in terms of `yⱼ`.

If `n>m` then the values `xᵢ` can depend also on other `xₖ`. The set `n-m` xs
-/
private partial def invertValues (xVars yVals fVals : Array Expr) : MetaM (Option (SystemInverse × Array MVarId)) := do

  trace[Meta.Tactic.structuralInverse.step] "inverting system in variables {← xVars.mapM ppExpr}\n{← equationsToString yVals fVals}"

  let xIdSet : FVarIdSet := .fromArray (xVars.map (fun x => x.fvarId!)) _

  -- data is and array of (yId, value, set of xId aprearing in value)
  let mut eqs ← fVals.mapIdxM fun i val => do
    let varSet : FVarIdSet := -- collect which xi's are used
      (← (val.collectFVars.run {}))
      |>.snd.fvarSet.intersectBy (fun _ _ _ => ()) xIdSet
    pure (i,val,varSet)

  let mut lctx ← getLCtx
  let  instances ← getLocalInstances

  let mut xVars' : Array Expr := #[]
  let mut xVals' : Array Expr := #[]
  let mut xResVars' : Array Expr := #[]
  let mut goals : Array MVarId := #[]

  -- forward pass
  for i in [0:fVals.size] do

    -- find the yVal with the minimal number of xVals in it
    let (j,yVal,varSet) := eqs.minI

    let yType ← inferType yVal

    -- we can't invert if equation does not depen't on any x
    if varSet.size = 0 then
      return none

    let varArr := varSet.toArray.map Expr.fvar
    -- pick x we want to resolve, taking the first one might not be the best ides
    let .some xVarId ← varArr.findIdxM? fun var => do pure (← isDefEq yType (← inferType var))
      | return none
    let xVar' := varArr[xVarId]!
    let varArrOther := varArr.eraseIdx! xVarId

    trace[Meta.Tactic.structuralInverse.step]
      "resolving {xVar'} from {yVals[j]!} = {← withLCtx lctx instances <| ppExpr yVal}"

    let xName ← xVar'.fvarId!.getUserName

    -- new value of x but it can still depend on x that have not been resolved
    let (xVal',goal?) ←
      if yVal.isFVar then
        pure (yVals[j]!, none)
      else
        withLCtx lctx instances <| do
        let g ← mkLambdaFVars #[xVar'] yVal
        let hg ← mkAppM ``Function.Bijective #[g]
        let goal := (← mkFreshExprMVar hg).mvarId!
        let f ← mkAppM ``Function.invFun #[← mkLambdaFVars #[xVar'] yVal, yVals[j]!]
        pure (f, .some goal)

    if let .some goal := goal? then
      trace[Meta.Tactic.structuralInverse.step] "new obligation {← withLCtx lctx instances <| ppExpr (← goal.getType)}"
      goals := goals.push goal

    trace[Meta.Tactic.structuralInverse.step] "resolved {← ppExpr xVar'} with {← withLCtx lctx instances <| ppExpr xVal'}"

    -- xRes is a function resolving x given all unresolved xs
    let xResId ← withLCtx lctx instances <| mkFreshFVarId
    let xResVar := Expr.fvar xResId
    let xResVal ← withLCtx lctx instances <|
      mkLambdaFVars varArrOther xVal'
    let xResType ← withLCtx lctx instances <|
      inferType xResVal
    lctx := lctx.mkLetDecl xResId (xName.appendAfter "'") xResType xResVal

    let xVal'' := mkAppN xResVar varArrOther

    xVars' := xVars'.push xVar'
    xVals' := xVals'.push xVal''
    xResVars' := xResVars'.push xResVar

    let varSet := varSet.erase xVar'.fvarId!

    -- remove the variable `var` from all the other equations
    eqs := eqs.map fun (k,kval,kvarSet) =>
      if j ≠ k then
        if kval.containsFVar xVar'.fvarId! then
          (k, kval.replaceFVar xVar' xVal'', kvarSet.erase xVar'.fvarId! |>.union varSet)
        else
          (k, kval.replaceFVar xVar' xVal'', kvarSet.erase xVar'.fvarId!)
      else
        (j, default, {})

    let (yVals',fVals') :=
      eqs.filterMap (fun (i,val,idset) => if idset.size = 0 then none else .some (yVals[i]!, val))
         |>.unzip
    trace[Meta.Tactic.structuralInverse.step] "system after resolving {← ppExpr xVar'}\n{← partiallyResolvedSystemToString lctx xResVars' yVals eqs}"


  let mut xVars'' : Array Expr := #[]

  -- backward pass
  xVars' := xVars'.reverse
  xVals' := xVals'.reverse
  for i in [0:xVars'.size] do

    let xVar' := xVars'[i]!
    let xVal' := xVals'[i]!
    let xId := xVar'.fvarId!

    let xId'' ← withLCtx lctx instances mkFreshFVarId
    let xVar'' := Expr.fvar xId''
    let xVal'' := xVal'.replaceFVars xVars'[0:i] xVars''
    xVars'' := xVars''.push xVar''

    lctx := lctx.mkLetDecl xId'' ((← xId.getUserName).appendAfter "''") (← xId.getType) xVal''

  let xVals := xVars.map (fun xVar => xVar.replaceFVars xVars' xVars'')

  trace[Meta.Tactic.structuralInverse.step] "system after backward pass\n{← afterBackwardPassSystemToString lctx xResVars' xVars'' xVars xVals}"

  let resolvedIdSet : FVarIdSet := .fromArray (xVars'.map (fun x => x.fvarId!)) _
  let unresolvedIdSet := xIdSet.diff resolvedIdSet

  let sinv : SystemInverse := {
    lctx := lctx
    letVars := xResVars' ++ xVars''
    resolvedXVars := resolvedIdSet.toArray.map .fvar
    unresolvedXVars := unresolvedIdSet.toArray.map .fvar
    xVals := xVals
  }

  return .some (sinv, goals)

open Qq
structure FullInverse where
  {u v : Level}
  {X : Q(Type u)}
  {Y : Q(Type v)}
  (f  : Q($X → $Y))
  (invFun : Q($Y → $X))
  (is_inv : Q(Function.Inverse $invFun $f))

open Qq
/--
  Holds right inverse to the function `f : X → Y`.

  Further more it provides decomposition `X ≃ X₁×X₂` such that `f` restricted to only `X₂` is fully invertible.
-/
structure RightInverse where
  {v : Level}
  {decX : StructureDecomposition}
  {Y  : Q(Type v)}
  (f  : Q($decX.X → $Y))
  (invFun : Q($decX.X₁ → $Y → $decX.X))
  (right_inv : Q(∀ x₁, Function.RightInverse ($invFun x₁) $f))
  (left_inv  : Q(∀ x₁, Function.LeftInverse (fun y => $decX.p₂ ($invFun x₁ y)) (fun x₂ => $f ($decX.q x₁ x₂))))

inductive FunctionInverse where
  | full (inv : FullInverse)
  | right (inv : RightInverse)

/-- Compute inverse of a function `f : X → Y` where both `X` and `Y` are possible nested strustures

For example
```
fun (x,(y,z)) => ((x+y, x), z)
==>
fun ((x',y'),z') => (y', (x' - y', z'))
```

It can also compute right inverses
```
fun (x,y,z) => x+y+z)
==>
fun (y,z) x' => (x'-y-z, y, z)
```
the right inverse `f⁻¹` is parametrized by a type `X₁` and for every `x₁ : X₁` the `f⁻¹ x₁` is right inverse of `f`

Returns also a list of pending goals proving that individual inversions are possible.
-/
def structuralInverse (f : Expr) : MetaM (Option (FunctionInverse × Array MVarId)) := do
  let f ← whnfCore (← instantiateMVars f)
  match f with
  | .lam xName xType xBody xBi =>
    withLocalDecl `x xBi xType fun x => do

      let b := xBody.instantiate1 x
      let xId := x.fvarId!
      let yType ← inferType b
      withLocalDecl `y xBi yType fun y => do

      let (xis, xmk) ← splitStructureElem x
      let (yis, ymk) ← splitStructureElem y

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

        let (bs,_) ← splitStructureElem b

        let .some (eqInv,goals) ← invertValues xiVars yis bs
          | return none

        withLCtx eqInv.lctx (← getLocalInstances) do

          let ⟨u,X,_⟩ ← inferTypeQ x
          let ⟨v,Y,_⟩ ← inferTypeQ y
          let f : Q($X → $Y) := f
          let b := (← mkAppM' xmk eqInv.xVals).headBeta

          if eqInv.unresolvedXVars.size = 0 then
            let invFun : Q($Y → $X) ← mkLambdaFVars (#[y] ++ eqInv.letVars) b
            let invFun ← Meta.LetNormalize.letNormalize invFun {removeLambdaLet:=false}

            let is_inv ← mkSorry q(Function.Inverse $invFun $f) false

            let finv : FullInverse := {
              u := u, v := v, X := X, Y := Y, f := f, invFun := invFun, is_inv := is_inv
            }

            return .some (.full finv, goals)
          else
            let x₁Val ← mkProdElem eqInv.unresolvedXVars
            let x₂Val ← mkProdElem eqInv.resolvedXVars
            let ⟨u₁, X₁,_⟩ ← inferTypeQ x₁Val
            let ⟨u₂, X₂,_⟩ ← inferTypeQ x₂Val

            let p₁ : Q($X → $X₁) ← mkLambdaFVars #[x] (x₁Val.replaceFVars xiVars xis)
            let p₂ : Q($X → $X₂) ← mkLambdaFVars #[x] (x₂Val.replaceFVars xiVars xis)

            let q : Q($X₁ → $X₂ → $X) ←
              withLocalDecl `x₁ default (← inferType x₁Val) fun x₁Var => do
              withLocalDecl `x₂ default (← inferType x₂Val) fun x₂Var => do
                let (x₁s, _) ← splitStructureElem x₁Var
                let (x₂s, _) ← splitStructureElem x₂Var
                mkLambdaFVars #[x₁Var, x₂Var] <|
                  xVar.replaceFVars (eqInv.unresolvedXVars ++ eqInv.resolvedXVars) (x₁s ++ x₂s)

            let proof ← mkFreshExprMVarQ q(IsDecomposition $p₁ $p₂ $q)

            let l ← proof.mvarId!.constructor
            l.forM fun m => do
              let (_,m') ← m.intros
              m'.refl

            let dec : StructureDecomposition := {
              u := u, v := u₁, w := u₂, X := X, X₁ := X₁, X₂ := X₂
              p₁ := p₁
              p₂ := p₂
              q := q
              proof := proof
            }

            let invFun ← mkLambdaFVars (eqInv.unresolvedXVars ++ #[y] ++ eqInv.letVars) b
            let invFun ← Meta.LetNormalize.letNormalize invFun {removeLambdaLet:=false}
            let invFun : Q($X₁ → $Y → $X) ← mkUncurryFun eqInv.unresolvedXVars.size invFun

            let right_inv ← mkSorry q(∀ x₁, Function.RightInverse ($invFun x₁) $f) false
            let left_inv  ← mkSorry q(∀ x₁, Function.LeftInverse (fun y => $p₂ ($invFun x₁ y)) (fun x₂ => $f ($q x₁ x₂))) false

            let rinv : RightInverse := {
              v := v, Y := Y, decX := dec, f := f, invFun := invFun
              right_inv := right_inv
              left_inv := left_inv
            }

            return .some (.right rinv, goals)

  | _ => throwError "Error in `invertFunction`, not a lambda function!"



-- open Elab Term in
-- elab "structural_inverse " e:term t:tac : term => do

--   let e ← elabTerm e none

--   IO.println (← ppExpr e)

--   let .some (inv, goals) ← structuralInverse e
--     | throwError "failed to get structural inverse"


--   for goal in goals do
--     let prf ← elabByTactic
--     goal. goals.size != 0 then
--     throwError s!"failed to get structural inverse, pending goals: {← goals.mapM fun g => g.withContext do pure <| toString <| ← ppExpr (← g.getType)}"

--   match inv with
--   | .full inv => return inv.invFun
--   | .right inv => return inv.invFun


-- set_option pp.funBinderTypes true in
-- #check structural_inverse fun (x : Int×Int) => x.2+x.1

-- #check structural_inverse fun ((x,y,z) : Int × Int × Int) => (x+y+z,x+y)


-- #eval show MetaM Unit from do

--   let e := q(fun ((x,y,z) : Int × Int × Int) => (x+y+z,x+y))

--   let .some (.right inv, goals) ← structuralInverse e
--     | return ()

--   IO.println s!"asdf {← ppExpr inv.invFun}"

/-
#eval show MetaM Unit from do

  let e := q(fun ((x,y,z) : Int × Int × Int) => (z,x))

  let .some (.right inv,goals) ← structuralInverse e
    | return ()

  IO.println s!"asdf {← ppExpr inv.invFun}"
  IO.println s!"asdf {← goals.mapM fun m => m.withContext (inferType (Expr.mvar m) >>= isTypeCorrect)}"

#eval show MetaM Unit from do

  let e := q(fun ((x,y,z) : Int × Int × Int) => (z,x,y))

  let .some (.full inv,goals) ← structuralInverse e
    | return ()

  IO.println s!"asdf {← ppExpr inv.invFun}"
  IO.println s!"asdf {← goals.mapM fun m => m.withContext (inferType (Expr.mvar m) >>= isTypeCorrect)}"


def swap (xy : Int×Int) : Int × Int := (xy.2, xy.1)

#eval show MetaM Unit from do

  let e := q(fun (xyz : Int × Int × Int) => (xyz.1+2 + xyz.2.1 + xyz.2.2, swap xyz.2))

  let .some (.full inv,goals) ← structuralInverse e
    | return ()

  IO.println s!"asdf {← ppExpr inv.invFun}"
  IO.println s!"asdf {← goals.mapM fun m => m.withContext (m.getType >>= ppExpr)}"


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

-/
