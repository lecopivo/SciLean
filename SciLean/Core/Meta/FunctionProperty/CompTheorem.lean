import SciLean.Core.Defs
import SciLean.Lean.Meta.Basic

namespace SciLean

set_option linter.unusedVariables false 

open Lean Parser.Term Lean.Elab Meta

/--
For free variables `#[x₁, .., xₙ]` create a fitting name for a variable of type `X₁ × .. × Xₙ`

Returns `x₁..xₙ`, for example for `#[x,y]` returns `xy`
 -/
private def mkProdFVarName (xs : Array Expr) : MetaM Name := do
  let name : String ← xs.foldlM (init:="") λ n x => do return (n ++ toString (← x.fvarId!.getUserName))
  pure name


private def createCompositionImpl (e : Expr) (xs : Array Expr) (k : (T : Expr) → (t : Expr) → (ys : Array Expr) → (e' : Expr) → MetaM α) : MetaM α := do
  withLocalDecl `T .implicit (mkSort levelOne) λ T => do
    withLocalDecl `t .default T λ t => do
      
      let xIds := xs.map λ x => x.fvarId!

      -- We are not using `withLocalDecls` as it requires `Inhabited α` and that 
      -- does not play well with map4MetaM
      let mut lctx ← getLCtx
      let mut i := lctx.numIndices
      let mut ys : Array Expr := .mkEmpty xs.size
      for id in xIds do 
        let name ← id.getUserName
        let bi ← id.getBinderInfo 
        let type ← mkArrow T (← id.getType)
        let yId ← mkFreshFVarId
        ys := ys.push (mkFVar yId)
        lctx := lctx.addDecl (mkLocalDeclEx i yId name type bi)
        i := i + 1

      withLCtx lctx (← getLocalInstances) do
        let yts ← ys.mapM λ y => mkAppM' y #[t]
        let replacePairs := xIds.zip yts
        let e' := replacePairs.foldl (init:=e) λ e (id,yt) => e.replaceFVarId id yt

        k T t ys e'

variable [MonadControlT MetaM n] [Monad n]

/-- 
  For every free variable `x : X` introduce `y : T → X` and replace every `x` in `e` with `y t`.

  Then call `k` on `e` providing the newly introduces `T`, `t`, `ys`
  -/
def createComposition  (e : Expr) (xs : Array Expr) (k : (T : Expr) → (t : Expr) → (ys : Array Expr) → (e' : Expr) → n α) : n α := 
  map4MetaM (fun k => createCompositionImpl e xs k) k


/-- 
  For every free variable `x : X`, elements of `xs`, introduce `y : T → X`, elements of `ys`, and: 
    - replace every `x` in `e` with `y t` 
    - replace every `x` in `other` with `y`.
  where `{T : Type} (t : T)` are newly introduced free variables

  Then call `k` on `e` providing `T`, `t`, `ys` `other`

  NOTE: Most likely this operation makes sense only if `other` is a list of free variables
  -/
def createCompositionOther (e : Expr) (xs : Array Expr) (other : Array Expr) 
  (k : (T : Expr) → (t : Expr) →  (ys : Array Expr) → (other' : Array Expr) → (e' : Expr) → n α) : n α := do

  createComposition e xs λ T t ys e => do 
    
    let other := other.map λ e' => 
      e'.replace (λ e'' => Id.run do
        for (x, y) in xs.zip ys do
          if e'' == x then 
            return some y
        return none)

    k T t ys other e


def mkCompTheoremFunProp (funProp spaceName : Name) (e : Expr) (xs : Array Expr) (contextVars : Array Expr) : MetaM Expr := do

  createCompositionOther e xs contextVars λ T t ys abstractOver e => do

    withLocalDecl `inst .instImplicit (← mkAppM spaceName #[T]) λ SpaceT => do

      let funPropDecls ← ys.mapM λ y => do
        let name := `inst
        let bi := BinderInfo.instImplicit
        let type ← mkAppM funProp #[y]
        pure (name, bi, λ _ => pure type)
  
      withLocalDecls funPropDecls λ ysProp => do
        let vars := #[T,SpaceT]
          |>.append abstractOver
          |>.append ysProp
        let statement ← mkAppM funProp #[← mkLambdaFVars #[t] e]

        mkForallFVars vars statement >>= instantiateMVars


/--
This function expects that `defVal` has the same type as `mkTargetExprDifferential e xs`

Assuming that `xs` is a subset of `contextVars`
-/
def mkCompTheoremDifferential (e : Expr) (xs : Array Expr) (contextVars : Array Expr) (defVal : Expr) : MetaM Expr := do

  createCompositionOther e xs contextVars λ T t ys contextVars e => do

    withLocalDecl `inst .instImplicit (← mkAppM ``Vec #[T]) λ SpaceT => do

      let lhs ← mkAppM ``differential #[← mkLambdaFVars #[t] e]

      let dtName := (← t.fvarId!.getUserName).appendBefore "d"
      withLocalDecl dtName .default (← inferType t) λ dt => do

        let funPropDecls ← ys.mapM λ y => do
          let name := `inst
          let bi := BinderInfo.instImplicit
          let type ← mkAppM ``IsSmooth #[y]
          pure (name, bi, λ _ => pure type)

        withLocalDecls funPropDecls λ ysProp => do
          let contextVars := #[T,SpaceT]
            |>.append contextVars
            |>.append ysProp

          let mut lctx ← getLCtx
          let mut i := lctx.numIndices
          let mut xs'  : Array Expr := .mkEmpty xs.size
          let mut dxs' : Array Expr := .mkEmpty xs.size
          for y in ys do 
            let id := y.fvarId!
            let  xName := (← id.getUserName).appendAfter "'"
            let dxName := xName.appendBefore "d"
            let  xVal ← mkAppM' y #[t]
            let dxVal ← mkAppM' (← mkAppM ``differential #[y]) #[t,dt]
            let  xType ← inferType xVal
            let dxType ← inferType dxVal
            let  xId ← mkFreshFVarId
            let dxId ← mkFreshFVarId
            xs'  :=  xs'.push (mkFVar  xId)
            dxs' := dxs'.push (mkFVar dxId)
            lctx := lctx.addDecl (mkLetDeclEx i xId xName xType xVal)
            lctx := lctx.addDecl (mkLetDeclEx (i+1) dxId dxName dxType dxVal)
            i := i + 2

          withLCtx lctx (← getLocalInstances) do

            let rhs ← 
              mkLambdaFVars xs defVal -- abstract old xs
              >>=
              λ e => mkAppM' e xs' >>= pure ∘ Expr.headBeta  -- replace xs with xs' 
              >>=
              λ e => mkAppM' e dxs' >>= pure ∘ Expr.headBeta -- apply dxs'
              >>=
              λ e => mkLambdaFVars (xs'.append dxs') e
              >>=
              λ e => mkLambdaFVars #[t,dt] e  -- abstract over t and dt

            mkForallFVars contextVars (← mkEq lhs rhs)


/--
This function expects that `defVal` has the same type as `mkTargetExprTangentMap e xs`

Assuming that `xs` is a subset of `contextVars`
-/
def mkCompTheoremTangentMap (e : Expr) (xs : Array Expr) (contextVars : Array Expr) (defVal : Expr) : MetaM Expr := do

  createCompositionOther e xs contextVars λ T t ys contextVars e => do

    withLocalDecl `inst .instImplicit (← mkAppM ``Vec #[T]) λ SpaceT => do

      let lhs ← mkAppM ``tangentMap #[← mkLambdaFVars #[t] e]

      let dtName := (← t.fvarId!.getUserName).appendBefore "d"
      withLocalDecl dtName .default (← inferType t) λ dt => do

        let funPropDecls ← ys.mapM λ y => do
          let name := `inst
          let bi := BinderInfo.instImplicit
          let type ← mkAppM ``IsSmooth #[y]
          pure (name, bi, λ _ => pure type)

        withLocalDecls funPropDecls λ ysProp => do
          let contextVars := #[T,SpaceT]
            |>.append contextVars
            |>.append ysProp

          let mut lctx ← getLCtx
          let mut i := lctx.numIndices
          let mut Txs' : Array Expr := .mkEmpty xs.size
          for y in ys do 
            let id := y.fvarId!
            let  xName := (← id.getUserName).appendAfter "'"
            let TxName := xName.appendBefore "T"
            let TxVal ← mkAppM' (← mkAppM ``tangentMap #[y]) #[t,dt]
            let TxType ← inferType TxVal
            let TxId ← mkFreshFVarId
            let TxFVar := mkFVar TxId
            Txs'  :=  Txs'.push (mkFVar TxId)
            lctx := lctx.addDecl (mkLetDeclEx i TxId TxName TxType TxVal)
            i := i + 1

          withLCtx lctx (← getLocalInstances) do

            let  xs' ← Txs'.mapM (λ Tx => mkProdProj Tx 0)
            let dxs' ← Txs'.mapM (λ Tx => mkProdProj Tx 1)

            let rhs ← do
              let mut e ← mkLambdaFVars xs defVal -- abstract old xs
              e ← mkAppM' e xs' >>= pure ∘ Expr.headBeta  -- replace xs with xs' 
              e ← mkAppM' e dxs' >>= pure ∘ Expr.headBeta -- apply dxs'
              e ← mkLambdaFVars Txs' e
              mkLambdaFVars #[t,dt] e  -- abstract over t and dt

            mkForallFVars contextVars (← mkEq lhs rhs)


/--
This function expects that `defVal` has the same type as `mkTargetExprTangentMap e xs`

Assuming that `xs` is a subset of `contextVars`
-/
def mkCompTheoremAdjoint (e : Expr) (xs : Array Expr) (contextVars : Array Expr) (defVal : Expr) : MetaM Expr := do

  createCompositionOther e xs contextVars λ T t ys contextVars e => do

    withLocalDecl `inst .instImplicit (← mkAppM ``SemiHilbert #[T]) λ SpaceT => do

      let lhs ← mkAppM ``adjoint #[← mkLambdaFVars #[t] e]

      let xName' := (← mkProdFVarName xs).appendAfter "'"
      let xType' ← inferType e
      withLocalDecl xName' .default xType' λ x' => do

        let funPropDecls ← ys.mapM λ y => do
          let name := `inst
          let bi := BinderInfo.instImplicit
          let type ← mkAppM ``HasAdjoint #[y]
          pure (name, bi, λ _ => pure type)

        withLocalDecls funPropDecls λ ysProp => do
          let contextVars := #[T,SpaceT]
            |>.append contextVars
            |>.append ysProp
            
          let xName'' := xName'.appendAfter "'"
          let xVal'' := (← mkAppM' defVal #[x']).headBeta
          let xType'' ← inferType xVal''

          withLetDecl xName'' xType'' xVal'' λ x'' => do

            let yVals' ← ys.mapIdxM λ i y => do
                let y ← mkAppM ``adjoint #[y] 
                mkAppM' y #[← mkProdProj x'' i]

            let ySum ← mkAppFoldlM ``HAdd.hAdd yVals'

            let rhs ← mkLambdaFVars #[x',x''] ySum

            mkForallFVars contextVars (← mkEq lhs rhs)


/--
This function expects that `defVal` has the same type as `mkTargetExprDifferential e xs`

Assuming that `xs` is a subset of `contextVars`
-/
def mkCompTheoremAdjDiff (e : Expr) (xs : Array Expr) (contextVars : Array Expr) (defVal : Expr) : MetaM Expr := do

  createCompositionOther e xs contextVars λ T t ys contextVars e => do

    withLocalDecl `inst .instImplicit (← mkAppM ``SemiHilbert #[T]) λ SpaceT => do

      let lhs ← mkAppM ``adjointDifferential #[← mkLambdaFVars #[t] e]

      let dxsName' := (← mkProdFVarName xs).appendAfter "'" |>.appendBefore "d"
      let dxsType' ← inferType e

      withLocalDecl dxsName' .default dxsType' λ dxs' => do

        let funPropDecls ← ys.mapM λ y => do
          let name := `inst
          let bi := BinderInfo.instImplicit
          let type ← mkAppM ``HasAdjDiff #[y]
          pure (name, bi, λ _ => pure type)

        withLocalDecls funPropDecls λ ysProp => do
          let contextVars := #[T,SpaceT]
            |>.append contextVars
            |>.append ysProp

          let mut lctx ← getLCtx
          let mut i := lctx.numIndices
          let mut xs'  : Array Expr := .mkEmpty xs.size
          for y in ys do 
            let id := y.fvarId!
            let  xName := (← id.getUserName).appendAfter "'"
            let  xVal ← mkAppM' y #[t]
            let  xType ← inferType xVal
            let  xId ← mkFreshFVarId
            xs'  :=  xs'.push (mkFVar  xId)
            lctx := lctx.addDecl (mkLetDeclEx i xId xName xType xVal)
            i := i + 1

          withLCtx lctx (← getLocalInstances) do

            -- replace `xs` with `xs'`
            let defVal := (← mkAppM' (← mkLambdaFVars xs defVal) xs').headBeta

            let dxsName : Name := ← xs.foldlM (init:="") λ (s : String) x => do
              let xName := toString (← x.fvarId!.getUserName)
              return s ++ "d" ++ xName
            let dxsVal := (← mkAppM' defVal #[dxs']).headBeta
            let dxsType ← inferType dxsVal

            withLetDecl dxsName dxsType dxsVal λ dxs => do

              let dxVals ← mkProdSplitElem dxs xs.size

              let xdxVals ← (ys.zip dxVals).mapM 
                λ (y,dx) => mkAppM ``adjointDifferential #[y, t, dx]

              let sum ← mkAppFoldlM ``HAdd.hAdd xdxVals

              let rhs ← mkLambdaFVars ((#[t,dxs'].append xs').push dxs) sum

              mkForallFVars contextVars (← mkEq lhs rhs)

/--
This function expects that `defVal` has the same type as `mkTargetExprDifferential e xs`

Assuming that `xs` is a subset of `contextVars`
-/
def mkCompTheoremRevDiff (e : Expr) (xs : Array Expr) (contextVars : Array Expr) (defVal : Expr) : MetaM Expr := do

  createCompositionOther e xs contextVars λ T t ys contextVars e => do

    withLocalDecl `inst .instImplicit (← mkAppM ``SemiHilbert #[T]) λ SpaceT => do

      let lhs ← mkAppM ``reverseDifferential #[← mkLambdaFVars #[t] e]

      let funPropDecls ← ys.mapM λ y => do
        let name := `inst
        let bi := BinderInfo.instImplicit
        let type ← mkAppM ``HasAdjDiff #[y]
        pure (name, bi, λ _ => pure type)

      withLocalDecls funPropDecls λ ysProp => do
        let contextVars := #[T,SpaceT]
          |>.append contextVars
          |>.append ysProp

        let mut lctx ← getLCtx
        let mut i := lctx.numIndices
        let mut Rxs : Array Expr := .mkEmpty xs.size
        for y in ys do 
          let id := y.fvarId!
          let RxName := (← id.getUserName).appendBefore "R"
          let RxVal ← mkAppM ``reverseDifferential #[y, t]
          let RxType ← inferType RxVal
          let RxId ← mkFreshFVarId
          Rxs  := Rxs.push (mkFVar RxId)
          lctx := lctx.addDecl (mkLetDeclEx i RxId RxName RxType RxVal)
          i := i + 1

        withLCtx lctx (← getLocalInstances) do

          let xs' ← Rxs.mapM λ Rx => mkProdProj Rx 0

          -- replace `xs` with `xs'`
          let RfxVal := (← mkAppM' (← mkLambdaFVars xs defVal) xs').headBeta

          withLetDecl `Rfx (← inferType RfxVal) RfxVal λ Rfx => do

            let fx  ← mkProdProj Rfx 0
            let df' ← mkProdProj Rfx 1

            let dxsName' := (← mkProdFVarName xs).appendAfter "'" |>.appendBefore "d"
            let dxsType' ← inferType e

            let dF' ←
              withLocalDecl dxsName' .default dxsType' λ dxs' => do

                let dxsName : Name := ← xs.foldlM (init:="") λ (s : String) x => do
                  let xName := toString (← x.fvarId!.getUserName)
                  return s ++ "d" ++ xName
                let dxsVal ← mkAppM' df' #[dxs']
                let dxsType ← inferType dxsVal

                withLetDecl dxsName dxsType dxsVal λ dxs => do

                  let dxVals ← mkProdSplitElem dxs xs.size
                  let dxFuns ← Rxs.mapM λ Rx => mkProdProj Rx 1

                  let xdxVals ← (dxFuns.zip dxVals).mapM 
                    λ (df,dx) => mkAppM' df #[dx]

                  let sum ← mkAppFoldlM ``HAdd.hAdd xdxVals

                  mkLambdaFVars #[dxs',dxs] sum

            let rhs ← mkLambdaFVars ((#[t].append Rxs).push Rfx) (← mkProdElem #[fx, dF'])

            mkForallFVars contextVars (← mkEq lhs rhs)



def mkCompTheorem (transName : Name) (e : Expr) (xs : Array Expr) (contextVars : Array Expr) (defVal : Expr) : MetaM Expr := do
  if transName == ``differential then
    mkCompTheoremDifferential e xs contextVars defVal  >>= instantiateMVars
  else if transName == ``tangentMap then
    mkCompTheoremTangentMap e xs contextVars defVal  >>= instantiateMVars
  else if transName == ``adjoint then
    mkCompTheoremAdjoint e xs contextVars defVal  >>= instantiateMVars
  else if transName == ``adjointDifferential then
    mkCompTheoremAdjDiff e xs contextVars defVal  >>= instantiateMVars
  else if transName == ``reverseDifferential then
    mkCompTheoremRevDiff e xs contextVars defVal  >>= instantiateMVars
  else
    throwError "Error in `mkCompTheorem`, unrecognized function transformation `{transName}`."

