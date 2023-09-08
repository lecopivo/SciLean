import SciLean

open SciLean

set_option linter.unusedVariables false

open Lean Meta

partial def splitToProjections (e : Expr) : MetaM (Array Expr) := do

  let .some info := getStructureInfo? (← getEnv) (← inferType e).getAppFn.constName
    | return #[e]

  -- for some reason fieldInfo comes in the opposite order then I would expect
  let eis ← info.fieldInfo.reverse.mapM (fun finfo => mkAppM finfo.projFn #[e])

  let eis ← eis.mapM splitToProjections
  return eis.flatten
  

def splitLambdaParallel (e : Expr)  : MetaM (Expr × Array Expr × Array Expr) := do
  match e with 
  | .lam xName xType xBody xBi => 
    let e ← instantiateMVars e
    lambdaTelescope e λ xs b => do
      let x := xs[0]!
      let b := b.instantiate1 x
      let xId := x.fvarId!

      let xis ← splitToProjections x
      IO.println (← xis.mapM ppExpr)

      withLocalDecls (xis.mapIdx fun i xi => (xName.appendAfter (toString i),xBi, fun _ => inferType xi))
        fun xiVars => do
          IO.println s!"asdf {← ppExpr b}"
          -- This is probably quite slow and has issues with Expr.proj
          let b := b.replace (fun x => xis.findIdx? (fun xi => x==xi) |>.map (fun i => xiVars[i]!))
          if b.containsFVar xId then
            throwError s!"failed to eliminate argument occurences {← ppExpr b}"

          let bis ← splitToProjections b 
          let bis ← bis.mapM reduceProjOfCtor

          let idxMap := xiVars.mapIdx fun i xiVar => (i.1, bis.findIdx? (fun bi => bi.containsFVar xiVar.fvarId!))

          IO.println s!"asdf {← ppExpr b}"
          IO.println s!"asdf {← bis.mapM ppExpr}"
          IO.println s!"perm {idxMap}"
          return default

      -- let ys := b.getAppArgs
      -- let mut f := b.getAppFn

      -- let mut lctx ← getLCtx
      -- let instances ← getLocalInstances

      -- let mut ys' : Array Expr := #[]
      -- let mut zs  : Array Expr := #[]

      -- if f.containsFVar xId then
      --   let zId ← withLCtx lctx instances mkFreshFVarId
      --   lctx := lctx.mkLocalDecl zId (name) (← inferType f)
      --   let z := Expr.fvar zId
      --   zs  := zs.push z
      --   ys' := ys'.push f
      --   f := z

      -- for y in ys, i in [0:ys.size] do
      --   if y.containsFVar xId then
      --     let zId ← withLCtx lctx instances mkFreshFVarId
      --     lctx := lctx.mkLocalDecl zId (name.appendAfter (toString i)) (← inferType y)
      --     let z := Expr.fvar zId
      --     zs  := zs.push z
      --     ys' := ys'.push y
      --     f := f.app z
      --   else
      --     f := f.app y

      -- let y' ← mkProdElem ys' mk
      -- let g  ← mkLambdaFVars xs y'

      -- f ← withLCtx lctx instances (mkLambdaFVars (zs ++ xs[1:]) f)
      -- f ← mkUncurryFun zs.size f mk fst snd

      -- return (f, g)
    
  | _ => throwError "Error in `splitLambdaToComp`, not a lambda function!"

open Qq in
#eval show MetaM Unit from do

  let e := q(fun xy : Int × Int => (xy.snd+2, xy.fst*2))
  let (f,gs,ps) ← splitLambdaParallel e

  IO.println ""

  let e := q(fun x : Int × (Int × Int) × Int => ((x.1,x.2.1.1), (x.2.1.2,x.2.2)))
  let (f,gs,ps) ← splitLambdaParallel e

  IO.println ""

  let e := q(fun x : (Int × Int) × (Int × Int) => ((x.1.1,x.2.1), (x.1.2,x.2.2)))
  let (f,gs,ps) ← splitLambdaParallel e


#exit
open Lean Meta Qq 
def invert (e : Expr) : MetaM Expr := do

  match e with 
  | .lam n xType xBody xBi => 
    withLocalDecl n xBi xType fun x => do
    let xBody := xBody.instantiate1 x

    let (f,g) ← splitLambdaToComp e

    sorry
  | _ => sorry
