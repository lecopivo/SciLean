import Lean
import SciLean.Tactic.LSimp.Main
import SciLean.Tactic.DataSynth.Decl
import SciLean.Lean.Meta.Uncurry
import SciLean.Lean.Meta.Basic

import Mathlib.Logic.Equiv.Defs

open Lean Meta

namespace SciLean.Tactic.DataSynth

-------------------------------------------------

/-- Cache for normalization results

 -/
abbrev NormCache := ExprMap Expr

def NormM := StateM NormCache

-------------------------------------------------

structure Goal where
  /-- Expression for `fun (x₁ : X₁) ... (xₙ : Xₙ) → P` for some `P : Prop`
  The goal is to find `x₁`, ..., `xₙ` and proof of `goal x₁ ... xₙ` -/
  goal : Expr
  dataSynthDecl : DataSynthDecl
deriving Hashable, BEq

namespace Goal

/-- Make goal for the proof with fresh meta variables. -/
def mkFreshProofGoal (g : Goal) : MetaM (Array Expr × Expr) := do
  let (xs,_,e) ← lambdaMetaTelescope g.goal
  return (xs,e)

/-- Pretty print of the goal -/
def pp (g : Goal) : MetaM MessageData := do
  let (xs,_,e) ← lambdaMetaTelescope g.goal
  return m!"{xs}, {e}"


end Goal

/-- Result of data synthesization.

Synthesized data `xs = #[x₁, ..., xₙ]` and proof `proof` of `goal x₁ ... xₙ`. -/
structure Result where
  xs : Array Expr
  proof : Expr
  goal : Goal


namespace Result

def getSolvedGoal (r : Result) : Expr := r.goal.goal.beta r.xs

/-- Given result for `g` and alternative data `xs` that is propositional to the data of the result `hs`. Proof `hs[i]` can be none if
`r.xs[i]` and `xs[i]` are defeq.

Return result with `xs` data. -/
def congr (r : Result) (rs : Array Simp.Result) : MetaM Result := do
  let goal := r.goal.goal

  -- proof that original result is equal to the result with normalized data
  let hgoal ←
      (r.xs.zip rs).foldlM (init:= ← mkEqRefl goal)
        (fun g (x,r) =>
          match r.proof? with
          | some hx => mkCongr g hx
          | none => mkCongrFun g x)
  let xs := rs.map (·.expr)

  -- cast proof of the orignal result to a proof of the new goal
  -- note: originaly we used `mkAppOptM` but replacing it with the following made
  --       `data_synth` four times faster on one test
  let .sort u ← inferType r.getSolvedGoal | throwError "bug"
  let proof := mkAppN (.const ``Eq.mp [u]) #[r.getSolvedGoal, goal.beta xs, hgoal, r.proof]

  return { xs := xs, proof := proof, goal := r.goal }

end Result


/-- For a `Goal` and its proof extract `Result` from it. -/
def Goal.getResultFrom (g : Goal) (proof : Expr) : MetaM Result := do

  -- todo: maybe add same sanity checks that we are doing reasonable things

  let P ← inferType proof
  let (xs,goal) ← g.mkFreshProofGoal
  if ¬(← isDefEq goal P) then
    throwError "invalid result of {← ppExpr P}"
  let xs ← xs.mapM instantiateMVars

  let r : Result := {
    xs := xs
    proof := ← instantiateMVars proof
    goal := g
  }
  return r


---------------------------------------------------

structure DataSynthConfig where
  maxNumSteps := 100
  normalizeLet := false
  normalizeLet' := false
  norm_core := true
  norm_lsimp := false
  norm_simp := false
  norm_dsimp := false
  domainDec := true

structure Config extends DataSynthConfig, Simp.Config


structure Context where
  config : Config := {}
  normalize : Expr → Simp.SimpM Simp.Result := fun e => return {expr := e}
  discharge : Expr → MetaM (Option Expr) := fun _ => return .none

structure State where
  numSteps := 0
  /-- cachec for results  -/
  cache : Std.HashMap Goal Result := {}
  /-- cache for failed goals -/
  failedCache : Std.HashSet Goal := {}
  -- /-- normalization cache -/
  -- normCache : Std.HashMap ExprStructEq Expr := {}


abbrev DataSynthM := ReaderT Context $ MonadCacheT ExprStructEq Expr $ StateRefT State Simp.SimpM


-----------

-- forward declaration

initialize dataSynthRef : IO.Ref (Goal → DataSynthM (Option Result)) ← IO.mkRef (fun _ => return none)
def dataSynth (g : Goal) : DataSynthM (Option Result) := do (← dataSynthRef.get) g


----


structure FunData where
  lctx : LocalContext
  insts : LocalInstances
  xs : Array Expr
  body : Expr
  deriving Inhabited


/-- Size of product type, assuming it is right associated
i.e. `prodSize (A×B×C) = 3` but `prodSize ((A×B)×C) = 2`
 -/
private def prodSize (e : Expr) : Nat :=
  go e 1
where
  go (e : Expr) (n : Nat) :=
    match e with
    | Expr.mkApp2 (.const ``Prod _) _ Y =>
      go Y (n+1)
    | _ => n

def curryLambdaTelescope (f : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let .forallE _ xType _ _ := (← inferType f)
    | throwError "can't curry `{← ppExpr f}` not a function"

  let n := prodSize xType
  let f ← mkCurryFun n f

  lambdaTelescope f k

def getFunData (f : Expr) : MetaM FunData := do
  curryLambdaTelescope (← ensureEtaExpanded f) fun xs b => do
    let data : FunData :=
      { lctx := ← getLCtx
        insts := ← getLocalInstances
        xs := xs
        body := b }
    return data


namespace FunData

def pp (f : FunData) : MetaM String :=
  withLCtx f.lctx f.insts do
    let xnames ← f.xs.mapM ppExpr
    let binder :=
      if f.xs.size = 1 then
        xnames[0]!
      else
        "(" ++ xnames.joinl id (· ++ ", " ++ ·) ++ ")"
    return s!"fun {binder} => {← ppExpr f.body}"

/-- Return `fun ((x₁,x₂,...,xₙ) : X₁×X₂×...×Xₙ) => f x₁ ... xₙ)` -/
def toExpr (f : FunData) : MetaM Expr :=
  withLCtx f.lctx f.insts do
    mkUncurryLambdaFVars f.xs f.body

/-- Returnns `(fun (x₁ : X₁) ((x₂,...,xₙ) : X₂×...×Xₙ) => f x₁ ... xₙ)` -/
def toExprCurry1 (f : FunData) : MetaM Expr :=
  withLCtx f.lctx f.insts do
    mkLambdaFVars #[f.xs[0]!] (← mkUncurryLambdaFVars f.xs[1:] f.body)

inductive FunHead where
  | bvar (i : Nat)
  | fvar (id : FVarId)
  | app
  | letE
  | lam
  | unimplemented
  deriving Repr

/-- Head of the function body. -/
def funHead (f : FunData) : MetaM FunHead :=
  match f.body with
  | .const .. | .proj .. | .app .. => return .app
  | .fvar xId =>
    let x := Expr.fvar xId
    if let .some i := f.xs.findIdx? (fun x' => x == x') then
      return .bvar i
    else
      return .fvar xId
  | .letE .. => return .letE
  | .lam .. => return .lam
  | .sort .. | .mdata .. | .mvar .. | .forallE .. | .bvar .. | .lit .. =>
    withLCtx f.lctx f.insts do
      throwError "invalid function body, ctor:{f.body.ctorName}\n{← ppExpr f.body}"

/-- Composition of two function.-/
inductive FunDecomp where
/-- Standard composition of `f` and `g` as `f∘g` -/
| comp (f g : FunData)
/-- Composition through letbinding, `fun x => let y := g x; f y x` -/
| letE (f g : FunData)
| none

/-- Decompose function as composition of two functions. -/
def decompose (f : FunData) : MetaM FunDecomp := do
  withLCtx f.lctx f.insts do
    let .letE n t v b _ := f.body | return .none

    let g : FunData := {
      lctx := f.lctx
      insts := f.insts
      xs := f.xs
      body := v
    }

    withLocalDeclD n t fun y => do
      let f : FunData := {
        lctx := ← getLCtx
        insts := f.insts
        xs := #[y] ++ f.xs
        body := b.instantiate1 y
      }

      return .letE f g


/-- Given a function `f : X → Y` find
`p₁ : X → X₁`, `p₂ : X → X₂` and `q : X₁ → X₂`  and `g : X₁ → Y`  -/
def decomposeDomain? (f : FunData) : MetaM (Option (Expr × Expr × Expr × FunData)) := do
  withLCtx f.lctx f.insts do

    if f.xs.size ≤ 1 then
      return none

    let vars := (← f.body.collectFVars |>.run {}).2.fvarSet
    let (xs₁, xs₂) := f.xs.partition (fun x => vars.contains x.fvarId!)

    if xs₂.size = 0 then
      return none

    let g : FunData := {f with xs := xs₁}

    let p₁ ←
      mkUncurryLambdaFVars f.xs (← mkProdElem xs₁) (withLet:=false)
    let p₂ ←
      mkUncurryLambdaFVars f.xs (← mkProdElem xs₂) (withLet:=false)

    let q ←
      mkUncurryLambdaFVars xs₂ (← mkProdElem f.xs) (withLet:=false)
      >>=
      mkUncurryLambdaFVars xs₁ (withLet:=false)

    return some (p₁,p₂,q,g)


end FunData


initialize dataSynthFunRef : IO.Ref (Goal → FunData → DataSynthM (Option Result)) ←
  IO.mkRef (fun _ _ => return none)

/-- Tactic `data_synth` driven by a input function `f` -/
def dataSynthFun (e : Goal) (f : FunData) : DataSynthM (Option Result) := do
  (← dataSynthFunRef.get) e f


--------------------------------------------------------------------------------------------------
