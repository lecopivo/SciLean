import Lean
import SciLean.Tactic.LSimp.Main
import SciLean.Tactic.DataSynth.Decl
import SciLean.Lean.Meta.Uncurry

open Lean Meta

namespace SciLean.Tactic.DataSynth

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

/-- Given result for `g` and alternative data `xs` that is propositional to the data of the result `hs`. Proof `hs[i]` can be none if
`r.xs[i]` and `xs[i]` are defeq.

Return result with `xs` data. -/
def congr (r : Result) (rs : Array Simp.Result) : MetaM Result := do
  let goal := r.goal.goal
  -- todo: this proof can be optimized as there is no need to start with `← mkEqRefl goal`
  let hgoal ← (r.xs.zip rs).foldlM (init:= ← mkEqRefl goal)
    (fun g (x,r) =>
      match r.proof? with
      | some hx => mkCongr g hx
      | none => mkCongrFun g x)
  let xs := rs.map (·.expr)
  let proof ← mkAppOptM ``Eq.mp #[← inferType r.proof, goal.beta xs, hgoal, r.proof]
  return { xs := xs, proof := proof, goal := r.goal }

def getSolvedGoal (r : Result) : Expr := r.goal.goal.beta r.xs

end Result


---------------------------------------------------

structure DataSynthConfig where
  maxNumSteps := 100
  normalizeLet := true
  lsimp := false
  simp := false

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


abbrev DataSynthM := ReaderT Context $ StateRefT State Simp.SimpM

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

def getFunData (f : Expr) : MetaM FunData :=
  uncurryLambdaTelescopeOnceImpl f fun xs b => do
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


end FunData

-- data synth driven by a function
initialize dataSynthFunRef : IO.Ref (Goal → FunData → DataSynthM (Option Result)) ←
  IO.mkRef (fun _ _ => return none)
def dataSynthFun (e : Goal) (f : FunData) : DataSynthM (Option Result) := do
  (← dataSynthFunRef.get) e f



--------------------------------------------------------------------------------------------------
