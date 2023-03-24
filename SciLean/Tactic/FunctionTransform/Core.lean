import Std.Lean.Parser
import Std.Lean.Meta.DiscrTree
import Mathlib.Algebra.Invertible
import Mathlib.Data.Rat.Cast
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Conv
import Qq.MetaM
import Qq.Delab

open Lean
open Lean.Meta Qq Lean.Elab Term


initialize registerTraceClass `Meta.Tactic.fun_trans
initialize registerTraceClass `Meta.Tactic.fun_trans.step
initialize registerTraceClass `Meta.Tactic.fun_trans.trans


def diff (f : α → β) : α → α → β := sorry

prefix:max "∂" => diff

theorem diff_I  : ∂ (λ x : α => x) = λ x dx => dx := sorry
-- theorem diff_K : ∂ (λ (x : α) (y : β) => x) = λ x dx y => dx := sorry
theorem diff_K [OfNat α 0] (β : Type _) (x : α) : ∂ (λ (y : β) => x) = λ y dy => 0 := sorry
theorem diff_B (f : β → γ) (g : α → β) 
  : ∂ (λ x => f (g x)) 
    = 
    λ x dx => ∂ f (g x) (∂ g x dx) := sorry
theorem diff_S [Add γ] (f : α → β → γ) (g : α → β) 
  : ∂ (λ x => f x (g x)) 
    = 
    λ x dx => 
      ∂ f x dx (g x) 
      + 
      ∂ (f x) (g x) (∂ g x dx) := sorry
theorem diff_C (f : β → α → γ)
  : ∂ (λ (x : α) (y : β) => f y x)
    =
    λ x dx y => ∂ (f y) x dx := sorry
theorem diff_eval (β) (x : α)
  : ∂ (λ (f : α → β) => f x)
    =
    λ f df => df x := sorry

def adj (f : α → β) : β → α := sorry

postfix:max "†" => adj

theorem adj_I  : ∂ (λ x : α => x) = λ x dx => dx := sorry
theorem adj_B (f : β → γ) (g : α → β) 
  : (λ x => f (g x))†
    = 
    λ z => g† (f† z) := sorry

theorem adj_S [Add α] (f : α → β → γ) (g : α → β) 
  : (λ x => f x (g x))†
    = 
    λ z => 
      let (a,b) := (λ ab : α×β => f ab.1 ab.2)† z
      a + g† b := sorry

def sum (f : α → β) : β := sorry

@[simp] theorem diff_sum 
  : ∂ (λ (f : α → β) => sum f)
    =
    λ f df => sum df := sorry

@[simp] theorem sum_eval (f : α → β → γ) (b : β)
  : sum f b
    =
    sum (λ a => f a b) := sorry

theorem adj_C (f : β → α → γ)
  : (λ (x : α) (y : β) => f y x)†
    =
    λ g => sum λ y => (f y)† (g y) := sorry

def kron (i i' : α) (b : β) : β := sorry

theorem adj_eval (β) (x : α)
  : (λ (f : α → β) => f x)†
    =
    λ y x' => kron x x' y := sorry

/--
Constructs a proof that the original expression is true
given a simp result which simplifies the target to `True`.
-/
def _root_.Lean.Meta.Simp.Result.ofTrue (r : Simp.Result) : MetaM (Option Expr) :=
  if r.expr.isConstOf ``True then
    some <$> match r.proof? with
    | some proof => mkOfEqTrue proof
    | none => pure (mkConst ``True.intro)
  else
    pure none

def _root_.Array.filterIdx (p : α → Bool) (as : Array α) : Array Nat :=
  as |>.mapIdx (λ i a => if p a then some i.1 else none) 
     |>.filterMap id

def _root_.Array.findRevIdx? {α : Type} (as : Array α) (p : α → Bool) : Option Nat :=
  as.reverse.findIdx? p |>.map λ i => as.size - 1 - i

def getNameOfRuleI (transName : Name) : Option Name :=
  if transName == ``diff then
    return ``diff_I
  else if transName == ``adj then
    return ``adj_I
  else
    none

def applyRuleI (transName : Name) (X : Expr) : MetaM (Option (Expr×Expr)) := do
  if let .some rule := getNameOfRuleI transName then
    let proof ← Meta.mkAppOptM rule #[X]
    let rhs := (← inferType proof).getArg! 2
    return (rhs, proof)
  else 
    return none


def getNameOfRuleK (transName : Name) : Option Name :=
  if transName == ``diff then
    return ``diff_K
  else
    none

def applyRuleK (transName : Name) (x Y : Expr) : MetaM (Option (Expr×Expr)) := do
  if let .some rule := getNameOfRuleK transName then
    let proof ← Meta.mkAppM rule #[Y, x]
    let rhs := (← inferType proof).getArg! 2
    return (rhs, proof)
  else
    trace[Meta.Tactic.fun_trans.trans] s!"Failed applying rule K"
    return none


def getNameOfRuleS (transName : Name) : Option Name :=
  if transName == ``diff then
    return ``diff_S
  else if transName == ``adj then
    return ``adj_S
  else 
    none

def applyRuleS (transName : Name) (f g : Expr) : MetaM (Option (Expr×Expr)) := do
  if let .some rule := getNameOfRuleS transName then
    let proof ← Meta.mkAppM rule #[f,g]
    let rhs := (← inferType proof).getArg! 2
     return (rhs, proof)
   else 
     return none


def getNameOfRuleB (transName : Name) : Option Name :=
  if transName == ``diff then
    return ``diff_B
  else if transName == ``adj then
    return ``adj_B
  else 
    none

def applyRuleB (transName : Name) (f g : Expr) : MetaM (Option (Expr×Expr)) := do
  if let .some rule := getNameOfRuleB transName then
    let proof ← Meta.mkAppM rule #[f,g]
    let rhs := (← inferType proof).getArg! 2
     return (rhs, proof)
   else 
     return none

def getNameOfRuleC (transName : Name) : Option Name :=
  if transName == ``diff then
    return ``diff_C
  else if transName == ``adj then
    return ``adj_C
  else 
    none

def applyRuleC (transName : Name) (f : Expr) : MetaM (Option (Expr×Expr)) := do
  if let .some rule := getNameOfRuleC transName then
    let proof ← Meta.mkAppM rule #[f]
    let rhs := (← inferType proof).getArg! 2
    return (rhs, proof)
  else
    return none


def getNameOfRuleEval (transName : Name) : Option Name :=
  if transName == ``diff then
    return ``diff_eval
  else if transName == ``adj then
    return ``adj_eval
  else 
    none

def applyRuleEval (transName : Name) (x Y : Expr) : MetaM (Option (Expr×Expr)) := do
  if let .some rule := getNameOfRuleEval transName then
    let proof ← Meta.mkAppM rule #[Y, x]
    let rhs := (← inferType proof).getArg! 2
    return (rhs, proof)
  else 
    return none


/-- 
  Is expression `e` of the form `T f x₀ x₁ .. xₙ` where `T` is some function transformation?
 -/
def getFunctionTransform (e : Expr) : Option (Name × Expr × Array Expr) :=
  if e.isApp && (e.isAppOf ``diff) then     
    return (``diff, e.getAppArgs[2]!, e.getAppArgs[3:])
  else if e.isApp && (e.isAppOf ``adj) then     
    return (``adj, e.getAppArgs[2]!, e.getAppArgs[3:])
  else
    none


/-- 
  -/
def transformFunction (transName : Name) (f : Expr) : MetaM (Option (Expr × Expr)) := do
  match f with 
  | .lam .. => lambdaTelescope f λ xs b => do
    trace[Meta.Tactic.fun_trans.trans] s!"Transforming '{← Meta.ppExpr f}'"
    if h : xs.size > 0 then

      -- rule C: λ x y => f y x
      if (xs.size ≠ 1) then
        trace[Meta.Tactic.fun_trans.trans] s!"case: C 'f:{← Meta.ppExpr f}'"
        let f ← Meta.mkLambdaFVars (#[xs[1]!, xs[0]!].append xs[2:]) b
        return ← applyRuleC transName f.eta
      else 

        let x := xs[0]
        let xId := x.fvarId!

        -- rule I: λ x => x 
        if (b == x) then
          trace[Meta.Tactic.fun_trans.trans] s!"case: I '{← Meta.ppExpr f}'"
          return ← applyRuleI transName (← inferType x)

        -- rule K: λ x => y
        if ¬(b.containsFVar xId) then
          trace[Meta.Tactic.fun_trans.trans] s!"case: K '{← Meta.ppExpr f}'" 
          return ← applyRuleK transName b (← inferType x)

        -- case: λ x => F x
        else if b.isApp then


          let F    := b.getAppFn
          let args := b.getAppArgs

          trace[Meta.Tactic.fun_trans.trans] s!"Application case 'F:{← Meta.ppExpr F}' 'args:{← args.mapM Meta.ppExpr}'"

          -- the first arguments with non-trivial occurence of `x`        
          let id? := args.findIdx? (λ arg => (arg != x) && (arg.containsFVar xId))

          -- non trivial composition?
          if let .some id := id? then
            let yVal  := args[id]!
            let yType ← inferType yVal
            let g ← mkLambdaFVars #[x] yVal
            let f'proof : Option (Expr × Expr) ← 
              withLocalDecl `y .default yType λ y => do
              let fbody ← mkAppOptM' F ((args.set! id y).map .some)
              -- rule B: λ x => f (g x)
              if ¬(fbody.containsFVar xId) then
                let f ← mkLambdaFVars #[y] fbody
                trace[Meta.Tactic.fun_trans.trans] s!"case: B 'f:{← Meta.ppExpr f}' 'g:{← Meta.ppExpr g}'"
                return ← applyRuleB transName f.eta g.eta
  
              -- rule S: λ x => f x (g x)
              else
                let f ← mkLambdaFVars #[x,y] fbody
                trace[Meta.Tactic.fun_trans.trans] s!"case: S 'f:{← Meta.ppExpr f}' 'g:{← Meta.ppExpr g}'"
                return ← applyRuleS transName f.eta g.eta
            return f'proof

          
          -- arguments containing `x`
          let ids := args.filterIdx (λ arg => arg.containsFVar xId)

          -- case: λ f => f x₀ .. xₙ
          if (ids.size == 0) && (F == x) then  
            trace[Meta.Tactic.fun_trans.trans] s!"case: π '{← Meta.ppExpr f}'"
            let lastId  := args.size - 1
            let lastArg := args[args.size - 1]!
            let αtype ← inferType lastArg
            let βtype ← inferType b
            if args.size == 1 then
              return ← applyRuleEval transName lastArg βtype 
            else
              let g ← mkLambdaFVars #[x] (← mkAppM' F args[0:lastId])
              let f ← withLocalDecl `F .default (← mkArrow αtype βtype) λ F => do
                mkLambdaFVars #[F] (← mkAppM' F #[lastArg])
              return ← applyRuleB transName f.eta g.eta

    return none
  | _  => return none


/-- A simp plugin which calls `NormNum.eval`. -/
def tryFunTrans? (post := false) (e : Expr) : SimpM (Option Simp.Step) := do
  if post then
    trace[Meta.Tactic.fun_trans.step] s!"Post-step through {← Meta.ppExpr e}"
  else 
    trace[Meta.Tactic.fun_trans.step] s!"Pre-step through {← Meta.ppExpr e}"
  
  if let .some (transName, f, args) := getFunctionTransform e then
    if let .some (f', proof) ← transformFunction transName f then
      if args.size == 0 then
        return some (.visit (.mk f' proof 0))
      else if args.size == 1 then
        let f'' ← mkAppM' f' args
        let proof' ← mkAppM ``congr_fun #[proof, args[0]!]
        return some (.visit (.mk f'' proof' 0))
      else if args.size == 2 then
        let f'' ← mkAppM' f' args
        let proof' ← mkAppM ``congr_fun₂ #[proof, args[0]!, args[1]!]
        return some (.visit (.mk f'' proof' 0))
      else if args.size == 3 then
        let f'' ← mkAppM' f' args
        let proof' ← mkAppM ``congr_fun₃ #[proof, args[0]!, args[1]!, args[2]!]
        return some (.visit (.mk f'' proof' 0))
      else
        throwError "Finish implementings tryFunTrans?"
        -- return some (.visit (.mk e none 0))
    else return some (.visit (.mk e none 0))
  else 
    return some (.visit (.mk e none 0))
      

variable (ctx : Simp.Context) (useSimp := true) in
mutual
  /-- A discharger which calls `norm_num`. -/
  partial def discharge (e : Expr) : SimpM (Option Expr) := do (← deriveSimp e).ofTrue

  /-- A `Methods` implementation which calls `norm_num`. -/
  partial def methods : Simp.Methods :=
    if useSimp then {
      pre := fun e ↦ do
        Simp.andThen (← Simp.preDefault e discharge) tryFunTrans?
      post := fun e ↦ do
        Simp.andThen (← Simp.postDefault e discharge) (tryFunTrans? (post := true))
      discharge? := discharge
    } else {
      pre := fun e ↦ Simp.andThen (.visit { expr := e }) tryFunTrans?
      post := fun e ↦ Simp.andThen (.visit { expr := e }) (tryFunTrans? (post := true))
      discharge? := discharge
    }

  /-- Traverses the given expression using simp and normalises any numbers it finds. -/
  partial def deriveSimp (e : Expr) : MetaM Simp.Result :=
    (·.1) <$> Simp.main e ctx (methods := methods)
end


-- FIXME: had to inline a bunch of stuff from `simpGoal` here
/--
The core of `norm_num` as a tactic in `MetaM`.

* `g`: The goal to simplify
* `ctx`: The simp context, constructed by `mkSimpContext` and
  containing any additional simp rules we want to use
* `fvarIdsToSimp`: The selected set of hypotheses used in the location argument
* `simplifyTarget`: true if the target is selected in the location argument
* `useSimp`: true if we used `norm_num` instead of `norm_num1`
-/
def funTransAt (g : MVarId) (ctx : Simp.Context) (fvarIdsToSimp : Array FVarId)
    (simplifyTarget := true) (useSimp := true) :
    MetaM (Option (Array FVarId × MVarId)) := g.withContext do
  g.checkNotAssigned `norm_num
  let mut g := g
  let mut toAssert := #[]
  let mut replaced := #[]
  for fvarId in fvarIdsToSimp do
    let localDecl ← fvarId.getDecl
    let type ← instantiateMVars localDecl.type
    let ctx := { ctx with simpTheorems := ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId) }
    let r ← deriveSimp ctx useSimp type
    match r.proof? with
    | some _ =>
      let some (value, type) ← applySimpResultToProp g (mkFVar fvarId) type r
        | return none
      toAssert := toAssert.push { userName := localDecl.userName, type, value }
    | none =>
      if r.expr.isConstOf ``False then
        g.assign (← mkFalseElim (← g.getType) (mkFVar fvarId))
        return none
      g ← g.replaceLocalDeclDefEq fvarId r.expr
      replaced := replaced.push fvarId
  if simplifyTarget then
    let res ← g.withContext do
      let target ← instantiateMVars (← g.getType)
      let r ← deriveSimp ctx useSimp target
      let some proof ← r.ofTrue
        | some <$> applySimpResultToTarget g target r
      g.assign proof
      pure none
    let some gNew := res | return none
    g := gNew
  let (fvarIdsNew, gNew) ← g.assertHypotheses toAssert
  let toClear := fvarIdsToSimp.filter fun fvarId ↦ !replaced.contains fvarId
  let gNew ← gNew.tryClearMany toClear
  return some (fvarIdsNew, gNew)

open Qq Lean Meta Elab Tactic Term

/-- Constructs a simp context from the simp argument syntax. -/
def getSimpContext (args : Syntax) (simpOnly := false) :
    TacticM Simp.Context := do
  let simpTheorems ←
    if simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) {} else getSimpTheorems
  let mut { ctx, starArg } ← elabSimpArgs args (eraseLocal := false) (kind := .simp)
    { simpTheorems := #[simpTheorems], congrTheorems := ← getSimpCongrTheorems }
  unless starArg do return ctx
  let mut simpTheorems := ctx.simpTheorems
  for h in ← getPropHyps do
    unless simpTheorems.isErased (.fvar h) do
      simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
  pure { ctx with simpTheorems }

open Elab.Tactic in

/--
Elaborates a call to `norm_num only? [args]` or `norm_num1`.
* `args`: the `(simpArgs)?` syntax for simp arguments
* `loc`: the `(location)?` syntax for the optional location argument
* `simpOnly`: true if `only` was used in `norm_num`
* `useSimp`: false if `norm_num1` was used, in which case only the structural parts
  of `simp` will be used, not any of the post-processing that `simp only` does without lemmas
-/
-- FIXME: had to inline a bunch of stuff from `mkSimpContext` and `simpLocation` here
def elabFunTrans (args : Syntax) (loc : Syntax)
    (simpOnly := false) (useSimp := true) : TacticM Unit := do
  let ctx ← getSimpContext args (!useSimp || simpOnly)
  let g ← getMainGoal
  let res ← match expandOptLocation loc with
  | .targets hyps simplifyTarget => funTransAt g ctx (← getFVarIds hyps) simplifyTarget useSimp
  | .wildcard => funTransAt g ctx (← g.getNondepPropHyps) (simplifyTarget := true) useSimp
  match res with
  | none => replaceMainGoal []
  | some (_, g) => replaceMainGoal [g]


open Lean.Parser.Tactic  -- Meta.NormNum

elab (name := funTrans) "fun_trans" only:&" only"? args:(simpArgs ?) loc:(location ?) : tactic =>
  elabFunTrans args loc (simpOnly := only.isSome) (useSimp := true)

-- /-- Basic version of `norm_num` that does not call `simp`. -/
-- elab (name := normNum1) "norm_num1" loc:(location ?) : tactic =>
--   elabNormNum mkNullNode loc (simpOnly := true) (useSimp := false)

