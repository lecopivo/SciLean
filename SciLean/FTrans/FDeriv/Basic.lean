import SciLean.Tactic.FTrans.Basic

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear

import SciLean.Tactic.LSimp.Elab

namespace SciLean

open Filter Asymptotics ContinuousLinearMap Set Metric


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

set_option linter.unusedVariables false

variable {K : Type _} [NontriviallyNormedField K]

variable {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
variable {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
variable {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]

variable {ι : Type _} [Fintype ι]

variable {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]


-- #check ContinuousLinearMap.mk

-- def _root_.ContinuousLinearMap.mk' (f : X → Y) (h₁ : IsLinearMap K f := by sorry) (h₂ : Continuous f := by continuity)
--   : X →L[K] Y := ⟨⟨⟨f, h₁.map_add⟩, h₁.map_smul⟩, by aesop⟩

-- #check ContinuousLinearMap.mk' (K := K) fun (x : X) => x

-- macro " fun " x:ident " →L[" R:term "] " b:term : term => `(ContinuousLinearMap.mk' (K:=$R) fun $x => $b)


@[ftrans]
theorem fderiv.id_rule 
  : (fderiv K fun x : X => x) = fun _ => ContinuousLinearMap.id K X -- fun _ => fun dx →L[K] dx 
  := by funext x; simp


@[ftrans]
theorem fderiv.const_rule (x : X)
  : (fderiv K fun _ : Y => x) = fun _ => 0
  := by funext x; simp


theorem fderiv.let_rule_at
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : X → Y → Z) (hf : DifferentiableAt K (fun xy : X×Y => f xy.1 xy.2) (x, g x))
  : (fderiv K 
      fun x : X => 
        let y := g x 
        f x y) x
    =
    let y  := g x
    let dg := fderiv K g x
    let df := fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y)
    df.comp ((id K X).prod dg)
  := by sorry_proof


theorem fderiv.let_rule
  (g : X → Y) (hg : Differentiable K g)
  (f : X → Y → Z) (hf : Differentiable K fun xy : X×Y => f xy.1 xy.2)
  : (fderiv K fun x : X =>
       let y := g x
       f x y)
    =
    fun x =>
      let y  := g x
      let dg := fderiv K g x
      let df := fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y)
      df.comp ((id K X).prod dg)
    -- fun x => fun dx →L[K]
    --   let y  := g x
    --   let dy := fderiv K g x dx
    --   fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx,dy)
  := by sorry_proof


theorem fderiv.pi_rule_at
  (x : X)
  (f : (i : ι) → X → E i) (hf : ∀ i, DifferentiableAt K (f i) x)
  : (fderiv K fun (x : X) (i : ι) => f i x) x
    = 
    ContinuousLinearMap.pi fun i => fderiv K (f i) x
    -- fun x => fun dx →L[K] fun i =>
    --   fderiv K (f i) x dx
  := fderiv_pi hf


theorem fderiv.pi_rule
  (f : (i : ι) → X → E i) (hf : ∀ i, Differentiable K (f i))
  : (fderiv K fun (x : X) (i : ι) => f i x)
    = 
    fun x => 
      ContinuousLinearMap.pi fun i => fderiv K (f i) x
    -- fun x => fun dx →L[K] fun i =>
    --   fderiv K (f i) x dx
  := by funext x; apply fderiv_pi (fun i => hf i x)


--------------------------------------------------------------------------------


@[ftrans]
theorem _root_.HAdd.hAdd.arg_a4a5.fderiv_comp
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (fderiv K fun x => f x + g x)
    =
    fderiv K f + fderiv K g
  := sorry

-- @[ftrans]
-- theorem _root_.HAdd.hAdd.arg_a5.fderiv_comp
--   (x : X) (f : X → Y) (hf : Differentiable K f)
--   : (fderiv K (HAdd.hAdd)
--     =
--     fderiv K f + fderiv K g 
--   := sorry


@[simp]
theorem _root_.HAdd.hAdd.arg_a4a5.Differentiable
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : Differentiable K fun x => f x + g x
  := sorry


-- Register `fderiv` as function transformation --------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq

open Lean Elab Term
def fderiv.ftransInfo : FTrans.Info where
  getFTransFun? e := 
    if e.isAppOf ``fderiv then

      if let .some f := e.getArg? 8 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``fderiv then
      e.modifyArg (fun _ => f) 8 
    else          
      e

  applyLambdaLetRule e :=
    match e.getArg? 8 with
    | .some (.lam xName xType 
              (.letE yName yType yVal body _) bi) => do

      let g := Expr.lam xName xType yVal bi  
      let f := Expr.lam xName xType (Expr.lam yName yType body default) bi  

      let K := e.getArg! 0

      let hgType ← mkAppM ``Differentiable #[K,g]
      let hfType ← mkAppM ``Differentiable #[K, ← mkUncurryFun 2 f]
      let hg ← mkSorry hgType false -- mkFreshExprMVar hgType
      -- let hg ← mkFreshExprMVar hgType
      -- let _ ← Elab.runTactic hg.mvarId! (← `(tactic| aesop))
      let hf ← mkSorry hfType false
      
      
      let proof ← mkAppM ``fderiv.let_rule #[g,hg,f,hf]
      let rhs := (← inferType proof).getArg! 2

      let goal : MVarId := sorry


      dbg_trace "g = {← ppExpr g}"
      dbg_trace "f = {← ppExpr f}"
      dbg_trace "rhs = {← ppExpr rhs}"
      return .some (.visit (.mk rhs proof 0))
    | _ => return none

  applyLambdaLambdaRule e := return none

  discharger := 
    let a : MacroM Syntax := `(tactic| simp)
    sorry

#check MacroM
-- do
--     let goal ← mkFreshExprMVar e
--     try 
      
--       let (_, _) ← Elab.runTactic goal.mvarId! (← `(tactic| aesop))
--       let result ← instantiateMVars goal
--       if result.hasExprMVar then
--         return none
--       else
--         return none
--     catch _ => 
--       return none
    -- match e.getArg? 8 with
    -- | .some (.lam xName xType 
    --           (.lam yName yType yVal body _) bi) => do

    -- | _ => return none



#eval show Lean.CoreM Unit from do
  FTrans.infoExt.insert ``fderiv fderiv.ftransInfo

example :
  (fderiv K λ x : X => x)
  =
  fun _ => 1
:= 
  by ftrans only; rfl

example (x : X) :
  (fderiv K λ _ : Y => x)
  =
  fun _ => 0
:= 
  by ftrans only

theorem hihi (x : X) :
  (fderiv K λ _ : Y => x)
  =
  fun _ => 0
:= 
  by ftrans only

set_option trace.Meta.Tactic.ftrans.step true
set_option trace.Meta.Tactic.simp.rewrite true
set_option trace.Meta.Tactic.simp.discharge true


example :
  (fderiv K λ x : X => (x + x) + (x + x) + (x + x))
  =
  fun _ => 0
  := by
  ftrans only
  sorry

example (x' : X) :
  (fderiv K (HAdd.hAdd x'))
  =
  fun _ => 0
  := by
  ftrans only
  set_option trace.Meta.Tactic.simp.unify true in
  ftrans only
  rw [HAdd.hAdd.arg_a4a5.fderiv_comp _ _  (by simp) (by simp)]
  sorry

#exit
example (x' : X) :
  (fderiv K λ x : X => x + x')
  =
  fun _ => 0
  := by
 ftrans only
 sorry


#exit

-- set_option pp.all true 
example :
  (fderiv K λ x : X => 
    let y := x + x
    x + y)
  =
  fun _ => 0
:= by
   ftrans only
   ftrans only
   sorry

-- example : Differentiable K fun x : (X×X) => x.1 + x.2 := by continuity



example : (Differentiable K fun x : X => x) = True := by simp
theorem hoho : (Differentiable K fun x : X => 
        let y := x + x
        y) = True := by aesop

-- example : Continuous fun x : (X×X) => x.1 + x.2 := by continuity
