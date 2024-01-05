import SciLean

import SciLean.Core.Functions.ArgMinMax
import SciLean.Modules.SolversAndOptimizers.GradientDescent

open SciLean

open NotationOverField 
set_default_scalar Float


syntax (name:=arrayTypeLiteral') (priority:=high) " ⊞[" term,* "] " : term


def List.toArrayType (l : List α) {n : USize} (h : l.length = n.toNat) [PlainDataType α] : α^[n] := 
  ⊞ i => l.get ⟨i.1.toNat,sorry_proof⟩

open Lean Meta Elab Term Qq
macro_rules 
 | `(⊞[ $x:term, $xs:term,* ]) => do 
   let n := Syntax.mkNumLit (toString (xs.getElems.size + 1))   
   `(List.toArrayType [$x,$xs,*] (n:=$n) sorry_proof)
  -- let n := Syntax.mkNumLit (toString xs.getElems.size)
  -- `(term| ListN.toArrayType (arrayType #[$xs,*] $n (by rfl))

-- @[app_unexpander Array.toArrayType] 
-- def unexpandArrayToArrayType : Lean.PrettyPrinter.Unexpander
--   | `($(_) #[$ys,*] $_*) =>     
--     `(⊞[$ys,*])
--   | _  => throw ()

def g := ⊞[0.0, -9.81]

def ballisticMotion (x v : Float^[2]) := (v, g - (5.0 + ‖v‖₂) • v)

#generate_revDeriv ballisticMotion x v
  prop_by unfold ballisticMotion; fprop
  trans_by unfold ballisticMotion; ftrans


noncomputable
approx aimToTarget (v₀ : Float^[2]) (optimizationRate : Float) := 
  λ (T : Float) (target : Float^[2]) =>
  let shoot := λ (v : Float^[2]) =>
                 odeSolve (t₀ := 0) (x₀ := ((0:Float^[2]),v)) (t := T)
                   (f := λ (t : Float) (x,v) => ballisticMotion x v) |>.fst
  Function.invFun shoot target
by
  
  -- reformulate inverse as minimization and apply gradient descent
  conv =>
    enter [2,T,target,shoot]
    rw [invFun_as_min_norm2 (R:=Float) _ _ sorry_proof]
    rw [argminFun.approx.gradientDescent v₀ optimizationRate]
  
  approx_limit n := sorry_proof

  unfold scalarGradient
  set_option trace.Meta.Tactic.simp.discharge true in
  set_option trace.Meta.Tactic.ftrans.step true in
  set_option trace.Meta.Tactic.ftrans.theorems true in
  set_option trace.Meta.Tactic.simp.unify true in
  ftrans


#exit  
  approx_limit 1; intro gdSteps
  clean_up

  unsafe_ad; ignore_fun_prop
  
  -- run automatic differentiation, it gets blocked on `ℛ shoot`
  conv =>
    enter [1]
    autodiff; autodiff; autodiff; autodiff; autodiff
  
  -- Precompute forward pass with midpoint method and 50 steps on the interval [0,T] and used linear interpolation
  conv =>
    enter_let x
    conv =>
      rw[odeSolve_fixed_dt_on_interval
          midpoint_step
          linearInterpolate1D
          T]
  
  approx_limit 50; intro forwardSteps; clean_up
  
  -- Use midpoint method with 50 steps on the backward pass
  conv => 
    --enter_let Rxy₂
    rw[odeSolve_fixed_dt midpoint_step]
      
  approx_limit 50; intro backwardSteps; clean_up


/-- Generate `n` trajectory points in the interval [0,T] -/
def shotTrajectoryPoints (n : ℕ) (T : ℝ) (v : ℝ×ℝ) : Array ((ℝ×ℝ)×(ℝ×ℝ)) := 
  odeSolve_fixed_dt_array (λ (t : ℝ) (x,v) => ballisticMotion x v)
    midpoint_step n 0 (0,v) T

/-- Do one step of optimization -/
def aimStep (target : ℝ×ℝ) (v₀ : ℝ×ℝ) := aimToTarget v₀ (5.0:ℝ) (1:ℝ) target
