
import SciLean
import SciLean.Functions.OdeSolve
import SciLean.Functions.GradientDescent
import SciLean.Solver.Solver 
import SciLean.Core.UnsafeAD
import SciLean.Tactic.LetUtils
import SciLean.Tactic.LetEnter
import SciLean.Tactic.Basic
import SciLean.Profile

open SciLean

def g : ℝ×ℝ := (0, -9.81)

def ballisticMotion (x v : ℝ×ℝ) := (v, g - (5 + ‖v‖) • v)

function_properties ballisticMotion (x v : ℝ×ℝ)
argument (x,v) [UnsafeAD]
  def ∂, def ∂†, def ℛ

#print ballisticMotion.arg_xv.differential

approx aimToTarget (v₀ : ℝ×ℝ) (optimizationRate : ℝ) := 
  λ (T : ℝ) (target : ℝ×ℝ) =>
  let shoot := λ (v : ℝ×ℝ) =>
                 odeSolve (t₀ := 0) (x₀ := ((0:ℝ×ℝ),v)) (t := T)
                   (f := λ (t : ℝ) (x,v) => ballisticMotion x v) |>.fst
  shoot⁻¹ target
by
  clean_up
  
  -- reformulate inverse as minimization and apply gradient descent
  conv =>
    enter [1,T,shoot,target]
    rw [invFun_as_argmin _ _ sorry_proof]
    rw [argminFun.approx.gradientDescent v₀ optimizationRate]
  
  approx_limit 1; intro gdSteps
  clean_up

  unsafe_ad; ignore_fun_prop
  
  -- run automatic differentiation, it gets blocked on `ℛ shoot`
  conv =>
    enter [1]
    autodiff; autodiff
  
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
