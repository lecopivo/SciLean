import SciLean
import SciLean.Functions.OdeSolve
import SciLean.Solver.Solver 
import SciLean.Core.UnsafeAD
import SciLean.Tactic.LetUtils
import SciLean.Tactic.LetEnter
import SciLean.Tactic.Basic
import SciLean.Profile

open SciLean
  

def g : ℝ×ℝ := (0, -9.81)


theorem invFun_as_argmin {X Y} [Nonempty X] [Hilbert X] [Hilbert Y] (f : X → Y) (y : Y) (hf : IsInv f)
  : f⁻¹ y = argmin x, ‖f x - y‖² := sorry_proof


def gradientDescent [Vec X] (gradf : X → X) (x₀ : X) (s : ℝ) (steps : Nat) : X := Id.run do
  let mut x := x₀
  for i in [0:steps] do
    x := x - s • gradf x
  x

theorem argminFun.approx.gradientDescent {X} [Hilbert X] {f : X → ℝ} (x₀ : X) (s : ℝ)
  : argmin x, f x 
    =
    limit λ n => gradientDescent (∇ f) x₀ s n
  := sorry_proof

theorem gradient_as_revDiff {X} [SemiHilbert X] (f : X → ℝ) 
  : (∇ λ x => f x) = λ x => (ℛ f x).2 1 := by rfl

theorem hold_fun_swap {α β} (f : α → β) (x : α)
  : f (hold x) = hold (f x) := by unfold hold; rfl

theorem hold_arg_swap {α β} (f : α → β) (x : α)
  : hold f x = hold (f x) := by unfold hold; rfl

def balisticMotion (x v : ℝ×ℝ) := (v, g  - (5 + ‖v‖) • v)

function_properties balisticMotion (x v : ℝ×ℝ)
argument (x,v) [UnsafeAD] [IgnoreFunProp]
  abbrev ∂ by unfold balisticMotion; fun_trans only; clean_up_simp,
  def ∂† by unfold balisticMotion; fun_trans only; clean_up_simp,
  def ℛ by unfold balisticMotion; fun_trans only; clean_up_simp
argument x
  IsSmooth,
  HasAdjDiff,
  abbrev ∂† by unfold balisticMotion; fun_trans only; clean_up_simp,
  abbrev ℛ by unfold balisticMotion; fun_trans only; clean_up_simp
argument v [UnsafeAD]
  IsSmooth,
  HasAdjDiff,
  def ∂† by unfold balisticMotion; fun_trans only; clean_up_simp,
  def ℛ by unfold balisticMotion; fun_trans only; clean_up_simp


approx aimToTarget (v₀ : ℝ×ℝ) (optimizationRate : ℝ) := 
  λ (T : ℝ) (target : ℝ×ℝ) =>
  let shoot := hold $ λ (t : ℝ) (v : ℝ×ℝ) =>
                 odeSolve (t₀ := 0) (x₀ := ((0:ℝ×ℝ),v)) (t := t)
                   (f := λ (t : ℝ) (x,v) => balisticMotion x v)
  (λ v => (shoot T v).1)⁻¹ target
by
  clean_up
  
  -- reformulate inverse as minimization and apply gradient descent
  conv =>
    enter [1,shoot,T,target]
    rw [invFun_as_argmin _ _ sorry_proof]
    rw [argminFun.approx.gradientDescent v₀ optimizationRate]
  
  approx_limit 1; intro gdSteps
  clean_up

  rw'[gradient_as_revDiff]

  unsafe_ad; ignore_fun_prop

  -- run automatic differentiation, it gets blocked on `ℛ shoot`
  conv =>
    enter [1]
    fun_trans only
      
  -- deal with `ℛ shoot` manually
  conv =>
    enter[1]; ext
    enter[T,target]
    let_add Rshoot (ℛ (shoot T))
    enter [RShoot]
    rw[(sorry_proof : ℛ (shoot T) = Rshoot)]
  
  let_unfold shoot
 
  -- run automatic differentiation on `shoot`, this formulates the adjoint problem
  conv =>
    enter [1]
    enter_let Rshoot
    dsimp
    rw[hold_arg_swap, hold_fun_swap reverseDifferential]
    fun_trans only; clean_up_simp

  -- The adjoint problem consists of two steps, forward and backward pass.
  -- We need to pick discretization for both of those passes.
  
  -- Precompute forward pass with midpoint method and 50 steps on the interval [0,T] and used linear interpolation
  conv =>
    enter [1]
    enter_let x
    conv =>
      rw[odeSolve_fixed_dt_on_interval
          midpoint_step
          linearInterpolate1D
          T]
  
  approx_limit 50; intro forwardSteps; clean_up
  
  -- Use midpoint method with 50 steps on the backward pass
  conv => 
    enter [1]
    -- enter_let Rfx₂
    enter [dx₀']
    rw[odeSolve_fixed_dt midpoint_step]
      
  approx_limit 50; intro backwardSteps; clean_up
  apply Approx.exact


/-- Generate `n` trajectory points in the interval [0,T] -/
def shotTrajectoryPoints (n : ℕ) (T : ℝ) (v : ℝ×ℝ) : Array ((ℝ×ℝ)×(ℝ×ℝ)) := 
  odeSolve_fixed_dt_array (λ (t : ℝ) (x,v) => balisticMotion x v)
    midpoint_step n 0 (0,v) T

/-- Do one step of optimization -/
def aimStep (target : ℝ×ℝ) (v₀ : ℝ×ℝ) := aimToTarget v₀ (5.0:ℝ) (1:ℝ) target
