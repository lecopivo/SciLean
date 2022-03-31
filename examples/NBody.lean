import SciLean.Basic
import SciLean.Mechanics
import SciLean.Tactic.BubbleLimit
import SciLean.Solver.Impl

open SciLean

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 500000

section SNorm

  variable {X} [Hilbert X]

  def snorm (ε : ℝ) (x : X) : ℝ := Math.sqrt (∥x∥² + ε^2)

  notation "∥" x "∥{" ε "}" => snorm ε x

  @[simp]
  theorem snorm.is_norm_at_zero (x : X) : snorm 0 x = ∥x∥ := sorry

  instance snorm.is_smooth (ε : ℝ) [NonZero ε] : IsSmooth (λ x : X => snorm ε x) := sorry
  instance snorm.is_positive [NonZero ε] (x : X) : IsPos (snorm ε x) := sorry

  @[reducible]
  instance snorm.is_atomic_smooth (ε : ℝ) [NonZero ε] : AtomicSmoothFun (λ x : X => snorm ε x) where
    df := λ x dx => (1/snorm ε x) * ⟪x, dx⟫
    is_smooth := sorry
    is_df := sorry

  variable (ε : ℝ) [NonZero ε]

  @[simp]
  theorem snorm.grad
    : ∇ (snorm ε) = λ x : X => (1/snorm ε x) * x :=
  by
    simp[gradient]; unfold_atomic; simp
    done

  instance snorm.is_smooth_of_pow {X Y} [Vec X] [Hilbert Y] (α : ℝ) (f : X → Y) [IsSmooth f]
    : IsSmooth (λ x => (snorm ε (f x))^α) := sorry
  
  @[simp]
  theorem snorm.diff_of_pow {X Y} [Vec X] [Hilbert Y] (α : ℝ) (f : X → Y) [IsSmooth f]
    : δ (λ x => (snorm ε (f x))^α) = λ x dx : X => α * ((snorm ε (f x))^(α-2)) * ⟪f x, δ f x dx⟫ := 
  by
    admit

  -- TODO: a bit dubious in the current formulation
  theorem snorm.norm_approx (x : X) 
    : ∥x∥ = limit λ n => (snorm (ε/n) x) := sorry

  def solver_limit {X} [Vec X] {g : ℕ → X} (n₀ : ℕ) (impl : (n : ℕ) → Solver λ f => f = g n)
    : Solver (λ f => f = limit g) := Solver.approx (λ n f => f = g n) sorry n₀ impl "" ""

  def solver_finish {X} [Vec X] {g : X}
    : Solver (λ f => f = g) := Solver.exact g rfl

  example (n : Nat) (x : Fin n → X) [NonZero n] : Solver (λ f => f = (∇ λ x : Fin n → X => ∑ i j, ∥x i - x j∥^(-1:ℝ))) :=
  by
    simp only [snorm.norm_approx ε]

    conv => enter[1,f,2]; bubble_lim; (tactic => simp; admit)
    apply solver_limit 1; intro E
    
    simp[gradient]
    
    conv =>
      enter [1,f,2,x,1,j,2,1,i]
      rw[!?((snorm (ε / E) (x i - x j) ^ (-(1 + 2) : ℝ)) * (x i - x j)
            =
            - ((snorm (ε / E) (x j - x i) ^ (-(1 + 2 : ℝ))) * (x j - x i)))]
      
    simp

    apply solver_finish
    
end SNorm


notation x "[[" i "]]" => PowType.powType.getOp x i

def H (n : Nat) (ε : ℝ) (m : ℝ^n) (x p : ((ℝ^(3:ℕ))^n)) := (∑ i, (1/(2*m[i])) * ∥p[i]∥²) + (∑ i j, (m[i]*m[j]) * ∥x[i] - x[j]∥{ε}^(-1:ℝ))

def solver (n : Nat) [NonZero n] (ε : ℝ) [NonZero ε] (m : ℝ^n) 
: Solver (λ f => f = ode_solve (HamiltonianSystem (H n ε m))) :=
by
  -- Unfold Hamiltonian definition and compute gradients
  simp[HamiltonianSystem, H]
  
  simp[gradient]

  -- Here I want to do some rewrites

  -- Apply RK4 method
  rw [ode_solve_fixed_dt runge_kutta4_step]
  conv => enter[1,f,2]; bubble_lim; (tactic => simp; admit)
  apply solver_limit 1; intro E
    
  apply solver_finish
