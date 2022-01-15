import SciLean.Basic
import SciLean.Mechanics

set_option synthInstance.maxHeartbeats 5000

open Function
namespace SciLean

variable (n : Nat) [NonZero n]


example : Table.Trait (ℝ^n) := by infer_instance
example : Add $ Table.Trait.Value (ℝ^n) := by infer_instance

def foo1 : Impl (∇ (λ x : ℝ^n => ∑ i, x[i])) := 
by
  autograd
  finish_impl

@[simp]
theorem sum_intro {C ι κ α}
  (f : ι → κ → α) [Table C κ α] [Table.Intro C] [Vec α] [Enumtype ι]
  : (∑ i, (Table.intro (f i) : C)) = (Table.intro (∑ i, f i) : C)
  := 
by
  admit

#check instHAdd
               
@[simp]
theorem add_intro {C ι α} [Table C ι α]
  (f g : ι → α) [Table.Intro C] [Add α] 
  : HAdd.hAdd (self := instHAdd) (Table.intro λ i : ι => f i : C) (Table.intro λ i : ι => g i : C) = (Table.intro λ i => f i + g i : C)
  := 
by
  admit

@[simp] 
theorem sum_into_lambda {X Y ι} [Enumtype ι] [Vec Y]
  (f : ι → X → Y)
  : (∑ i, λ j => f i j) = (λ j => ∑ i, f i j)
  := sorry

@[simp] 
theorem sum_of_sum {X ι} [Enumtype ι] [Vec X]
  (f g : ι → X)
  : (∑ i, f i + g i) = (∑ i, f i) + (∑ i, g i)
  := sorry

@[simp] 
theorem sum_of_kron_1 {n} [NonZero n]
  (g : Fin n → Fin n) [IsInv g]
  (j : Fin n)
  : (∑ i, kron (g i) j) = 1
  := sorry

@[simp] 
theorem sum_of_kron_2 {n} [NonZero n]
  {X} [Vec X] (f : Fin n → ℝ → X) [∀ i, IsLin (f i)]
  (g : Fin n → Fin n) [IsInv g]
  (j : Fin n)
  : (∑ i, f i (kron (g i) j)) = f (g⁻¹ j) 1
  := sorry

@[simp] 
theorem sum_of_kron_3 {n} [NonZero n]
  {X} [Vec X] (f : ℝ → α → X) [IsLin f]
  (h : Fin n → α)
  (g : Fin n → Fin n) [IsInv g]
  (j : Fin n)
  : (∑ i, f (kron (g i) j) (h i)) = f 1 (h (g⁻¹ j))
  := sorry

theorem sum_of_kron_4 {n} [NonZero n]
  {X} [Vec X] (f : α → ℝ → β → X)
  (h1 : Fin n → α) (h2 : Fin n → β)
  (g : Fin n → Fin n) [IsInv g]
  (j : Fin n)
  : (∑ i, f (h1 i) (kron (g i) j) (h2 i)) = f (h1 (g⁻¹ j)) 1 (h2 (g⁻¹ j))
  := sorry

@[simp] 
theorem kron_mul_assoc {i j : Fin n} (x y : ℝ) : (kron i j) * x * y = (kron i j) * (x * y) 
  := sorry

@[simp] 
theorem kron_neg {i j : Fin n} : -(kron i j) = (kron i j) * (-1) 
  := sorry

@[simp] 
theorem kron_neg_mul {i j : Fin n} (x : ℝ) : -(kron i j * x) = kron i j * (-x) 
  := sorry

example [NonZero n] (j : Fin n) 
  : (∑ i : Fin n, kron (i+1) j) = 1
  :=
  by simp done


example [NonZero n] (j : Fin n) 
  : (∑ i : Fin n, i * (kron (i+1) j)) = (j-1)
  :=
  by simp done

example [NonZero n] (j : Fin n) 
  : (∑ i : Fin n, (kron (i+1) j) * i) = (j-1)
  :=
  by simp done

example (y : ℝ^n) : (λ (x : ℝ^n) i => x[i] * y[i])† = 0 
  :=
  by
    -- rw[Adjoint.adjoint_of_comp_parm]
    simp
    conv =>
      enter [1,y,1,i]
      rw[Adjoint.adjoint_of_comp_parm]
    funext f
    simp
    admit

-- set_option trace.Meta.Tactic.simp true in
def foo2 : Impl (∇ (λ x : ℝ^n => ∑ i, x[i+1])) 
  := 
  by 
    autograd
    finish_impl

-- set_option trace.Meta.Tactic.simp true in
def foo2' : Impl (∇ (λ x : (Fin n → ℝ) => ∑ i, x (i+1))) 
  := 
  by
    autograd
    finish_impl

-- set_option trace.Meta.Tactic.simp true in
def foo3 : Impl (∇ (λ x : ℝ^n => ∑ i, x[i] * x[i])) := 
by
  autograd
  conv =>
    enter [1,x,1,1,i]
    rw[Adjoint.adjoint_of_comp_parm]
  simp
  finish_impl

variable (n : Nat) [NonZero n]

def H (m k : ℝ) (x p : ℝ^n) := 
  let Δx := (1 : ℝ)/(n : ℝ)
  (Δx/(2*m)) * ∥p∥² + (Δx * k/2) * (∑ i, ∥x[i] - x[i-1]∥²)  -- + 2 * k * (∑ i, ∥(∥x[i] - x[i-1]∥² - 0.01)∥²)

-- set_option trace.Meta.isDefEq true in
def solver (m k : ℝ) (steps : Nat) : Impl (ode_solve (HamiltonianSystem (H n m k))) :=
by
  -- Unfold Hamiltonian definition and compute gradients
  simp[HamiltonianSystem, H, swap];
  autograd
  autograd

  -- Apply RK4 method
  rw [ode_solve_fixed_dt runge_kutta4_step]
  lift_limit steps "Number of ODE solver steps."; admit; simp
    
  finish_impl


def wave_equation_main : IO Unit := do

  let steps := 1
  let m := 1.0
  let k := 100000.0

  let N : Nat := 100
  let evolve ← (solver N m k steps).assemble

  let t := 1.0
  let x₀ : (ℝ^N) := Table.intro λ (i : Fin N) => (Math.sin ((i : ℝ)/10))
  let p₀ : (ℝ^N) := Table.intro λ i => (0 : ℝ)
  let mut (x,p) := (x₀, p₀)

  for i in [0:1000] do
  
    (x, p) := evolve 0.1 (x, p)

    let M : Nat := 20
    for (m : Nat) in [0:M] do
      for (n : Nat) in [0:N] do
        
        let xi := x[n]
        if (2*m - M)/(M : ℝ) - xi < 0  then
          IO.print "x"
        else
          IO.print "."

      IO.println ""
  
-- #eval wave_equation_main

