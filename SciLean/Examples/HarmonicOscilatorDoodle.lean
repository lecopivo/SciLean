import SciLean.Basic

import SciLean.Mechanics.Basic

abbrev V := ℝ × ℝ

-- 1/(2*m) * ⟨p,p⟩ +
def H (m k : ℝ) (x p : V) := 1/(2*m) * ⟨p,p⟩ + k/2 * ⟨x, x⟩  --* (Math.exp (Math.exp ⟨x, x⟩ * ⟨x, x⟩))

-- Ideal definition
-- def H (m : ℝ) := λₛ (k : ℝ) (x p : V) => 1/(2*m) * ⟨p,p⟩ + k/2 * ⟨x,x⟩

def dual_intro {U} [Vec U] (f : U → ℝ) : dual f = dual (λ v => f v) := by simp
def diff_intro {X Y} [Vec X] [Vec Y] (f : X → Y) : δ f = λ x dx => δ f x dx := by simp
def comp_dual_intro {α X} [Vec X] (f : α → (X → ℝ)) : comp dual f = (λ x => dual (f x)) := by funext x; simp; done
def impl_intro {X Y : Type} (f : X → Y) : Impl f = Impl (λ x => f x) := by simp


@[simp] def prod_sum' {X Y} [Add X] [Add Y] [Add (X×Y)] (x x' : X) (y y' : Y) : (x, y) + (x', y') = (x + x', y + y') := sorry

#check ode_solve (HamiltonianSystem (H _ _))

set_option synthInstance.maxHeartbeats 5000
set_option synthInstance.maxSize 1000

def solver (m k : ℝ) (steps : Nat) : SpecImpl (ode_solve (HamiltonianSystem (H m k))) :=
by 
  -- solver_check (m>0) "Mass has to be nonzero." 

  simp [HamiltonianSystem, H, symp, uncurry];
  rmlamlet; rw [diff_intro]; simp; rmlamlet; rw [comp_dual_intro]; simp; -- autograd    
  -- algebraic_simplify
  conv => 
    enter [1,1,xp];
    simp;
    rw [prod_sum]
    rw [prod_sum]
    rw [prod_sum]
    -- rw [prod_sum]
    -- rw [prod_sum]
    -- rw [prod_sum]
    -- rw [prod_sum]
    simp
    rw [add_zero]
    rw [zero_add]
    rw [add_zero]
    -- rw [add_zero]
    -- rw [zero_add]
    rw [add_same_4]
    rw [add_same_4]
    -- rw [add_same_4]
    -- rw [add_same_4]

    rw [smul_smul_mul]
    rw [smul_smul_mul]
    -- rw [smul_smul_mul]
    -- rw [smul_smul_mul]
    -- rw [smul_smul_mul]
    -- rw [smul_smul_mul]
    -- rw [smul_smul_mul]
    -- rw [smul_smul_mul]
    -- rw [smul_smul_mul]
    -- rw [smul_smul_mul]
    -- rw [smul_smul_mul]
    -- rw [smul_smul_mul]
  
  simp
  

  -- rw [ode_solve_with_fixed_step forward_euler]
  -- lift_limit steps "Number of ODE solver steps."
  -- finish_impl

  admit


