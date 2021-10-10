import SciLean.Basic
import SciLean.Mechanics

set_option synthInstance.maxHeartbeats 50000
set_option synthInstance.maxSize 10000

abbrev V := ℝ × ℝ
abbrev Q := ℝ

def g : ℝ := 9.81
def L' (m k : ℝ) (x v : V) := (m/2) * ⟨v,v⟩ - m * g * x.2

def parm (l : ℝ) (θ : Q) : V := (l * Math.sin θ, -l * Math.cos θ)
def L (m k l : ℝ) (θ ω : Q) := L' m k (parm l θ) (δ (parm l) θ ω)

-- def solver (m k l : ℝ) (steps : Nat) : Impl (ode_solve (LagrangianSystem (L m k l))) :=
-- by
def solver (m k l : ℝ) (steps : Nat) : Impl (λ x v : Q => (L m k l) x v) :=
by

  -- impl_assume (l>0) "Pendulum length has to be non zero."
  -- impl_assume (m>0) "Mass has to be non zero."
  
  -- transforms lagrangian to hamiltonian - i.e. preform Legandre transform and simplifies
  simp [LagrangianSystem, L, L', parm, gradient]

  rmlamlet
  conv in (differential _) =>
    intro x dx
    simp

  simp
 
  rmlamlet; simp

  conv => 
    enter [1,x,v]
    simp
  simp
  finish_impl


-- def test : (λ x : Nat => id (id x)) = λ x => x := by
--   conv =>      --- error: 'pattern' conv tactic failed, pattern was not found
--     pattern (id _)
--     . simp


def solver_1 (m k l : ℝ) (steps : Nat) : Impl (λ x v : Q => ∇(swap (L m k l) v) x) :=
by
  conv in (L _ _ _) =>
    enter [θ, ω]
    simp [L, L', parm]
    rmlamlet
    simp

  simp [gradient]
  
  conv =>
    enter [1, θ, ω]
    rmlamlet
    simp


  finish_impl

  
def solver_2 (m k l : ℝ) (steps : Nat) : Impl (λ x v : Q => ∇(δ (L m k l) x v) v) :=
by
  conv in (L _ _ _) =>
    enter [θ, ω]
    simp [L, L', parm]
    rmlamlet
    simp

  simp [gradient]
  
  conv =>
    enter [1, θ, ω]
    rmlamlet
    pattern (differential _ _)
    . pattern (differential _ _ _)
      enter [dω]; simp

  conv =>
    enter [1, θ, ω, 1, dw]
    rmlamlet
    simp
  .

  finish_impl

  
def solver_3 (m k l : ℝ) (steps : Nat) : Impl (λ x v : Q => δ(∇((L m k l) x)) v) :=
by
  simp [gradient]
  conv  =>
    enter [1,x,v]
    pattern (differential _)
    enter [v,1]
    pattern (L _ _ _ _)
    simp [L, L']
    enter [ω,1]
    pattern (differential _ _ _)
    simp [parm]
    rmlamlet
    simp

  conv =>
    enter [1,x,v,1,2]
    rmlamlet
    enter [x,dx]
    simp
    enter [2]
    
  conv =>
    enter [1,x,v,1,u]
    simp
    rmlamlet
    simp

  conv =>
    enter [1,x,v]
    enter [p]
    rmlamlet
    simp
  
  finish_impl


def test2 : (Function.comp id id) = λ x : Nat => x := by
  conv in (Function.comp _) =>      --- error: 'pattern' conv tactic failed, pattern was not found
    simp
