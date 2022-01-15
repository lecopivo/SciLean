import SciLean.Basic
import SciLean.Mechanics

import Lean.Meta.Tactic

set_option synthInstance.maxHeartbeats 5000
set_option synthInstance.maxSize 1000

abbrev V := ℝ × ℝ
abbrev Q := ℝ

def g : ℝ := 9.81
def L' (m : ℝ) (x v : V) := (m/2) * ⟨v,v⟩ - m * g * x.2


def parm (l : ℝ) (θ : Q) : V := (l * Math.sin θ, -l * Math.cos θ)
def L (m l : ℝ) (θ ω : Q) := L' m (parm l θ) (δ (parm l) θ ω)

-- set_option trace.Meta.Tactic.simp true
-- set_option trace.Meta.synthInstance true

def solver (m l : ℝ) (steps : Nat) : Impl (ode_solve (LagrangianSystem (L m l))) :=
by

  

  conv in (L _ _) =>
    simp [L, L', parm]
    { pattern (differential _); rmlamlet; enter [θ, ω]; simp }  -- autodiff
  
  simp -- Lagrangian is in a nice form now

  conv => 
    pattern (LagrangianSystem _); whnf

  simp
  
  --------------------- mass matrix ---------------------------------
  conv =>   -- autograd par1
    repeat' (enter [1]; pattern (gradient _))
    simp [gradient]
    pattern (differential _)
    rmlamlet
    repeat' (ext x);
    simp

  conv =>   -- autograd part2
    pattern (comp dual _)
    ext x; simp
    pattern (dual _)
    rmlamlet
    simp

  conv =>  -- autodiff
    repeat' enter [1]; pattern (differential _)
    rmlamlet
    repeat' (ext x)
    simp

  .
  
  ------- potential forces ----
  conv =>   -- autograd par1
    repeat' (enter [1]; pattern (gradient _))
    simp [gradient]
    pattern (differential _)
    rmlamlet
    repeat' (ext x);
    simp

  conv =>   -- autograd part2
    pattern (comp dual _)
    ext x; simp
    pattern (dual _)
    rmlamlet
    simp

  .

  ------- geometry forces ----
  conv =>  -- autodiff
    repeat' enter [1]; pattern (differential _)
    rmlamlet
    repeat' (ext x)
    simp

  conv =>   -- autograd par1
    repeat' (enter [1]; pattern (gradient _))
    simp [gradient]
    pattern (differential _)
    rmlamlet
    repeat' (ext x);
    simp

  conv =>   -- autograd part2
    pattern (comp dual _)
    ext x; simp
    pattern (dual _)
    rmlamlet
    simp

  .

  ------- TODO: invert ------


  ------- TODO: ode_solve --------

  admit

