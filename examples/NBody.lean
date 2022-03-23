import SciLean.Basic
import SciLean.Mechanics

open SciLean

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 5000000
set_option maxHeartbeats 5000000

variable {X} [Hilbert X]

instance (ε : ℝ) [NonZero ε] (α : ℝ) : IsSmooth (λ x : X => (∥x∥² + ε^2)^α) := sorry

@[simp]
theorem eps_norm.diff {X} [Hilbert X] (ε : ℝ) [NonZero ε]
  : δ (λ (x : X) (α : ℝ) => (∥x∥² + ε^2)^α) = λ (x dx : X) (α) => 2 * α * ((∥x∥² + ε^2)^(α-1)) * ⟪x, dx⟫
  := sorry

@[simp]
theorem eps_norm.grad {X} [Hilbert X] (ε : ℝ) [NonZero ε] (α : ℝ)
  : ∇ (λ x : X => (∥x∥² + ε^2)^α) = λ x : X => 2 * α * (((∥x∥² + ε^2)^(α-1)) * x)
  := by funext x; autograd; done


def ϕ (ε : ℝ) (α : ℝ) (x : X) := (∥x∥² + ε^2)^(α/2)
instance (ε : ℝ) [NonZero ε] (α : ℝ) : IsSmooth (λ x : X => ϕ ε α x) := by simp[ϕ] infer_instance done

@[simp]
theorem ϕ.diff (ε : ℝ) [NonZero ε] (α : ℝ) 
  : δ (ϕ ε α) = λ x dx : X => α * (ϕ ε (α-2) x) * ⟪x, dx⟫ := 
by 
  simp[ϕ] 
  rw[!?(2 * (α / 2) = α),
     !?((α - 2) / 2 = α /2 - 1)] 
  done

@[simp]
theorem ϕ.grad (ε : ℝ) [NonZero ε] (α : ℝ) 
  : ∇ (ϕ ε α) = λ x : X => α * (ϕ ε (α-2) x * x) := 
by 
  simp[ϕ]
  rw[!?(2 * (α / 2) = α),
     !?((α - 2) / 2 = α /2 - 1)]
  done

-- Lennard-Jones potential
-- https://en.wikipedia.org/wiki/Lennard-Jones_potential
def LennardJones 
  (ε /- reguralization    -/ : ℝ) 
  (e /- dispersion energy -/ : ℝ)
  (r /- particle radius   -/ : ℝ) 
  (x : X) :=
  let E := (r^(6:ℝ))*(ϕ ε (-6) x)
  4 * e * E * (E - 1)

-- #check SciLean.SemiHilbert.instSemiHilbertArrow

def H (n : Nat) (ε : ℝ) (x p : ((ℝ^(3:ℕ))^n)) := ∥p∥² + ∑ i j, ϕ ε (-1) (x[i] - x[j])

def V {n : Nat} (ε : ℝ) (x : ((ℝ^(3:ℕ))^n)) := ∑ i j, ϕ ε (-1) (x[i] - x[j])

-- variable (n : Nat) (x : (ℝ^(3:ℕ))^n) (i j : Fin n) (u : ℝ^n) (i j : Fin n) (ε : ℝ)

notation x "[[" i "]]" => PowType.powType.getOp x i

theorem sum_of_const {X : Type} {n : Nat} (x : X) [Vec X] 
  : (∑ i : Fin n, x) = (n : ℝ) * x
:= sorry

theorem mul_add_expand {X : Type} [Vec X] (r : ℝ) (x y : X) 
  : r * (x + y) = r * x + r * y
:= sorry

theorem mul_sub_expand {X : Type} [Vec X] (r : ℝ) (x y : X) 
  : r * (x - y) = r * x - r * y
:= sorry
  
-- -- set_option pp.explicit true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
-- set_option synthInstance.maxHeartbeats 50000 in
-- set_option synthInstance.maxSize 1000 in
-- def double_sum_adjoint (n : Nat) [NonZero n] (x : ((ℝ^(3:ℕ))^n))
--      : Impl (fun (dx : ((ℝ^(3:ℕ))^n)) i =>
--         ∑ j, 2 * ⟪x[i] - x[j], dx[i] - dx[j]⟫)†
--   := 
-- by
--   simp
--   simp only [mul_sub_expand, mul_add_expand]
--   simp
--   finish_impl

--   finish_impl
  

-- notation x "[[" i "]]" => PowType.powType.getOp x i
variable {n : Nat} [NonZero n] (ε : ℝ) [NonZero ε]


  -- conv =>
  --   enter [1]
  --   unfold gradient
  --   pattern (δ _)
  --   -- simp


-- set_option trace.Meta.Tactic.simp.discharge true in
example  : Impl (∇ λ x : Fin n → ℝ^(3:ℕ) => ∑ i j, ϕ ε (-1) (x i - x j)) :=
by
  autograd
  -- conv =>
  --   enter [1]
  --   unfold gradient
  --   pattern (δ _)
  --   simp
  --   conv => 
  --     pattern (δ _)
  --     enter [x,dx]
  --     simp (config := {singlePass := true})
  --     simp (config := {singlePass := true})
  --     enter[1,i]
  --     simp (config := {singlePass := true})
  --     simp (config := {singlePass := true})
  --     enter[1,j]
  --     simp (config := {singlePass := true})
  --     simp (config := {singlePass := true})
  --     simp (config := {singlePass := true})
  --     simp (config := {singlePass := true})
  --   . 
  --   simp (config := {singlePass := true})
  --   simp (config := {singlePass := true})
  --   simp
  --   conv => 
  --     enter [x,1,j,1,2,1,i]
  --     simp only [!?(∀ y, ϕ ε (-1 - 2) (x[j] - y) = ϕ ε (-1 - 2) (y - x[j]))]

  -- . 
  finish_impl

-- def V.grad (n : Nat) [NonZero n] (ε : ℝ) [NonZero ε] (m k : ℝ) 
--   : Impl (∇ λ x : Fin n → Fin 3 → ℝ => ∑ i j, ∥x i - x j∥²) := 
-- by
--   autograd
--   sum_together
--   finish_impl


-- def V.grad (n : Nat) [NonZero n] (ε : ℝ) [NonZero ε] (m k : ℝ) 
--   : Impl (∇ λ x : ((ℝ^(3:ℕ))^n) => ∑ i j, ∥x[i] - x[j]∥²) := 
-- by
--   autograd
--   sum_together
--   finish_impl

-- def V.grad' (n : Nat) [NonZero n] (ε : ℝ) [NonZero ε] (p : ((ℝ^(3:ℕ))^n)) (c : ℝ)
--   : Impl (∇ λ x : ((ℝ^(3:ℕ))^n) =>  ∑ i j, ϕ ε (-1) (x[i] - x[j])) := 
-- by
--   autograd
--   finish_impl

-- def solver (n : Nat) [NonZero n] (ε : ℝ) [NonZero ε] (m k : ℝ) (steps : Nat) 
-- : Impl (ode_solve (HamiltonianSystem (H n ε))) :=
-- by
--   -- Unfold Hamiltonian definition and compute gradients
--   simp[HamiltonianSystem, H]
--   autograd
--   autograd

--   -- Apply RK4 method
--   rw [ode_solve_fixed_dt runge_kutta4_step]
--   lift_limit steps "Number of ODE solver steps."; admit; simp
    
--   finish_impl


-- def main : IO Unit := do
--   IO.println s!"Hello Houdini!"
--   IO.println s!"Current time: {← Hou.time}" 
--   let t : ℝ ← Hou.time

--   let m ← Hou.getDetailR 0 "mass"
--   let k ← Hou.getDetailR 0 "stiffness"
--   let substeps := 1
--   let N : Nat := (← Hou.npoints 0).toNat

--   IO.println s!"mass: {m} stiffness: {k}"

--   let evolve ← (solver N m k substeps).assemble

--   let mut X : ℝ^N ← PowType.intro λ i => 0
--   let mut V : ℝ^N ← PowType.intro λ i => 0

--   -- load points
--   for (i : Nat) in [0:N] do 
--     let x ← Hou.getPointV3 0 "P" i
--     let v ← Hou.getPointV3 0 "v" i
--     X := X.set ⟨i,sorry⟩ (x[(1 : Fin 3)])
--     V := V.set ⟨i,sorry⟩ (v[(1 : Fin 3)])

--   let (X',V') := evolve (1.0/24.0) (X,V)

--   for (i : Nat) in [0:N] do 
--     let mut x ← Hou.getPointV3 0 "P" i
--     let mut v ← Hou.getPointV3 0 "v" i
--     x := x.set 1 (X'[!i])
--     v := v.set 1 (V'[!i])
--     Hou.setPointV3 "P" i x
--     Hou.setPointV3 "v" i v

--   IO.println ""
