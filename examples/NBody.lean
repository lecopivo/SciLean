import SciLean.Basic
-- import SciLean.Mechanics

open SciLean

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 500000

variable {X} [Hilbert X]

instance (ε : ℝ) [NonZero ε] (α : ℝ) : IsSmooth (λ x : X => (∥x∥² + ε^2)^α) := sorry

@[simp]
theorem eps_norm.diff {X} [Hilbert X] (ε : ℝ) [NonZero ε] (α : ℝ)
  : δ (λ x : X => (∥x∥² + ε^2)^α) = λ x dx : X => 2 * α * ((∥x∥² + ε^2)^(α-1)) * ⟪x, dx⟫
  := sorry

@[simp]
theorem eps_norm.grad {X} [Hilbert X] (ε : ℝ) [NonZero ε] (α : ℝ)
  : ∇ (λ x : X => (∥x∥² + ε^2)^α) = λ x : X => 2 * α * ((∥x∥² + ε^2)^(α-1)) * x
  := by funext x; autograd; done


def ϕ (ε : ℝ) (α : ℝ) (x : X) := (∥x∥² + ε^2)^α
instance (ε : ℝ) [NonZero ε] (α : ℝ) : IsSmooth (λ x : X => ϕ ε α x) := by simp[ϕ] infer_instance done

@[simp]
theorem ϕ.diff (ε : ℝ) [NonZero ε] (α : ℝ) 
  : δ (ϕ ε α) = λ x dx : X => 2 * α * (ϕ ε (α-1) x) * ⟪x, dx⟫  
  := by simp[ϕ] done

@[simp]
theorem ϕ.grad (ε : ℝ) [NonZero ε] (α : ℝ) 
  : ∇ (ϕ ε α) = λ x : X => 2 * α * (ϕ ε (α-1) x) * x
  := by simp[ϕ] done

-- #check SciLean.SemiHilbert.instSemiHilbertArrow



def H (n : Nat) (ε : ℝ) (x p : ((ℝ^(3:ℕ))^n)) := ∥p∥² + ∑ i j, ϕ ε (-1) (x[i] - x[j])

variable (n : Nat) (x : (ℝ^(3:ℕ))^n) (i j : Fin n) (u : ℝ^n) (i j : Fin n) (ε : ℝ)

#check ϕ ε (-1) (x[i] - x[j])

example : SemiInner.Trait (ℝ^(3:ℕ)) := by infer_instance
#check (∥x[i] + x[j]∥²)
#check (u + u)
  

-- set_option trace.Meta.synthInstance true in
-- set_option trace.Meta.Tactic.simp true in
def V.diff (n : Nat) [NonZero n] (ε : ℝ) [NonZero ε] (m k : ℝ) 
-- : Impl (δ λ x : (ℝ^(3:ℕ)^n) => ∑ i j, ϕ ε (-1) (x[i] - x[j])) := 
: Impl (δ λ x : ((ℝ^(3:ℕ))^n) => ∑ i j, ∥x[i] - x[j]∥²) := 
by
  autodiff
  finish_impl

-- instance (n : ℕ) : SciLean.HasAdjoint (sum : (Fin n → ℝ) → ℝ) := by infer_instance


-- instance {X Y} [Hilbert X] [Hilbert Y] : SciLean.HasAdjoint (fun xy : X × Y => xy.fst) := by sorry
-- instance {X Y} [Hilbert X] [Hilbert Y] : SciLean.HasAdjoint (fun xy : X × Y => xy.snd) := by sorry

-- @[simp] theorem Prod.fst.adjoint {X Y} [Hilbert X] [Hilbert Y] 
--   : (Prod.fst : X × Y → X)† = λ x : X => (x, 0) := by sorry

-- @[simp] theorem Prod.snd.adjoint {X Y} [Hilbert X] [Hilbert Y] 
--   : (Prod.snd : X × Y → Y)† = λ y : Y => (0, y) := by sorry

-- set_option trace.Meta.Tactic.simp true in
-- example {X Y} [Hilbert X] [Hilbert Y] 
--   : (Prod.fst : X × Y → X)† = λ x : X => (x, 0)
--   := 
-- by 
--   simp (config := { singlePass := true })
--   admit

-- instance (x : ((ℝ^(3:ℕ))^n)) : ∀  (i : Fin n), SciLean.HasAdjoint 
--   fun (dx : ((ℝ^(3:ℕ))^n)) =>
--           ∑ j, 2 * ⟪x[i] - x[j], dx[i] - dx[j]⟫
--   := by infer_instance

example (n : Nat) [NonZero n] (x : ((ℝ)^n))
     : ∀ (i : Fin n), HasAdjoint (fun (dx : ((ℝ)^n)) =>
                       ∑ j, x[i] * dx[j])
     := by intro i; infer_instance

set_option trace.Meta.Tactic.simp.discharge true in
def double_sum_adjoint' (n : Nat) [NonZero n] (x : ((ℝ)^n))
     : Impl (fun (dx : ((ℝ)^n)) (i : Fin n) =>
        ∑ j, x[i] * dx[j])†
  := 
by
  -- WHY IS THIS NOT SIMPLIFYING ?? 
  -- i.e. why simp can't discharge?
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  finish_impl

  
-- set_option pp.explicit true in
set_option trace.Meta.Tactic.simp.discharge true in
def double_sum_adjoint (n : Nat) [NonZero n] (x : ((ℝ^(3:ℕ))^n))
     : Impl (fun (dx : ((ℝ^(3:ℕ))^n)) i =>
        ∑ j, 2 * ⟪x[i] - x[j], dx[i] - dx[j]⟫)†
  := 
by
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  simp (config := { singlePass := true })
  
  -- conv =>
  --   enter [1,y,1,1,i,1,j]
  --   simp
  --   delta Function.uncurry
    
  finish_impl
  



def V.grad (n : Nat) [NonZero n] (ε : ℝ) [NonZero ε] (m k : ℝ) 
-- : Impl (δ λ x : (ℝ^(3:ℕ)^n) => ∑ i j, ϕ ε (-1) (x[i] - x[j])) := 
: Impl (∇ λ x : ((ℝ^(3:ℕ))^n) => ∑ i j, ∥x[i] - x[j]∥²) := 
by
  autograd
  conv =>
    enter [1,x]
    simp

  . 

    
  finish_impl


-- set_option trace.Meta.isDefEq true in
-- set_option trace.Meta.Tactic.simp true in
-- def solver (n : Nat) [NonZero n] (ε : ℝ) [NonZero ε] (m k : ℝ) (steps : Nat) 
-- : Impl (ode_solve (HamiltonianSystem (H n ε m k))) :=
-- by
--   -- Unfold Hamiltonian definition and compute gradients
--   simp[HamiltonianSystem, H]
--   autograd
--   conv in (gradient _) =>
--     simp[gradient]
--     conv =>
--       pattern (δ _)
--       enter [x, dx]
--       simp (config := { singlePass := true })
--       simp (config := { singlePass := true })
    


  -- -- Apply RK4 method
  -- rw [ode_solve_fixed_dt runge_kutta4_step]
  -- lift_limit steps "Number of ODE solver steps."; admit; simp
    
  -- finish_impl
  -- admit
  -- done


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



