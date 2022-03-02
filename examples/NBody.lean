import SciLean.Basic
import SciLean.Mechanics

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
-- def V.diff (n : Nat) [NonZero n] (ε : ℝ) [NonZero ε] (m k : ℝ) 
-- : Impl (δ λ x : ((ℝ^(3:ℕ))^n) => ∑ i j, ∥x[i] - x[j]∥²) := 
-- by
--   autodiff
--   finish_impl

-- instance (n : ℕ) : SciLean.HasAdjoint (sum : (Fin n → ℝ) → ℝ) := by infer_instance

instance {X Y} [Hilbert X] [Hilbert Y] : SciLean.HasAdjoint (fun xy : X × Y => xy.fst) := by sorry
instance {X Y} [Hilbert X] [Hilbert Y] : SciLean.HasAdjoint (fun xy : X × Y => xy.snd) := by sorry

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

notation x "[[" i "]]" => PowType.powType.getOp x i


example (x : Fin n → ℝ) : ∀  (i : Fin n), SciLean.HasAdjoint 
  fun (dx : Fin n → ℝ) => 
          ∑ j, x i * (dx i + dx j)
  := by infer_instance done

example (x : Fin n → ℝ^(3:ℕ)) : ∀  (i : Fin n), SciLean.HasAdjoint 
  fun (dx : Fin n → ℝ^(3:ℕ)) j => ⟪x i,  dx j - dx j⟫
  := by infer_instance done


-- example : SciLean.SemiHilbert ℝ (SciLean.SemiInner.Trait₂.R (ℝ × ℝ) ℝ) (SciLean.SemiInner.Trait₂.D (ℝ × ℝ) ℝ) SciLean.SemiInner.Trait₂.eval := by infer_instance

constant sum' {n} (f : Fin n → ℝ) : ℝ

instance {n} : IsLin (sum' : (Fin n → ℝ) → ℝ) := sorry
instance {n} : HasAdjoint (sum' : (Fin n → ℝ) → ℝ) := sorry

--- Float gets exposed somewhere, somehow :(
-- set_option trace.Meta.isDefEq true in
example (x : ((ℝ)^n)) (c : ℝ) : ∀ (i : Fin n), HasAdjoint 
  fun (dx : ((ℝ)^n)) => ∑ j, x[j] * (dx[j] + (2:ℝ)*dx[i])
  := by infer_instance done

example {X} [Hilbert X] : ∀ (i : Fin n), HasAdjoint
  fun (x : X) => -x
  := by infer_instance done

-- set_option pp.explicit true in
-- set_option trace.Meta.synthInstance true in
example : ∀ (i : Fin n), HasAdjoint 
  fun (x : ℝ) => -x
  := 
by
  -- intro i  -- with this it works
  infer_instance done

open SemiInner in
class HA' {X}
  {R} [Vec R] (f : X → X) : Prop  
  -- where
  --   hasAdjoint : ∃ (f' : Y → X), ∀ (x : X) (y : Y) (d : (Trait₂.D X Y)), 
  --                  (testFunction' d x ∨ testFunction' d y) → ⟪f' y, x⟫ = ⟪y, f x⟫
  --   preservesTestFun : ∀ (x : X) (d : (Trait₂.D X Y)), testFunction' d x → testFunction' d (f x)

open SemiInner in
@[reducible] abbrev HA {X} 
  [Trait X] 
  [Vec (Trait.R X)]
  (f : X → X) 
  : Prop 
  := HA' (R := (Trait.R X)) f

instance {X R D e} [Vec R] [SemiHilbert X R D e] : HA (λ x : X => -x) := sorry

example {X} [Hilbert X] : ∀ (i : Fin n), HA
  fun (x : X) => -x
  := by infer_instance done

-- set_option pp.explicit true in
-- set_option trace.Meta.isDefEq true in
-- set_option trace.Meta.synthInstance true in
example : HA
  fun (x : ℝ) => -x
  := by infer_instance done

example : ∀ (i : Fin n), HasAdjoint 
  fun (x : ((ℝ^(3:ℕ))^n)) => -x
  := by infer_instance done

example {m} : ∀ (i : Fin n), HasAdjoint $
  (fun (dx : Fin n → Fin m → ℝ) => dx i)
  := by infer_instance done

example {m : Nat} : ∀ (i : Fin n), HasAdjoint 
  fun (dx : Fin n → ℝ^m) j => dx i + dx j
  := by infer_instance done

set_option trace.Meta.synthInstance true in
example {m : Nat} (x : ℝ^m) : ∀ (i : Fin n), HasAdjoint 
  fun (dx : Fin n → ℝ^m) => ∑ j, ⟪x, dx i + dx j⟫
  := by infer_instance done

example (x : ℝ^(3:ℕ)) : ∀ (i : Fin n), HasAdjoint 
  fun (dx : ((ℝ^(3:ℕ))^n)) =>
          ∑ j, ⟪x, dx[i] + dx[j]⟫
  := by infer_instance done

example (x : ((ℝ^(3:ℕ))^n)) : ∀  (i : Fin n), HasAdjoint 
  fun (dx : ((ℝ^(3:ℕ))^n)) =>
          ∑ j, 2 * ⟪x[i] - x[j], dx[i] + dx[j]⟫
  := by infer_instance done


-- set_option trace.Meta.isDefEq true in
example (n : List Nat) (i : Nat) (m : List (_ i)) (h : n = m) : n = m := sorry

-- example (x : SemiInner.Trait₂.R ℝ ℝ) (i : Nat) (y : SemiInner.Trait₂.R (_ i) (_ i))  : True := sorry

-- -- set_option trace.Meta.synthInstance true in
-- example (n : Nat)
--      : ∀ (c : ℝ), HasAdjoint (fun (dx : Fin n → ℝ) => fun j => c * dx j)
--      :=
-- by
--   -- intro c
--   infer_instance; done

-- --- This needs to work and it does not for some reason :(
-- ---
-- ---   This has problem because it triggers a SubGoal 'SciLean.Vec Float'
-- --- that can't be solved.
-- -- set_option trace.Meta.synthInstance true in
-- example (n : Nat)
--      : ∀ (c : ℝ), HasAdjoint (fun (dx : Fin n → ℝ) => sum' fun j => c * dx j)
--      :=
-- by
--   -- intro c
--   infer_instance; done

-- def double_sum_adjoint'' (n : Nat) (x : Fin n → ℝ)
--      : Impl (fun (dx : Fin n → ℝ) (i j : Fin n) => x i * dx j)†
--   := 
-- by
--   simp
--   finish_impl


-- -- set_option trace.Meta.Tactic.simp.rewrite true in
-- -- set_option trace.Meta.Tactic.simp.discharge true in
-- def double_sum_adjoint' (n : Nat) [NonZero n] (x : ((ℝ)^n)) (c : ℝ)
--      : Impl (fun (dx : ((ℝ)^n)) (i j : Fin n) => x[i] * dx[j])†
--   := 
-- by
--   simp
--   finish_impl

-- example (x : ((ℝ)^n)) : ∀  (i : Fin n), SciLean.HasAdjoint 
--   fun (dx : ((ℝ)^n)) =>
--           ∑ j, ⟪x[i] - x[j], dx[i] - dx[j]⟫
--   := by infer_instance

-- instance (i : Fin n) :
--   SciLean.HasAdjoint fun (f : Fin n → ℝ) => (f i)
--   := sorry

-- -- set_option trace.Meta.synthInstance true in
-- -- This example seems important!!!
-- example (x : Fin n → ℝ) :
--   ∀ (i : Fin n), SciLean.HasAdjoint fun (dx : Fin n → ℝ) => ∑ j, (x j) * (dx i + dx j)
--   := 
-- by 
--   infer_instance
--   done

-- notation x "[[" i "]]" => PowType.powType.getOp x i

  
-- -- set_option pp.explicit true in
-- -- set_option trace.Meta.Tactic.simp.rewrite true in
-- def double_sum_adjoint (n : Nat) [NonZero n] (x : ((ℝ^(3:ℕ))^n))
--      : Impl (fun (dx : ((ℝ^(3:ℕ))^n)) i =>
--         ∑ j, 2 * ⟪x[i] - x[j], dx[i] - dx[j]⟫)†
--   := 
-- by
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   simp (config := { singlePass := true })
--   finish_impl
  
-- notation x "[[" i "]]" => PowType.powType.getOp x i

-- def V.grad (n : Nat) [NonZero n] (ε : ℝ) [NonZero ε] (m k : ℝ) 
--   : Impl (∇ λ x : ((ℝ^(3:ℕ))^n) => ∑ i j, ∥x[i] - x[j]∥²) := 
-- by
--   autograd
--   -- sum_together
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
