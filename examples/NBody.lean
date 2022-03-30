import SciLean.Basic
import SciLean.Mechanics
import SciLean.Tactic.BubbleLimit
import SciLean.Solver.Impl

open SciLean

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 500000

-- section Pow

--   @[reducible]
--   instance Math.pow.is_atomic_smooth (ε : ℝ) [NonZero ε] : AtomicSmoothFun (λ x : X => snorm ε x) where
--     df := λ x dx => (1/snorm ε x) * ⟪x, dx⟫
--     is_smooth := sorry
--     is_df := sorry

-- end Pow

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


  def foo' (n : Nat) (y : X) : Impl (∇ λ x => (snorm ε (x - y))^(-1:ℝ)) :=
  by
    -- simp only [snorm.norm_approx ε]
    -- lift_limit (1:ℕ) "asdf"; admit; simp
    simp[gradient]
    simp[AtomicAdjointFun₂.adj₂]
    finish_impl

  #check Eq.mp

  class Fact (P : Prop) where
    p : P

  -- noncomputable
  def foo (n : Nat) (y : X) : Impl (∇ λ x => ∥x - y∥^(-1:ℝ)) :=
  by
    impl_assume (ε > 0) "asdf"

    simp only [snorm.norm_approx ε]
    bubble_limit; admit;

    simp[gradient]
    simp[AtomicAdjointFun₂.adj₂]
    
    lift_limit (1:ℕ) "asdf"; admit; simp

    impl_assume (ε = 0) "hihi" h
    rw[h]; simp
    finish_impl

  def bar (y: X):= (foo' 1 1 y).assemble!

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
    unfold_atomic
    simp[hold]
    
    conv =>
      enter [1,f,2,x,1,j,2,1,i]
      rw[!?((snorm (ε / E) (x i - x j) ^ (-(1 + 2) : ℝ)) * (x i - x j)
            =
            - ((snorm (ε / E) (x j - x i) ^ (-(1 + 2 : ℝ))) * (x j - x i)))]
      
    simp

    apply solver_finish
    
end SNorm


-- -- Lennard-Jones potential
-- -- https://en.wikipedia.org/wiki/Lennard-Jones_potential
-- def LennardJones 
--   (ε /- reguralization    -/ : ℝ) 
--   (e /- dispersion energy -/ : ℝ)
--   (r /- particle radius   -/ : ℝ) 
--   (x : X) :=
--   let E := (r^(6:ℝ))*(ϕ ε (-6) x)
--   4 * e * E * (E - 1)

-- #check SciLean.SemiHilbert.instSemiHilbertArrow

-- def V {n : Nat} (ε : ℝ) (x : ((ℝ^(3:ℕ))^n)) := ∑ i j, ϕ ε (-1) (x[i] - x[j])

-- variable (n : Nat) (x : (ℝ^(3:ℕ))^n) (i j : Fin n) (u : ℝ^n) (i j : Fin n) (ε : ℝ)

-- notation x "[[" i "]]" => PowType.powType.getOp x i

-- theorem sum_of_const {X : Type} {n : Nat} (x : X) [Vec X] 
--   : (∑ i : Fin n, x) = (n : ℝ) * x
-- := sorry

-- theorem mul_add_expand {X : Type} [Vec X] (r : ℝ) (x y : X) 
--   : r * (x + y) = r * x + r * y
-- := sorry

-- theorem mul_sub_expand {X : Type} [Vec X] (r : ℝ) (x y : X) 
--   : r * (x - y) = r * x - r * y
-- := sorry
  
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
-- variable {n : Nat} [NonZero n] (ε : ℝ) [NonZero ε]


  -- conv =>
  --   enter [1]
  --   unfold gradient
  --   pattern (δ _)
  --   -- simp


-- set_option trace.Meta.Tactic.simp.discharge true in
-- example  : Impl (∇ λ x : Fin n → ℝ^(3:ℕ) => ∑ i j, ϕ ε (-1) (x i - x j)) :=
-- by
--   autograd
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
  -- finish_impl

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

notation x "[[" i "]]" => PowType.powType.getOp x i

def H' (n : Nat) (ε : ℝ) (m : Fin n → ℝ) (x p : Fin n → ℝ^(3:ℕ)) := (∑ i, (1/(2*(m i))) * ∥p i∥²) + (∑ i j, (m i * m j) * ∥x i - x j∥{ε}^(-1:ℝ))

@[simp high]
theorem diff_of_const' {X Y : Type} [Vec X] [Vec Y] (y : Y)
  : δ (λ x : X => y) = λ x dx  => (0 : Y) := sorry

theorem smul_add {X} [Vec X] (r : ℝ) (x y : X) : r * (x + y) = r * x + r * y := sorry
theorem smul_sub {X} [Vec X] (r : ℝ) (x y : X) : r * (x - y) = r * x - r * y := sorry

def solver' (n : Nat) [NonZero n] (ε : ℝ) [NonZero ε] (m : Fin n → ℝ) 
: Solver (λ f => f = ode_solve (HamiltonianSystem (H' n ε m))) :=
by
  -- Unfold Hamiltonian definition and compute gradients
  simp[HamiltonianSystem, H']
  
  conv in (∇ _) =>
    simp[gradient, AtomicSmoothFun₂.df₁, AtomicSmoothFun₂.df₂, AtomicSmoothFun.df, AtomicAdjointFun.adj, AtomicAdjointFun₂.adj₁, AtomicAdjointFun₂.adj₂]

  conv in (∇ _) =>
    simp[gradient, AtomicSmoothFun₂.df₁, AtomicSmoothFun₂.df₂, AtomicSmoothFun.df, AtomicAdjointFun.adj, AtomicAdjointFun₂.adj₁, AtomicAdjointFun₂.adj₂]
    simp only [smul_smul_mul,smul_add,smul_sub]
    simp

    -- simp [gradient]
    -- simp [AtomicSmoothFun₂.df₁, hold]
    -- simp
  -- simp

  -- simp[gradient]
  -- unfold_atomic
  -- simp[hold]

  -- -- Apply RK4 method
  -- rw [ode_solve_fixed_dt runge_kutta4_step]
  -- conv => enter[1,f,2]; bubble_lim; (tactic => simp; admit)
  -- apply solver_limit 1; intro E
    
  apply solver_finish


def H (n : Nat) (ε : ℝ) (m : ℝ^n) (x p : ((ℝ^(3:ℕ))^n)) := (∑ i, (1/(2*m[i])) * ∥p[i]∥²) + (∑ i j, (m[i]*m[j]) * ∥x[i] - x[j]∥{ε}^(-1:ℝ))


-- m[[j]] * m[[i]] * (-(∥x[[j]] - x[[i]]∥{ε} ^ -(1 + 2)) * (↑n * (x[[j]] - x[[i]]))) 
theorem hoho {X} [Hilbert X] (x y : X) (a ε: ℝ) (m m' : ℝ)
  : m * (-(∥x - y∥{ε}^a) * (m'*(x - y))) = -m' * (-(∥y - x∥{ε}^a) * (m*(y - x))) := sorry


-- def solver (n : Nat) [NonZero n] (ε : ℝ) [NonZero ε] (m : ℝ^n) 
-- : Solver (λ f => f = ode_solve (HamiltonianSystem (H n ε m))) :=
-- by
--   -- Unfold Hamiltonian definition and compute gradients
--   simp[HamiltonianSystem, H]
  
--   simp[gradient]
--   unfold_atomic
--   simp[hold]

--   -- Apply RK4 method
--   rw [ode_solve_fixed_dt runge_kutta4_step]
--   conv => enter[1,f,2]; bubble_lim; (tactic => simp; admit)
--   apply solver_limit 1; intro E
    
--   apply solver_finish


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
