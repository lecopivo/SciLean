import SciLean.Modules.DifferentialEquations.OdeSolve
import SciLean.Util.LimitNotation


namespace SciLean

variable 
  {R : Type _} [IsROrC R] 
  {X : Type _} [Vec R X]
  {Y : Type _} [Vec R Y]
  {Z : Type _} [Vec R Z]

set_default_scalar R
open LimitNotation

/-- Can we integrate differential equation `∂ x t = f t (x t)` using `stepper` function?

The function `stepper t₁ t₂ x₀` computes approximation of the solution `x t₂` under initial condition `x t₁ = x₀`

TODO: refine the conditions, we probably want consistency and convergence. Maybe integrability in `f` too? or integrability of `f` should be specified somewhere else?
-/
structure IsOdeStepper (f : R → X → X) (stepper : R → R → X → X) where
  consistent : ∀ t x, (limit Δt' → 0, ∂ Δt:=Δt', stepper t Δt x) = f t x
  -- converges - something that it really converges
  -- maybe integrability of `f` ?? 
  
def odeSolveFixedStep (stepper : R → R → X → X) (steps : Nat) (t₁ t₂ : R) (x₀ : X) : X := Id.run do
  let Δt := (t₂-t₁)/steps
  let mut x := x₀
  let mut t := t₁
  for _ in [0:steps] do
    x := stepper t (t+Δt) x
    t += Δt 
  x

theorem odeSolve_fixed_dt (f : R → X → X) (stepper : (R → R → X → X)) 
  (hf : HasUniqueOdeSolution f) (hstepper : IsOdeStepper f stepper)
  : odeSolve f t₁ t₂ x₀ = limit n → ∞, odeSolveFixedStep stepper n t₁ t₂ xₒ := sorry_proof

--       simp -- bugs in reverseMode transform
#exit    

--- This requires some conditions on the function ... or just add the conclusion as an assumption
theorem odeSolve_fixed_dt.forward_euler (f : ℝ → X → X)
  : odeSolve f = limit (λ n => odeSolve_fixed_dt_impl' n (forward_euler_step f)) := sorry_proof

def midpoint_step (f : ℝ → X → X) (t₀ : ℝ) (x₀ : X) (Δt : ℝ) : X := 
  let dt := Δt/2
  let x' := x₀ + dt • f t₀ x₀
  x₀ + Δt • (f (t₀+dt) x')

def midpointStepper (f : ℝ → X → X) : OdeStepper f where
  stepper := midpoint_step f

function_properties SciLean.midpoint_step {X : Type} [Vec X] (f : ℝ → X → X) (t₀ : ℝ) (x₀ : X) (Δt : ℝ)
argument x₀ [IsSmooth λ (tx : ℝ×X) => f tx.1 tx.2]
  IsSmooth := by unfold midpoint_step; sorry_proof,
  noncomputable abbrev ∂ := λ dx₀ =>
    let Tf := λ t (xdx : X×X) => 𝒯 (λ x' => f t x') xdx.1 xdx.2
    (midpoint_step Tf t₀ (x₀,dx₀) Δt).2
    by sorry_proof,
  noncomputable abbrev 𝒯 := λ dx₀ =>
    let Tf := λ t (xdx : X×X) => 𝒯 (λ x' => f t x') xdx.1 xdx.2
    midpoint_step Tf t₀ (x₀,dx₀) Δt
    by sorry_proof
      

--- This requires some conditions on the function ... or just add the conclusion as an assumption
theorem odeSolve_fixed_dt.midpoint_euler (f : ℝ → X → X)
  : odeSolve f = limit (λ n => odeSolve_fixed_dt_impl' n (midpoint_step f)) := sorry_proof


noncomputable
def backward_euler_step (f : ℝ → X → X) (t₀ : ℝ) (x₀ : X) (Δt : ℝ) := 
  (λ x' => x' + Δt • f t₀ x')⁻¹ x₀

noncomputable
def implicit_midpoint_step (f : ℝ → X → X) (t₀ : ℝ) (x₀ : X) (Δt : ℝ) := 
  (λ x' => x' + Δt • f (t₀ + Δt/2) (((1:ℝ)/2) • (x₀ + x')))⁻¹ x₀

def runge_kutta4_step (f : ℝ → X → X) (t₀ : ℝ) (x₀ : X) (Δt : ℝ) : X :=
  let dt := Δt/2
  let k1 := f t₀ x₀
  let k2 := f (t₀+dt) (x₀ + dt • k1)
  let k3 := f (t₀+dt) (x₀ + dt • k2)
  let k4 := f (t₀+Δt) (x₀ + Δt • k3)
  x₀ + (Δt/6) • (k1 + (2:ℝ)•k2 + (2:ℝ)•k3 + k4)

--- This requires some conditions on the function ... or just add the conclusion as an assumption
theorem odeSolve_fixed_dt.runge_kutta4 (f : ℝ → X → X)
  : odeSolve f = limit (λ n => odeSolve_fixed_dt_impl' n (runge_kutta4_step f)) := sorry_proof

abbrev Stepper := ∀ {X} [Vec X], (ℝ → X → X) → (ℝ → X → ℝ → X)

instance {X} [Vec X] (f : ℝ → X → X) 
  : CoeFun (OdeStepper f) (λ _ => ℝ → X → ℝ → X) := ⟨λ s => s.stepper⟩

def odeSolve_fixed_dt_array {X} [Vec X] (f : ℝ → X → X)
  (stepper : Stepper) (n : Nat) (t₀ : ℝ) (x₀ : X) (T : ℝ) : Array X := Id.run do
  let Δt := (T - t₀)/n
  let mut x := x₀
  let mut t := t₀
  let mut xs := .mkEmpty (n+1)
  xs := xs.push x
  let step := stepper f
  for _ in [0:n] do
    x := step t x Δt
    xs := xs.push x
    t += Δt
  xs

theorem odeSolve_fixed_dt_on_interval {X} [Vec X] {f : ℝ → X → X} {t₀ : ℝ} {x₀ : X} 
  (stepper : Stepper) (interpol : (ℤ→X) → (ℝ→X)) (T : ℝ)
  : (λ t => odeSolve f t₀ x₀ t)
    = 
    limit λ n => 
      let Δt := (T-t₀) / n
      let toGrid := λ t : ℝ => (t - t₀)/Δt
      let odeData := odeSolve_fixed_dt_array f stepper n t₀ x₀ T
      λ t => interpol (extend1DFinStreak λ i => odeData.get i) (toGrid t)
  := sorry

#exit

-- argument t [Hilbert X] [IsSmooth f] [∀ s, IsSmooth (f s)]
--   hasAdjDiff   := by constructor; infer_instance; simp; intro; infer_instance; done,
--   adjDiff_simp := ⟪dt', f t (odeSolve f t x₀)⟫ by simp[adjointDifferential,hold]; done
 
argument x₀ [Hilbert X] [IsSmooth f] [∀ s, HasAdjoint (f s)]
  hasAdjoint := sorry_proof,
  adj_simp   := odeSolve (λ s => (f (t - s))†) t x₀' 
  by 
    -- Define adjoint solution `y such that
    --  ∀ s, ⟪x (t - s), y s⟫ = ⟪x t, y 0⟫
    -- in particular for s := t we get desired ⟪x 0, y t⟫ = ⟪x t, y 0⟫
    -- Differentiate above equation w.r.t to `s and you get that `y satisfies
    -- ∂ y s 1 = (f (t - s))†
    sorry_proof
argument x₀ [Vec X] [IsSmooth f] [∀ s, IsSmooth (f s)]
  isSmooth   := sorry_proof,
  diff_simp  := odeSolve (λ s => ∂ (f s) (odeSolve f s x₀)) t dx₀
    by sorry_proof
argument x₀ [Hilbert X] [IsSmooth f] [inst : ∀ t, HasAdjDiff (f t)]
  hasAdjDiff   := by 
    have isf := λ t => (inst t).isSmooth
    have iaf := λ t => (inst t).hasAdjDiff
    constructor; infer_instance; simp; intro x₀; infer_instance,
  adjDiff_simp := odeSolve (λ s => ∂† (f (t - s)) (odeSolve f (t - s) x₀)) t dx₀' 
    by 
      have isf := λ t => (inst t).isSmooth
      have iaf := λ t => (inst t).hasAdjDiff
      simp at iaf
      simp[adjointDifferential]
      done


instance odeSolve.arg_f.isSmooth {X W} [Vec X] [Vec W] 
  (f : W → ℝ → X → X) [IsSmooth f] [∀ w, IsSmooth (f w)] [∀ w t, IsSmooth (f w t)]
  : IsSmooth (λ w => odeSolve (f w)) := sorry_proof

@[simp]
theorem odeSolve.arg_f.diff_simp {X W} [Vec X] [Vec W] 
  (f : W → ℝ → X → X) [IsSmooth f] [∀ w, IsSmooth (f w)] [∀ w t, IsSmooth (f w t)]
  : ∂ (λ w => odeSolve (f w))
    =
    λ w dw t x => (odeSolve (λ t (x,dx) => (f w t x, ∂ f w dw t x + ∂ (f w t) x dx)) t (x,0)).1
  := sorry_proof

theorem odeSolve.arg_f.diff_simp_alt {X W} [Vec X] [Vec W] 
  (f : W → ℝ → X → X) [IsSmooth f] [∀ w, IsSmooth (f w)] [∀ w t, IsSmooth (f w t)]
  : ∂ (λ w => odeSolve (f w))
    =
    λ w dw t x₀ => 
      let x := λ t => odeSolve (f w) t x₀
      (odeSolve (λ t dx => ∂ f w dw t (x t) + ∂ (f w t) (x t) dx) t 0)
  := sorry_proof

-- @[simp]
-- theorem odeSolve.arg_f.adj_simp {X W} [SemiHilbert X] [SemiHilbert W] 
--   (f : W → ℝ → X → X) [IsSmooth f] [∀ w, IsSmooth (f w)] [∀ w t, IsSmooth (f w t)] (x₀ : X)
--   : (λ w => odeSolve (f w) t x₀)†
--     =
--     λ x' => sorry
--   := sorry_proof

-- @[simp]
-- theorem odeSolve.arg_f.adjDiff_simp {X W} [SemiHilbert X] [SemiHilbert W] 
--   (f : W → ℝ → X → X) [IsSmooth f] [∀ w, IsSmooth (f w)] [∀ w t, IsSmooth (f w t)] (x₀ : X)
--   : ∂† (λ w => odeSolve (f w) t x₀)
--     =
--     λ w dw' => 
--       sorry := 
--   by
--     simp only [adjointDifferential]
--     simp [odeSolve.arg_f.diff_simp_alt]
    
-- example [Hilbert X] (f : ℝ → X → X) (y : X) [IsSmooth f] [∀ t, HasAdjDiff (f t)] 
--   : ∇ (λ x₀ => ∥odeSolve f t x₀ - y∥²) = 0 := 
-- by 
--   simp[gradient]; unfold hold; simp




