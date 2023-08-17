import SciLean.Modules.DifferentialEquations.OdeSolve
import SciLean.Util.RewriteBy


namespace SciLean

variable 
  {K : Type _} [IsROrC K] 
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]

open_notation_over_field K

structure OdeStepper {K X} [IsROrC K] [Vec K X] (f : K → X → X) where
  stepper (t s : K) (x : X) : X
  -- The basic consistency condition is:
  is_consistent : ∀ t x, (∂ (s:=t), stepper t s x) 1 = f t x
  -- there are probably others

def forwardEulerStepper (f : K → X → X) : OdeStepper f where
  stepper t s x := x + (s-t) • f t x
  is_consistent := by ftrans

@[ftrans]
theorem _root_.Function.invFun.arg_a1.cderiv_rule
  (f : X → Y)
  : cderiv K (fun y => Function.invFun f y)
    =
    fun y dy => 
      let x := Function.invFun f y
      Function.invFun (cderiv K f x) dy :=
by
  sorry_proof

variable (f : X → Y → Z)
#check (cderiv K fun x => Function.invFun (f x) ∘ (f x)) rewrite_by 
  simp[Function.comp.arg_a0.cderiv_rule _  sorry sorry]


@[ftrans]
theorem _root_.Function.invFun.arg_f.cderiv_rule
  (f : X → Y → Z)
  : cderiv K (fun x => Function.invFun (f x))
    =
    fun x dx => 
      
      sorry :=
by
  have h : 
  sorry_proof


noncomputable
def backwardEulerStepper (f : K → X → X) : OdeStepper f where
  stepper t s x := Function.invFun (fun x' => x' - (s-t) • f t x') x
  is_consistent := by 
    simp
    set_option trace.Meta.Tactic.simp.unify true in 
    ftrans only
    sorry_proof


-- function_properties SciLean.forward_euler_step {X : Type} [Vec X] (f : ℝ → X → X) (t₀ : ℝ) (x₀ : X) (Δt : ℝ)
-- argument x₀ [IsSmooth λ (tx : ℝ×X) => f tx.1 tx.2]
--   IsSmooth := by unfold forward_euler_step; sorry_proof,
--   noncomputable abbrev ∂ := λ dx₀ =>
--     dx₀ + Δt • (∂ x':=x₀;dx₀, f t₀ x')
--     -- forward_euler_step Tf t₀ (x₀,dx₀) Δt
--     by
--       unfold forward_euler_step
--       have : ∀ t, IsSmooth (f t) := sorry_proof 
--       fun_trans
--       simp, -- WTF where did the goal `True` came from?
--   noncomputable abbrev 𝒯 := λ dx₀ =>
--     let Tf := λ t (xdx : X×X) => 𝒯 (λ x' => f t x') xdx.1 xdx.2
--     forward_euler_step Tf t₀ (x₀,dx₀) Δt
--     by
--       unfold forward_euler_step
--       funext dx₀
--       have : ∀ t, IsSmooth (f t) := sorry_proof
--       fun_trans
--       fun_trans
--       unfold tangentMap 
--       fun_trans
--       try simp
--       done


-- function_properties SciLean.forward_euler_step {X : Type} [SemiHilbert X] (f : ℝ → X → X) (t₀ : ℝ) (x₀ : X) (Δt : ℝ)
-- argument x₀  --[∀ t, HasAdjDiff λ (x : X) => f t x]

--   noncomputable abbrev ℛ := 
--     let Rf := ℛ (λ x' => f t₀ x') x₀
--     (x₀ + Δt • Rf.1, λ y' => y' + Δt • Rf.2 y')
--     by
--       unfold forward_euler_step
--       ignore_fun_prop
--       conv => 
--         rhs
--         fun_trans
--       conv => 
--         lhs
--         fun_trans
--       simp -- bugs in reverseMode transform
    

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

