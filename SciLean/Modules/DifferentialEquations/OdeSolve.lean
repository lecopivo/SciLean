import SciLean.Core
import SciLean.Data.Curry

set_option linter.unusedVariables false

namespace SciLean

variable {R : Type _} [IsROrC R] {X : Type _} [Vec R X]

set_default_scalar R

def IsOdeSolution (f : R → X → X) (t₀ : R) (x₀ : X) (x : R → X) : Prop :=
  (∀ t, (∂ x) t = f t (x t))
  ∧
  x t₀ = x₀

structure HasOdeSolution (f : R → X → X) : Prop where
  ex : ∀ t₀ x₀, ∃ x, IsOdeSolution f t₀ x₀ x

structure HasUniqueOdeSolution (f : R → X → X) extends HasOdeSolution f : Prop where
  uniq : ∀ t₀ x₀ x x', IsOdeSolution f t₀ x₀ x → IsOdeSolution f t₀ x₀ x' → x = x'
            
open Classical in
noncomputable
def odeSolve (f : R → X → X) (t₀ t : R) (x₀ : X) : X :=
  if h : HasUniqueOdeSolution f -- TODO: can we reduce it to just HasOdeSolution? 
  then Classical.choose (h.ex t₀ x₀) t
  else Classical.arbitrary X

section OnVec

variable 
  {R : Type _} [IsROrC R] 
  {W : Type _} [Vec R W]
  {X : Type _} [Vec R X]
  {Y : Type _} [Vec R Y]
  {Z : Type _} [Vec R Z]

@[fprop]
theorem odeSolve.arg_ft₀tx₀.IsDifferentiable_rule
  (f : W → R → X → X) (t₀ t : W → R) (x₀ : W → X) 
  (hf : IsDifferentiable R (fun (w,t,x) => f w t x)) 
  (ht₀ : IsDifferentiable R t₀) (ht : IsDifferentiable R t)
  (hx : IsDifferentiable R x₀)
  : IsDifferentiable R fun w => odeSolve (f w) (t₀ w) (t w) (x₀ w) := sorry_proof


@[ftrans]
theorem odeSolve.arg_ft₀tx₀.cderiv_rule
  (f : W → R → X → X) (t₀ t : W → R) (x₀ : W → X) 
  (hf : IsDifferentiable R (fun (w,t,x) => f w t x)) 
  (ht₀ : IsDifferentiable R t₀) (ht : IsDifferentiable R t)
  (hx : IsDifferentiable R x₀)
  : cderiv R (fun w => odeSolve (f w) (t₀ w) (t w) (x₀ w))
    =
    fun w dw => 
      let t₀dt₀ := fwdCDeriv R t₀ w dw
      let tdt   := fwdCDeriv R t₀ w dw
      let x₀dx₀ := fwdCDeriv R x₀ w dw
      let Tf := fwdCDeriv R (fun wkx : W×R×X => f wkx.1 wkx.2.1 wkx.2.2)

      let F := fun (t : R) (xdx : X×X) =>
        let x  := xdx.1
        let dx := xdx.2
        Tf (w,t,x) (dw,t₀dt₀.2,dx)

      let xdx := odeSolve F (t₀dt₀.1) (tdt.1) x₀dx₀

      (xdx.2 + tdt.2 • f w tdt.1 xdx.1)
    := sorry_proof


@[ftrans]
theorem odeSolve.arg_ft₀tx₀.fwdCDeriv_rule
  (f : W → R → X → X) (t₀ t : W → R) (x₀ : W → X) 
  (hf : IsDifferentiable R (fun (w,t,x) => f w t x)) 
  (ht₀ : IsDifferentiable R t₀) (ht : IsDifferentiable R t)
  (hx : IsDifferentiable R x₀)
  : fwdCDeriv R (fun w => odeSolve (f w) (t₀ w) (t w) (x₀ w))
    =
    fun w dw => 
      let t₀dt₀ := fwdCDeriv R t₀ w dw
      let tdt   := fwdCDeriv R t₀ w dw
      let x₀dx₀ := fwdCDeriv R x₀ w dw
      let Tf := fwdCDeriv R (fun wkx : W×R×X => f wkx.1 wkx.2.1 wkx.2.2)

      let F := fun (t : R) (xdx : X×X) =>
        let x  := xdx.1
        let dx := xdx.2
        Tf (w,t,x) (dw,t₀dt₀.2,dx)

      let xdx := odeSolve F (t₀dt₀.1) (tdt.1) x₀dx₀

      (xdx.1, xdx.2 + tdt.2 • f w tdt.1 xdx.1) := 
by 
  (conv => lhs; unfold fwdCDeriv)
  ftrans
  funext w dw
  simp[fwdCDeriv]
  sorry_proof
      

@[fprop]
theorem odeSolve.arg_x₀.IsContinuousLinearMap_rule
  (f : R → X → X) (t₀ t : R) (x₀ : W → X)
  (hf : ∀ t, IsContinuousLinearMap R (f t)) (hx₀ : IsContinuousLinearMap R x₀)
  : IsContinuousLinearMap R (fun w => odeSolve f t₀ t (x₀ w)) := sorry_proof

end OnVec

section OnSemiInnerProductSpace

variable 
  {R : Type _} [IsROrC R] 
  {W : Type _} [SemiInnerProductSpace R W]
  {X : Type _} [SemiInnerProductSpace R X]
  {Y : Type _} [SemiInnerProductSpace R Y]
  {Z : Type _} [SemiInnerProductSpace R Z]

@[fprop]
theorem odeSolve.arg_x₀.HasSemiAdjoint_rule
  (f : R → X → X) (t₀ t : R) (x₀ : W → X)
  (hf : ∀ t, HasSemiAdjoint R (f t)) (hx₀ : HasSemiAdjoint R x₀)
  : HasSemiAdjoint R (fun w => odeSolve f t₀ t (x₀ w)) := sorry_proof

@[ftrans]
theorem odeSolve.arg_x₀.semiAdjoint_rule
  (f : R → X → X) (t₀ t : R) (x₀ : W → X)
  (hf : ∀ t, HasSemiAdjoint R (f t)) (hx₀ : HasSemiAdjoint R x₀)
  : semiAdjoint R (fun w => odeSolve f t₀ t (x₀ w))
    =
    fun x₀' => 
      let f' := (fun s y => - semiAdjoint R (f s) y)
      let y := odeSolve f' t t₀ x₀'
      semiAdjoint R x₀ y := 
by
  -- Define adjoint solution `y` such that
  -- ∀ s, ⟪x s, y s⟫ = constant
  -- and `y t = x₀'`
  -- Now pick s := t and s := t₀ and we get the following relation:
  --    ⟪x t, x₀'⟫ = ⟪x t₀, y t₀⟫
  -- We know that `x t = S (x t₀)`, where S is the evolution operator we want to find adjoint of.
  -- Thus `y t₀ = S† x₀'`
  --
  -- We can show that `y` satisfies diffrential equation `ⅆ y t = -(f t)† (y t)`
  -- by differentiating `⟪x s, y s⟫` w.r.t. to `s`
  -- 
  -- Therefore we can express `y t₀` using `odeSolve`
  sorry_proof



@[fprop]
theorem odeSolve.arg_ft₀tx₀.HasAdjDiff_rule
  (f : W → R → X → X) (t₀ t : W → R) (x₀ : W → X) 
  (hf : HasAdjDiff R (fun (w,t,x) => f w t x)) 
  (ht₀ : HasAdjDiff R t₀) (ht : HasAdjDiff R t)
  (hx : HasAdjDiff R x₀)
  : HasAdjDiff R fun w => odeSolve (f w) (t₀ w) (t w) (x₀ w) := sorry_proof


@[ftrans]
theorem odeSolve.arg_x₀.revCDeriv_rule
  (f : R → X → X) (t₀ t : R) (x₀ : W → X) 
  (hf : HasAdjDiff R (fun (t,x) => f t x)) 
  (hx : HasAdjDiff R x₀)
  : revCDeriv R (fun w => odeSolve f t₀ t (x₀ w))
    =
    fun w =>
      let x₀dx₀ := revCDeriv R x₀ w
      let x := hold $ λ s => odeSolve f t₀ s x₀dx₀.1
      let dfdx := hold λ s dx' => - gradient R (fun x' => f s x') (x s) dx'
      (x t, 
       fun dx => 
         let dx := odeSolve dfdx t₀ t dx
         x₀dx₀.2 dx) := 
by
  unfold gradient revCDeriv hold
  ftrans; 
  funext w; simp
  -- set_option trace.Meta.Tactic.simp.discharge true in
  -- set_option trace.Meta.Tactic.simp.unify true in
  -- set_option trace.Meta.Tactic.ftrans.step true in
  ftrans
  ftrans
  sorry_proof



end OnSemiInnerProductSpace
#exit


function_properties SciLean.odeSolve {X : Type} [Hilbert X]
  (f : ℝ → X → X) [∀ t, HasAdjDiff λ x : X => f t x] (t₀ : ℝ) (x₀ : X) (t : ℝ)
argument x₀
  HasAdjDiff := sorry_proof,
  noncomputable abbrev ∂† := 
    -- alternatives 
    --   fst:
        λ dx₀' =>
        let x := hold $ λ s => odeSolve f t₀ x₀ s 
        odeSolve (λ s dx' => - ∂† (x':= x s; dx'), f s x') t dx₀' t₀
      -- snd:
      --   λ dx₀' =>
      --   let F := λ s (xdx' : X×X) => 
      --              let x   := xdx'.1
      --              let dx' := xdx'.2
      --              (- (f s x),
      --               - ∂† (x':=x;dx'), f s x')
      --   let xt := odeSolve f t₀ x₀ t
      --   (odeSolve F t (xt, dx₀') t₀).2
      -- by sorry_proof
    by sorry_proof,
  noncomputable abbrev ℛ := 
    let x := hold $ λ s => odeSolve f t₀ x₀ s
    (x t, 
     λ dx₀' => 
       odeSolve (λ s dx' => - ∂† (x':= x s; dx'), f s x') t dx₀' t₀)
    by sorry_proof


theorem odeSolve.arg_fx₀.HasAdjDiff' {S X : Type} [Hilbert S] [Hilbert X]
  (f : S → ℝ → X → X) [IsSmooth λ stx : S×ℝ×X => f stx.1 stx.2.1 stx.2.2]
  [∀ t, HasAdjDiff (λ sx : S×X => f sx.1 t sx.2)]
  (t₀ : ℝ)
  (x₀ : S → X) [HasAdjDiff x₀]
  (t : ℝ)
  : HasAdjDiff λ s => odeSolve (f s) t₀ (x₀ s) t := sorry


theorem odeSolve.arg_fx₀.adjointDifferential_simp' {S X : Type} [Hilbert S] [Hilbert X]
  (f : S → ℝ → X → X) [IsSmooth λ stx : S×ℝ×X => f stx.1 stx.2.1 stx.2.2]
  [∀ t, HasAdjDiff (λ sx : S×X => f sx.1 t sx.2)]
  (t₀ : ℝ)
  (x₀ : S → X) [HasAdjDiff x₀]
  (t : ℝ)
  : (∂† s, odeSolve (f s) t₀ (x₀ s) t)
    =
    -- alternatives 
    --   fst:

        fun s => 
          let x := λ t' => odeSolve (f s) t₀ (x₀ s) t'

          fun ds' =>

          let dfdx' := λ t x dx' => ∂† x':=x;dx', f s t x'
          let dfds' := λ t x ds' => ∂† s':=s;ds', f s' t x

          let F := λ (t : ℝ) (x' : X×S) =>
                   let α := x'.1
                   let β := x'.2
                   (dfdx' t (x t) α,
                    - dfds' t (x t) α)

          let x' := odeSolve F t (ds', 0) t₀
          let α := x'.1
          let β := x'.2
          ∂† x₀ s α + β
      -- snd:
      --   fun s ds' =>

      --     let dfdx' := λ t x dx' => ∂† x':=x;dx', f s t x'
      --     let dfds' := λ t x ds' => ∂† s':=s;ds', f s' t x

      --     let xt := odeSolve (f s) t₀ (x₀ s) t

      --     let F := λ (t : ℝ) (x' : X×X×S) =>
      --              let x := x'.1
      --              let α := x'.2.1
      --              let β := x'.2.2
      --              (f s t x,
      --               dfdx' t x α,
      --               - dfds' t x α)

      --     let x' := odeSolve F t (xt, ds', 0) t₀
      --     let α := x'.2.1
      --     let β := x'.2.2
      --     ∂† x₀ s α + β
      -- by sorry_proof
  := sorry_proof


theorem odeSolve.arg_fx₀.reverseDifferential_simp' {S X : Type} [Hilbert S] [Hilbert X]
  (f : S → ℝ → X → X) [IsSmooth λ stx : S×ℝ×X => f stx.1 stx.2.1 stx.2.2]
  [∀ t, HasAdjDiff (λ sx : S×X => f sx.1 t sx.2)]
  (t₀ : ℝ)
  (x₀ : S → X) [HasAdjDiff x₀]
  (t : ℝ)
  : (ℛ  λ s => odeSolve (f s) t₀ (x₀ s) t)
    =
    λ s => 
    let x := λ t' => odeSolve (f s) t₀ (x₀ s) t'
    (x t,
     fun ds' =>

       let dfdx' := λ t x dx' => ∂† x':=x;dx', f s t x'
       let dfds' := λ t x ds' => ∂† s':=s;ds', f s' t x

       let F := λ (t : ℝ) (x' : X×S) =>
                let α := x'.1
                let β := x'.2
                (dfdx' t (x t) α,
                 - dfds' t (x t) α)

       let x' := odeSolve F t (ds', 0) t₀
       let α := x'.1
       let β := x'.2
       ∂† x₀ s α + β)
  := sorry_proof

#eval show Lean.CoreM Unit from do

  addFunctionProperty ``odeSolve ``IsSmooth #[2,3,4,5].toArraySet none ``odeSolve.arg_ft₀x₀t.IsSmooth' none
  addFunctionProperty ``odeSolve ``differential #[2,3,4,5].toArraySet none ``odeSolve.arg_ft₀x₀t.differential_simp' none

  addFunctionProperty ``odeSolve ``HasAdjDiff #[2,4].toArraySet none ``odeSolve.arg_fx₀.HasAdjDiff' none
  addFunctionProperty ``odeSolve ``adjointDifferential #[2,4].toArraySet none ``odeSolve.arg_fx₀.adjointDifferential_simp' none
  addFunctionProperty ``odeSolve ``reverseDifferential #[2,4].toArraySet none ``odeSolve.arg_fx₀.reverseDifferential_simp' none


--------------------------------------------------------------------------------

variable {X Y Z} [Vec X] [Vec Y] [Vec Z]

def odeSolve_fixed_dt_impl (n : Nat) (stepper : (ℝ → X → X) → ℝ → X → ℝ → X) 
  (f : ℝ → X → X) (t₀ : ℝ) (x₀ : X) (t : ℝ) : X := 
Id.run do
  let Δt := (t-t₀)/n
  let mut x  := x₀
  let mut t' := t₀
  for _ in [0:n] do
    x := stepper f t' x Δt
    t' := t' + Δt
  x


def odeSolve_fixed_dt_impl' (n : Nat) (stepper : ℝ → X → ℝ → X) 
  (t₀ : ℝ) (x₀ : X) (t : ℝ) : X := 
Id.run do
  let Δt := (t-t₀)/n
  let mut x  := x₀
  let mut t' := t₀
  for _ in [0:n] do
    x := stepper t' x Δt
    t' := t' + Δt
  x


def odeSolve_fixed_dt_impl'' (n : Nat) (stepper : ℝ → X → ℝ → X×(X→X)) 
  (t₀ : ℝ) (x₀ : X) (t : ℝ) : X×(X→X) := 
Id.run do
  let Δt := (t-t₀)/n
  let mut x  := x₀
  let mut t' := t₀
  let mut df : X → X := id
  for _ in [0:n] do
    let (x', df') := stepper t' x Δt
    x := x'
    df := df ∘ df'
    t' := t' + Δt
  (x,df)


def odeSolve_fixed_dt_impl'.differential_simp (n : Nat) (stepper : ℝ → X → ℝ → X)
  (t₀ : ℝ) (t : ℝ)
  : (∂ x₀', odeSolve_fixed_dt_impl' n stepper t₀ x₀' t)
    =
    λ x₀ dx₀ =>
      let Tstepper := λ t' (xdx : X × X) Δt => 𝒯 (λ x' => stepper t' x' Δt) xdx.1 xdx.2
      (odeSolve_fixed_dt_impl' n Tstepper t₀ (x₀,dx₀) t).2
  := sorry


--- This requires some conditions on the function ... or just add the conclusion as an assumption
theorem odeSolve_fixed_dt (stepper : (ℝ → X → X) → ℝ → X → ℝ → X) 
  : odeSolve = limit (λ n => odeSolve_fixed_dt_impl n stepper) := sorry_proof



--  ___ _
-- / __| |_ ___ _ __ _ __  ___ _ _ ___
-- \__ \  _/ -_) '_ \ '_ \/ -_) '_(_-<
-- |___/\__\___| .__/ .__/\___|_| /__/
--             |_|  |_|

structure OdeStepper {X} [Vec X] (f : ℝ → X → X) where
  stepper : ℝ → X → ℝ → X
  -- The basic consistency condition is:
  -- is_valid : ∀ t x, lim Δt → 0, (stepper t x Δt - stepper x) / Δt = f t x
  -- there are probably others

def forward_euler_step  (f : ℝ → X → X) (t₀ : ℝ) (x₀ : X) (Δt : ℝ) : X := x₀ + Δt • f t₀ x₀

def forwardEulerStepper (f : ℝ → X → X) : OdeStepper f where
  stepper := forward_euler_step f

function_properties SciLean.forward_euler_step {X : Type} [Vec X] (f : ℝ → X → X) (t₀ : ℝ) (x₀ : X) (Δt : ℝ)
argument x₀ [IsSmooth λ (tx : ℝ×X) => f tx.1 tx.2]
  IsSmooth := by unfold forward_euler_step; sorry_proof,
  noncomputable abbrev ∂ := λ dx₀ =>
    dx₀ + Δt • (∂ x':=x₀;dx₀, f t₀ x')
    -- forward_euler_step Tf t₀ (x₀,dx₀) Δt
    by
      unfold forward_euler_step
      have : ∀ t, IsSmooth (f t) := sorry_proof 
      fun_trans
      simp, -- WTF where did the goal `True` came from?
  noncomputable abbrev 𝒯 := λ dx₀ =>
    let Tf := λ t (xdx : X×X) => 𝒯 (λ x' => f t x') xdx.1 xdx.2
    forward_euler_step Tf t₀ (x₀,dx₀) Δt
    by
      unfold forward_euler_step
      funext dx₀
      have : ∀ t, IsSmooth (f t) := sorry_proof
      fun_trans
      fun_trans
      unfold tangentMap 
      fun_trans
      try simp
      done


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

