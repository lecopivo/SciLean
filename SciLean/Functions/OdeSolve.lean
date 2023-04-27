import SciLean.Core
import SciLean.Functions.Limit
import SciLean.Alternatives

import Mathlib.Topology.Basic

namespace SciLean

-- TODO: Add Semi Group property for `f` that guarantees the existence
--       of solution for all times
noncomputable
opaque odeSolve {X : Type} [Vec X] (f : ℝ → X → X) (t₀ : ℝ) (x₀ : X) (t : ℝ) : X

function_properties SciLean.odeSolve {X : Type} [Vec X] (f : ℝ → X → X) [IsSmooth λ tx : ℝ×X => f tx.1 tx.2] (t₀ : ℝ) (x₀ : X) (t : ℝ)
argument (t₀,x₀,t)
  IsSmooth := sorry_proof,
  noncomputable abbrev ∂ := λ dt₀ dx₀ dt =>
    let F := λ (t : ℝ) (x' : X×X×X) => 
             let x := x'.1
             let dxdx₀ := x'.2.1
             let dxdt₀ := x'.2.2
             (f t x,
              (∂ x':=x;dxdx₀, f t x'),        
              (ⅆ t':=t, f t' x) + (∂ x':=x;dxdt₀, f t x'))
    let x' := odeSolve F t₀ (x₀, dx₀, 0) t
    dt • f t x'.1 + x'.2.1 + dt₀ • x'.2.2
    by sorry_proof,
  noncomputable abbrev 𝒯 := λ dt₀ dx₀ dt =>
    let F := λ (t : ℝ) (x' : X×X×X) => 
             let x := x'.1
             let dxdx₀ := x'.2.1
             let dxdt₀ := x'.2.2
             (f t x,
              (∂ x':=x;dxdx₀, f t x'),        
              (ⅆ t':=t, f t' x) + (∂ x':=x;dxdt₀, f t x'))
    let x' := odeSolve F t₀ (x₀, dx₀, 0) t
    (x'.1, dt • f t x'.1 + x'.2.1 + dt₀ • x'.2.2)
    by sorry_proof

function_properties SciLean.odeSolve {X : Type} [Vec X] (f : ℝ → X → X) [IsSmooth λ tx : ℝ×X => f tx.1 tx.2] (t₀ : ℝ) (x₀ : X) (t : ℝ)
argument t₀
  IsSmooth := by infer_instance,
  noncomputable abbrev ∂ := λ dt₀ => 
    let F := λ (t : ℝ) (x' : X×X) => 
             let x := x'.1
             let dxdt₀ := x'.2
             (f t x,
              (ⅆ t':=t, f t' x) + (∂ x':=x;dxdt₀, f t x'))
    let x' := odeSolve F t₀ (x₀, 0) t
    dt₀ • x'.2
    by sorry_proof,
  noncomputable abbrev 𝒯 := λ dt₀ =>
    let F := λ (t : ℝ) (x' : X×X) => 
             let x := x'.1
             let dxdt₀ := x'.2
             (f t x,
              (ⅆ t':=t, f t' x) + (∂ x':=x;dxdt₀, f t x'))
    let x' := odeSolve F t₀ (x₀, 0) t
    (x'.1, dt₀ • x'.2)
    by sorry_proof

function_properties SciLean.odeSolve {X : Type} [Vec X] (f : ℝ → X → X) [IsSmooth λ tx : ℝ×X => f tx.1 tx.2] (t₀ : ℝ) (x₀ : X) (t : ℝ)
argument x₀
  IsSmooth := by infer_instance,
  noncomputable abbrev ∂ := λ dx₀=>
    let F := λ (t : ℝ) (x' : X×X) => 
             let x := x'.1
             let dxdx₀ := x'.2
             (f t x,
              (∂ x':=x;dxdx₀, f t x'))
    let x' := odeSolve F t₀ (x₀, dx₀) t
    x'.2
    by sorry_proof,
  noncomputable abbrev 𝒯 := λ dx₀=>
    let F := λ (t : ℝ) (x' : X×X) => 
             let x := x'.1
             let dxdx₀ := x'.2
             (f t x,
              (∂ (x':=x;dxdx₀), f t x'))
    odeSolve F t₀ (x₀, dx₀) t
    by sorry_proof

function_properties SciLean.odeSolve {X : Type} [Vec X] (f : ℝ → X → X) [IsSmooth λ tx : ℝ×X => f tx.1 tx.2] (t₀ : ℝ) (x₀ : X) (t : ℝ)
argument t
  IsSmooth := by apply SciLean.odeSolve.arg_t₀x₀t.IsSmooth',
  noncomputable abbrev ∂ := λ dt => 
    dt • f t (odeSolve f t₀ x₀ t) 
    by sorry_proof,
  noncomputable abbrev 𝒯 := λ dt =>
    let x := odeSolve f t₀ x₀ t; 
    (x, dt • f t x) 
    by sorry_proof


function_properties SciLean.odeSolve {X : Type} [Vec X] (f : ℝ → X → X) [∀ t, IsLin λ x : X => f t x] (t₀ : ℝ) (x₀ : X) (t : ℝ)
argument x₀
  IsLin := sorry_proof


function_properties SciLean.odeSolve {X : Type} [Hilbert X] 
  (f : ℝ → X → X) [∀ t, HasAdjoint λ x : X => f t x] (t₀ : ℝ) (x₀ : X) (t : ℝ)
argument x₀
  HasAdjoint := sorry_proof,
  noncomputable abbrev † := λ x₀' =>
    odeSolve (λ s y => -(f s)† y) t  x₀' t₀
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

function_properties SciLean.odeSolve {X : Type} [Hilbert X] 
  (f : ℝ → X → X) [∀ t, HasAdjDiff λ x : X => f t x] (t₀ : ℝ) (x₀ : X) (t : ℝ)
argument x₀
  HasAdjDiff := sorry_proof,
  noncomputable abbrev ∂† := 
    alternatives 
      fst:
        λ dx₀' =>
        let x := λ s => odeSolve f t₀ x₀ s 
        odeSolve (λ s dx' => - ∂† (x':= x s; dx'), f s x') t dx₀' t₀
      snd:
        λ dx₀' =>
        let F := λ s (xdx' : X×X) => 
                   let x   := xdx'.1
                   let dx' := xdx'.2
                   (- (f s x),
                    - ∂† (x':=x;dx'), f s x')
        let xt := odeSolve f t₀ x₀ t
        (odeSolve F t (xt, dx₀') t₀).2
      by sorry_proof
    by sorry_proof



theorem odeSolve.arg_ft₀x₀t.IsSmooth' {S X : Type} [Vec S] [Vec X]
  (f : S → ℝ → X → X) [IsSmooth λ stx : S×ℝ×X => f stx.1 stx.2.1 stx.2.2]
  (t₀ : S → ℝ) [IsSmooth t₀]
  (x₀ : S → X) [IsSmooth x₀]
  (t : S → ℝ) [IsSmooth t]
  : IsSmooth λ s => odeSolve (f s) (t₀ s) (x₀ s) (t s) := sorry_proof

theorem odeSolve.arg_f.IsSmooth' {S X : Type} [Vec S] [Vec X]
  (f : S → ℝ → X → X) [IsSmooth λ stx : S×ℝ×X => f stx.1 stx.2.1 stx.2.2]
  (t₀ : ℝ) (x₀ : X) (t : ℝ) 
  : IsSmooth λ s => odeSolve (f s) t₀ x₀ t := sorry_proof

theorem odeSolve.arg_ft₀x₀t.differential_simp' {S X : Type} [Vec S] [Vec X]
  (f : S → ℝ → X → X) [IsSmooth λ stx : S×ℝ×X => f stx.1 stx.2.1 stx.2.2]
  (t₀ : S → ℝ) [IsSmooth t₀]
  (x₀ : S → X) [IsSmooth x₀]
  (t : S → ℝ) [IsSmooth t]
  : (∂ s, odeSolve (f s) (t₀ s) (x₀ s) (t s))
    =
    λ s ds =>

      let fs := f s
      let dfdx := λ t x dx => ∂ x':=x;dx, f s t x'
      let dfdt := λ t x    => ⅆ t':=t,    f s t' x
      let dfds := λ t x    => ∂ s':=s;ds, f s' t x
      let F := λ (t : ℝ) (x' : X×X×X×X) => 
               let x := x'.1
               let dxdf := x'.2.1
               let dxdx₀ := x'.2.2.1
               let dxdt₀ := x'.2.2.2
               (fs t x,
                (dfds t x + dfdx t x dxdf),
                (dfdx t x dxdx₀),        
                (dfdt t x + dfdx t x dxdt₀))

      let dx₀ := ∂ x₀ s ds
      let dt₀ := ∂ t₀ s ds
      let dt := ∂ t s ds

      let x' := odeSolve F (t₀ s) ((x₀ s), 0, dx₀, 0) (t s)
      dt • fs (t s) x'.1 + x'.2.1 + x'.2.2.1 + dt₀ • x'.2.2.2
    := sorry_proof

theorem odeSolve.arg_f.differential_simp' {S X : Type} [Vec S] [Vec X]
  (f : S → ℝ → X → X) [IsSmooth λ stx : S×ℝ×X => f stx.1 stx.2.1 stx.2.2]
  (t₀ : ℝ) (x₀ : X) (t : ℝ) 
  : (∂ s, odeSolve (f s) t₀ x₀ t)
    =
    λ s ds =>

      let fs := f s
      let dfdx := λ t x dx => ∂ x':=x;dx, f s t x'
      let dfds := λ t x    => ∂ s':=s;ds, f s' t x
      let F := λ (t : ℝ) (x' : X×X) => 
               let x := x'.1
               let dxdf := x'.2
               (fs t x,
                (dfds t x + dfdx t x dxdf))

      let x' := odeSolve F t₀ (x₀, 0) t
      x'.2
    := sorry_proof


-- register function transformations for ite
#eval show Lean.CoreM Unit from do

  addFunctionProperty ``odeSolve ``IsSmooth #[2,3,4,5].toArraySet none ``odeSolve.arg_ft₀x₀t.IsSmooth' none
  addFunctionProperty ``odeSolve ``differential #[2,3,4,5].toArraySet none ``odeSolve.arg_ft₀x₀t.differential_simp' none

  addFunctionProperty ``odeSolve ``IsSmooth #[2].toArraySet none ``odeSolve.arg_f.IsSmooth' none
  addFunctionProperty ``odeSolve ``differential #[2].toArraySet none ``odeSolve.arg_f.differential_simp' none


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

--- This requires some conditions on the function ... or just add the conclusion as an assumption
theorem odeSolve_fixed_dt (stepper : (ℝ → X → X) → ℝ → X → ℝ → X) 
  : odeSolve = limit (λ n => odeSolve_fixed_dt_impl n stepper) := sorry_proof

--  ___ _
-- / __| |_ ___ _ __ _ __  ___ _ _ ___
-- \__ \  _/ -_) '_ \ '_ \/ -_) '_(_-<
-- |___/\__\___| .__/ .__/\___|_| /__/
--             |_|  |_|

def forward_euler_step  (f : ℝ → X → X) (t₀ : ℝ) (x₀ : X) (Δt : ℝ) : X := x₀ + Δt • f t₀ x₀

def midpoint_step (f : ℝ → X → X) (t₀ : ℝ) (x₀ : X) (Δt : ℝ) : X := 
  let dt := Δt/2
  let x' := x₀ + dt • f t₀ x₀
  x₀ + Δt • (f (t₀+dt) x')

def runge_kutta4_step (f : ℝ → X → X) (t₀ : ℝ) (x₀ : X) (Δt : ℝ) : X :=
  let dt := Δt/2
  let k1 := f t₀ x₀
  let k2 := f (t₀+dt) (x₀ + dt • k1)
  let k3 := f (t₀+dt) (x₀ + dt • k2)
  let k4 := f (t₀+Δt) (x₀ + Δt • k3)
  x₀ + (Δt/6) • (k1 + (2:ℝ)•k2 + (2:ℝ)•k3 + k4)


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
