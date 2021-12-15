import SciLean.Basic
import SciLean.Simp
import SciLean.Tactic

open Function

open SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Hilbert X] [Hilbert Y] [Hilbert Z]

example (f g : X → Y) [HasAdjoint f] [HasAdjoint g] (y : Y) : (λ x => f x + g x)† y = f† y + g† y := by simp done
example (y : Y) (r : ℝ) : (λ x => ⟪x,y⟫)† r = r*y := by simp done
example (y : X) (r : ℝ) : (λ x => ⟪x,y⟫ + ⟪y,x⟫)† r = 2*r*y := by simp done
example (r : ℝ) (x' : X) : (λ x : X => r*((λ x'' => ⟪x', x''⟫) x))† = λ s => r * s * x' := by simp funext s; simp done
example : (λ (x : Fin n → ℝ) => sum λ i => x i)† 1 = (λ i => (1 : ℝ)) := by simp done
example {n : Nat} (a : Fin n) [NonZero n] : (λ (f : Fin n → ℝ) i => f (i - a))† = (λ (f : Fin n → ℝ) x => f (x + a)) := by simp funext f x; simp done
-- set_option trace.Meta.Tactic.simp true in
example {n} [NonZero n] (f : Fin n → ℝ) (c : Fin n) 
        : (λ (g : Fin n → ℝ) => sum (λ i => (f i) * (g (i+c))))† (1 : ℝ) = (fun i => f (i - c)) := by simp admit
-- example {n} [NonZero n] (f : Fin n → ℝ) (c : Fin n) 
--         : (λ (g : Fin n → ℝ) => ⟨f, λ i => (g (i+c))⟩)† (1 : ℝ) = (fun i => f (i - c)) := by  simp admit
example {n} [NonZero n] (c : Fin n) : (λ (g : Fin n → ℝ) => (λ i => g (i+c)))† = (fun f x => f (x - c)) := by autoadjoint admit

instance (y : ℝ) : HasAdjoint (λ x : ℝ => x * y) := by infer_instance done
instance (y : ℝ) : HasAdjoint (λ x : ℝ => y * x) := by infer_instance done
instance (y : ℝ) : (λ x : ℝ => x * y)† 1 = y := by simp done
instance (y : ℝ) : (λ x : ℝ => y * x)† 1 = y := by simp done

instance {ι} [Enumtype ι] (f : ι → ℝ) : HasAdjoint (λ (df : ι → ℝ) i => df i) := by infer_instance done
instance {ι} [Enumtype ι] (f : ι → ℝ) : HasAdjoint (λ (df : ι → ℝ) i => f i * df i) := by infer_instance done
instance {ι} [Enumtype ι] (f : ι → ℝ) : HasAdjoint (λ (df : ι → ℝ) i => df i * f i) := by infer_instance done
instance {ι} [Enumtype ι] (f : ι → ℝ) : HasAdjoint (λ (df : ι → ℝ) i => df i * f i + f i * df i) := by infer_instance done

example {ι} [Enumtype ι] (f : ι → ℝ) : (fun df : ι → ℝ => ∑ i, df i * f i + f i * df i)† 1 = (2 : ℝ) * f := by simp done
