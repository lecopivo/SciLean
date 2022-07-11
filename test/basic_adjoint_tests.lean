import SciLean.Core.Functions

open Function

open SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Hilbert X] [Hilbert Y] [Hilbert Z] 

example (f : Y → Z) (g : X → Y) (z : Z) [HasAdjoint f] [HasAdjoint g] : (f ∘ g)† z = g† (f† z) := by simp done
example (f g : X → Y) [HasAdjoint f] [HasAdjoint g] (y : Y) : (λ x => f x + g x)† y = f† y + g† y := by simp

example (y : Y) (r : ℝ) 
  : (λ x => ⟪x,y⟫)† r = r*y := by simp done
example (y : X) (r : ℝ) 
  : (λ x => ⟪x,y⟫ + ⟪y,x⟫)† r = r * y + r * y := by simp done
example (r : ℝ) (x' : X) 
  : (λ x : X => r*((λ x'' => ⟪x', x''⟫) x))† = λ s => (r * s) * x' := by simp done

example {n : Nat} (a : Fin n) [Nonempty (Fin n)] 
  : (λ (f : Fin n → ℝ) i => f (i - a))† = (λ (f : Fin n → ℝ) x => f (x + a)) := 
  by funext f i; simp[sum_into_lambda]; done
example {ι} [Enumtype ι] 
  : (λ x : ι → X => sum x)† = (λ (x : X) (i : ι) => x) := by simp done
example {n} (c : Fin n)  [Nonempty (Fin n)] 
  : (λ (g : Fin n → ℝ) => (λ i => g (i+c)))† = (fun f x => f (x - c)) := by simp[Function.comp,sum_into_lambda]; done

example {ι} [Enumtype ι] (f : ι → X → Y) [∀ i, HasAdjoint (f i)] 
  : (λ x i => f i x)† = (λ y => ∑ i, (f i)† (y i)) := by funext y; simp done
example {ι} [Enumtype ι] [Nonempty ι] (f : ι → X → Y) [∀ i, HasAdjoint (f i)] 
  : (λ (g : ι → X) i => f i (g i))† = (λ h i => (1:ℝ) * ((f i)† (h i))) := by funext h i; simp[sum_into_lambda]; done

example (y : ℝ) : (λ x : ℝ => x * y)† 1 = ⟪1,y⟫ := by simp done
example (y : ℝ) : (λ x : ℝ => y * x)† 1 = y := by simp done

-- set_option trace.Meta.Tactic.simp.discharge true in
example (a b : ℝ) (x : X)
  : (λ dx : X => (a * ⟪x, dx⟫) * b)† 1 = (a * ⟪1,b⟫) * x := 
by simp; unfold hold; simp done

example {ι} [Enumtype ι] [Nonempty ι] (i : ι) (c : ℝ)
  : (fun (x : ι → ℝ) => x i * c)† 1 = (fun j => kron i j * ⟪1,c⟫)
  := by simp; unfold hold; simp done

example -- [NonZero n]
  : (λ (x : Fin n → ℝ) => sum λ i => x i)† 1 = (λ i => (1 : ℝ)) := by simp done

example {n} (f : Fin n → ℝ) (c : Fin n) [Nonempty (Fin n)] 
  : (λ (g : Fin n → ℝ) => sum (λ i => (f i) * (g (i+c))))† (1 : ℝ) = (fun i => f (i - c)) := by funext i; simp[sum_into_lambda]; done

-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
-- example {n} (f : Fin n → ℝ) [Nonempty (Fin n)] 
--   : (fun df : Fin n → ℝ => ∑ i, df i * f i + f i * df i)† 1 = λ i => ⟪1,f i⟫ + f i := by funext i; simp; unfold hold; simp; simp only [sum_into_lambda]; done

-- example {n} (f : Fin n → ℝ) (i : Fin n) [Nonempty (Fin n)]
--   : (λ (x : Fin n → ℝ) => x i * f i)† = λ (y : ℝ) j => kron i j * ⟪y, f i⟫
--   := by funext x j; simp; unfold hold; simp done


example {X Y : Type} [Hilbert X] [Hilbert Y] : (Prod.fst : X × Y → X)† = λ x : X => (x, 0) := by simp
example {X Y : Type} [Hilbert X] [Hilbert Y] : (Prod.snd : X × Y → Y)† = λ y : Y => (0, y) := by simp
example {X Y : Type} [Hilbert X] [Hilbert Y] : (λ ((x,y) : X × Y) => x)† = λ x : X => (x, (0:Y)) := by simp
example {X Y : Type} [Hilbert X] [Hilbert Y] : (λ ((x,y) : X × Y) => y)† = λ y : Y => ((0:X), y) := by simp
