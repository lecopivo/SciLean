import SciLean.Linear.Basic
import SciLean.Linear.Combinators
import SciLean.Linear.Adjoint

-- import SciLean.Affine.Combinators
-- import SciLean.IsZero.Basic
import SciLean.Meta

variable {α β γ : Type} 
variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {U : Type} {V : Type} {W : Type} [Hilbert U] [Hilbert V] [Hilbert W]

theorem test1 (f : X → X) [IsLin f] : IsLin (comp (comp f f) (comp f (comp f f))) := by infer_instance
theorem test2 (f : β → X → Y) (g : α → β) (a : α) [IsLin (f (g a))] : IsLin (comp f g a) := by infer_instance
theorem test3 (w : U) : IsLin λ u v : U => ⟨u, v + w⟩ := by rmlamlet; infer_instance
theorem test4 (w : U) : IsLin λ u : U => u := by rmlamlet; infer_instance
theorem test5  : IsLin λ u : X => u + u := by rmlamlet; infer_instance
theorem test6 (w : U) : IsLin λ u : U => ⟨u, w⟩ + ⟨u, w⟩ := by rmlamlet; infer_instance
theorem test7 (w : U) : IsLin λ u : U => ⟨u, w⟩ + ⟨w, ⟨(5 : ℝ)*u, w⟩*w⟩ := by rmlamlet; infer_instance
theorem test8  : IsLin λ u : X => u + u + u := by rmlamlet; infer_instance
theorem test9  : IsLin λ u : X => u + ((3 : ℝ) * u + u) + u := by rmlamlet; infer_instance
theorem test10 (A : X → X) [IsLin A] : IsLin λ u : X => (u + ((u + A u) + (10 : ℝ)*u) + u) + u := by rmlamlet; infer_instance
theorem test11 (A : X → X) (B : X → X) [IsLin A] [IsLin B] : IsLin λ x => A x + B (A (B x) + B x) := by rmlamlet; infer_instance

set_option trace.Meta.synthInstance true

-- theorem test8 (w : U) : IsLin λ u : U => ⟨u, u⟩ := by rmlamlet; infer_instance


-- theorem ttest9 : (λ x y : U => x + y) = 0 := by rmlamlet; admit
-- theorem ttest10 : (λ x y : U => y + x) = 0 := by rmlamlet; admit

-- theorem ttest11 (f : X → Y) : (λ x y => f x + y) = 0 := by rmlamlet; admit
-- theorem ttest12 (f : X → Y) : (λ x y => x + f y) = 0 := by rmlamlet; admit
-- theorem ttest13 (f : X → Y) : (λ x y => f y + x) = 0 := by rmlamlet; admit
-- theorem ttest14 (f : X → Y) : (λ x y => y + f x) = 0 := by rmlamlet; admit


-- theorem ttest15 (f : X → Z) (f' : Y → Z) : (λ x y => f x + f' y) = 0 := by rmlamlet; admit
-- theorem ttest16 (f : X → Z) (f' : Y → Z) : (λ x y => f' x + f y) = 0 := by rmlamlet; admit
-- theorem ttest17 (f : X → Z) (f' : Y → Z) : (λ x y => f y + f' x) = 0 := by rmlamlet; admit
-- theorem ttest18 (f : X → Z) (f' : Y → Z) : (λ x y => f' y + f x) = 0 := by rmlamlet; admit


-- theorem ttest9 (f : X → Z) (g : Y → Z) : (λ x y => f x + y) = 0 := by rmlamlet; admit
-- theorem test9 (f : X → Z) (g : Y → Z) : (λ x y => f x + g y) = 0 := by rmlamlet; admit
-- theorem test9 (f : X → Z) (g : Y → Z) : (λ x y => g y + f x) = 0 := by rmlamlet; admit
