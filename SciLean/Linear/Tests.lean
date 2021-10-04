import SciLean.Linear

-- import SciLean.Affine.Combinators
-- import SciLean.IsZero.Basic
import SciLean.Meta

section
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

end


section 

variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

variable (f : Y → Z) (g : X → Y) (A : Y ⇀ Z) (B : X ⇀ Y) [IsLin f] [IsLin g] 

-- def map1 : X ⇀ X := (λₗ x : X => x)
-- def map2 : X ⇀ X := (λₗ x : X => x + x)
-- def map3 : X ⇀ Y := (λₗ x : X => B x)
-- def map4 : X ⇀ Z := (λₗ x : X => f (B x))

end
