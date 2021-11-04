import SciLean.Operators.Calculus

namespace SciLean

namespace Differential.Tests

  variable {α β γ : Type}
  variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
  variable {U V W : Type} [Hilbert U] [Hilbert V] [Hilbert W]

  variable (f : Y → Z) [IsSmooth f]
  variable (g : X → Y) [IsSmooth g]
  variable (f1 : X → X) [IsSmooth f1]
  variable (f2 : Y → Y) [IsSmooth f2]
  variable (f3 : Z → Z) [IsSmooth f3]
  variable (F : X → Y → Z) [IsSmooth F] [∀ x, IsSmooth (F x)]
  variable (G : X × Y → Z) [IsSmooth G]

  variable (x dx : X) (y dy : Y) (z dz : Z)

  example : IsSmooth (λ (g : X → Y) (x : X) => f3 (F x (g x))) := by infer_instance; done
  example : IsSmooth (λ (g : X → X) (x : X) => F (g x) y) := by infer_instance; done

  example : δ (λ x => x) x dx = dx := by simp; done
  example : δ (λ x => f (g x)) x dx = δ f (g x) (δ g x dx) := by simp; done
  example : δ (λ x => f (g (f1 x))) x dx = δ f (g (f1 x)) (δ g (f1 x) (δ f1 x dx)) := by simp; done
  example : δ (λ (x : X) => F x (g x)) x dx = δ F x dx (g x) + δ (F x) (g x) (δ g x dx) := by simp;  done
  example : δ (λ (x : X) => f3 (F x (g x))) x dx = δ f3 (F x (g x)) (δ F x dx (g x) + δ (F x) (g x) (δ g x dx)) := by simp; done
  example (g dg) : δ (λ (g : X → Y) (x : X) => F x (g x)) g dg x = δ (F x) (g x) (dg x) := by simp; done
  example (g dg) : δ (λ (g : X → X) (x : X) => F (g x) y) g dg x = δ F (g x) (dg x) y := by simp; done 


  -- rw [differential_of_composition_2_1] done
  -- theorem test7 (g dg) : δ (λ (g : X → X) (x : X) (y : Y) => F (g x) y) g dg x y = δ F (g x) (dg x) y := by simp; done

  example (g dg) : δ (λ (g : X → X) (y : Y) => F (g x) y) g dg y = 0 := by simp; admit
  -- theorem test6 (g dg) : δ (λ (g : X → X) (x : X) => F x y) g dg x = 0 := by rw [differential_of_composition_2_1]; done



  example : δ (λ x => x + x) x dx = dx + dx := by simp; done
  example (r dr : ℝ) : δ (λ x : ℝ => x*x + x) r dr = dr*r + r*dr + dr := by simp; done
  example (r dr : ℝ) : δ (λ x : ℝ => x*x*x + x) r dr = dr*r + r*dr + dr := by simp; done

  instance : IsLin (λ u v : U => (u, v)_[SemiInner.domain]) := sorry
  instance (d) : IsLin λ u : U => (u, v)_[d] := sorry
  instance (d u) : IsLin (λ v : U => (u, v)_[d]) := sorry

  

  variable (u du u' : U) (v dv : V)
  example : IsLin λ u : U => ⟨u,u'⟩ := by infer_instance
  example : IsSmooth λ (u v : U) (d) => (u,v)_[d] := by infer_instance
  example (u) : IsSmooth λ (v : U) (d) => (u,v)_[d] := by infer_instance
  example : IsSmooth λ (u : U) (d) => (u,u)_[d] := by infer_instance
  example : δ (λ u : U => ⟨u,u'⟩) u du = ⟨du,u'⟩ := by simp; done
  set_option trace.Meta.Tactic.simp true
  example : δ (λ u : U => ⟨u,u⟩) u du = ⟨u, du⟩ + ⟨du,u⟩ := by simp; done

end Differential.Tests

