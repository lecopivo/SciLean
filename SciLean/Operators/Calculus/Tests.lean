import SciLean.Basic
-- import SciLean.Simp
import SciLean.Tactic.Basic

set_option synthInstance.maxHeartbeats 5000

namespace SciLean

macro "autodiff"    : conv => `(repeat' (conv => pattern (δ _); repeat' ext; simp))
macro "autoadjoint" : conv => `(repeat' (conv => pattern (adjoint _); repeat' ext; simp))
macro "autograd   " : conv => `(conv => pattern (∇ _); simp[gradient]; autodiff; autoadjoint; simp)

macro "autodiff"    : tactic => `(conv => autodiff)
macro "autoadjoint" : tactic => `(conv => autoadjoint)
macro "autograd   " : tactic => `(conv => autograd)

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

  example : IsSmooth (λ (g : X → Y) (x : X) => f3 (F x (g x))) := by infer_instance done
  example : IsSmooth (λ (g : X → X) (x : X) => F (g x) y) := by infer_instance done

  example : δ (λ x => x) x dx = dx := by simp done
  example : δ (λ x => f (g x)) x dx = δ f (g x) (δ g x dx) := by simp done
  example : δ (λ x => f (g (f1 x))) x dx = δ f (g (f1 x)) (δ g (f1 x) (δ f1 x dx)) := by simp done
  example : δ (λ (x : X) => F x (g x)) x dx = δ F x dx (g x) + δ (F x) (g x) (δ g x dx) := by simp  done
  example : δ (λ (x : X) => f3 (F x (g x))) x dx = δ f3 (F x (g x)) (δ F x dx (g x) + δ (F x) (g x) (δ g x dx)) := by simp done

  example g dg x : δ (λ (g : X → Y) => f (g x)) g dg = δ f (g x) (dg x) := by simp done
  example g dg x : δ (λ (g : X → Y) (x : X) => F x (g x)) g dg x = δ (F x) (g x) (dg x) := by simp done
  example g dg y : δ (λ (g : X → X) (x : X) => F (g x) y) g dg x = δ F (g x) (dg x) y := by simp done 
  example g dg x : δ (λ (g : X → X) (y : Y) => F (g x) y) g dg y = δ F (g x) (dg x) y := by simp done

  example (y x dx : X) : δ (λ x : X => y) x dx = 0 := by simp done
  example : δ (λ x => x + x) x dx = dx + dx := by simp done
  example (r dr : ℝ) : δ (λ x : ℝ => x*x + x) r dr = dr*r + (r + 1)*dr := by simp done
  example (r dr : ℝ) : δ (λ x : ℝ => x*x*x + x) r dr = (dr * r + r * dr) * r + (r * r + 1) * dr := by simp done

  variable (u du u' : U) (v dv : V)
  example : δ (λ u : U => ⟨u,u'⟩) u du = ⟨du,u'⟩ := by simp done
  example : δ (λ u : U => ⟨u, u⟩) u du = ⟨du, u⟩ + ⟨u, du⟩ := by simp done
  example : δ (λ u : U => ⟨⟨u,u⟩*u, u⟩) u du = (⟨du,u⟩ + ⟨u,du⟩)*⟨u,u⟩ + ⟨u,u⟩*(⟨du,u⟩ + ⟨u,du⟩) := by simp done
  example (v : U) (m k : ℝ) : δ (λ u : U => (1/(2*m))*⟨u,u⟩ + (k/2)*⟨v,v⟩) u du = (1/(2*m))*(⟨du,u⟩ + ⟨u,du⟩) := by simp done

  section GradientTests

  end GradientTests

  section DifferentiatingSums

    example : IsLin (sum : (Fin n → X) → X) := by infer_instance
    example : IsLin (λ (x : NDVector [n]) i => x.lget i) := by infer_instance

    example (x dx : NDVector [n]) : δ (λ x => ∑ i, x[i]) x dx = ∑ i, dx[i] := by simp done
    example (x dx : NDVector [n]) : δ (λ x => ∑ i, 2*x[i]) x dx = ∑ i, 2*dx[i] := by simp done
    example (x dx : NDVector [n]) : δ (λ x => (∑ i, x[i]*x[i])) x dx = ∑ i, dx[i]*x[i] + x[i]*dx[i] := by autodiff done
    example (x : NDVector [n]) : ∇ (λ x => ∑ i, x[i]) x = NDVector.lmk (λ i => 1) := by autograd done
    example (x : NDVector [n]) : ∇ (λ x => ∑ i, x[i]*x[i]) x = (2:ℝ)*x := by autograd done


    example (x : NDVector [n]) (a : Fin _) : ∇ (λ x => ∑ i, x[i]*x[i-a]) x = (2:ℝ)*x :=
    by
      autograd
      admit


    example {n} [NonZero n] (a : Fin n) 
            : ∇ (λ (f : Fin n → ℝ) => ∑ i, (f (i+a) - f i)*(f (i+a) - f i)) 
              = 
                (λ (f : Fin n → ℝ) i => 2 * (f (i - a + a) - f (i - a) - (f (i + a) - f i))) := 
    by autograd done

    example {n} [NonZero n] : ∇ (λ (f : Fin n → ℝ) => ∑ i, (1/2)*(f i)*(f i)) = (λ (f : Fin n → ℝ) => (2:ℝ)*(1/2)*f) := 
    by autograd done
    
    -- move to tests about adjoints
    example {dims} (a : Fin _) [NonZero dims.product] : (λ (x : NDVector dims) i => x[i - a])† = λ x => (NDVector.lmk λ i => x (i+a)) := by simp done
    example {n} (a : Fin n) [NonZero n] : (fun (x : Fin n → ℝ) i => x (i + a))† = (fun x i => x (i - a)) := by simp done
    
  end DifferentiatingSums

end Differential.Tests
