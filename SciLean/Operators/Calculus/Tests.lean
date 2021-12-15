import SciLean.Basic
-- import SciLean.Simp
import SciLean.Tactic

set_option synthInstance.maxHeartbeats 50000
-- set_option maxHeartbeats 500000

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
  example (r dr : ℝ) : δ (λ x : ℝ => x*x*x + x) r dr = (dr * r + r * dr) * r + (r * r + 1) * dr := by autodiff done

  variable (u du u' : U) (v dv : V)
  example : δ (λ u : U => ⟪u,u'⟫) u du = ⟪du,u'⟫ := by simp done
  example : δ (λ u : U => ⟪u',u⟫) u du = ⟪u',du⟫ := by simp done
  -- example : δ (λ u : U => ⟪u, u⟫) u du = ⟪du, u⟫ + ⟪u, du⟫ := by simpx done
  -- example : δ (λ u : U => ⟪⟪u,u⟫*u, u⟫) u du = (⟪du,u⟫ + ⟪u,du⟫)*⟪u,u⟫ + ⟪u,u⟫*(⟪du,u⟫ + ⟪u,du⟫) := by
  -- simp done
  -- example (v : U) (m k : ℝ) : δ (λ u : U => (1/(2*m))*⟨u,u⟩ + (k/2)*⟨v,v⟩) u du = (1/(2*m))*(⟨du,u⟩ + ⟨u,du⟩) := by simp done

  section GradientTests

  end GradientTests

  -- section DifferentiatingSums

  --   open NDVector
  --   example : IsLin (sum : (Fin n → X) → X) := by infer_instance
  --   -- example : IsLin (λ (x : NDVector [n]) i => x.lget i) := by infer_instance

  --   variable {dims} (x dx : NDVector dims) [NonZero dims.product] (a : Fin dims.product) 

  --   example : δ (λ x => ∑ i, x[i]) x dx = ∑ i, dx[i] := by simp done
  --   example : δ (λ x => ∑ i, 2*x[i]) x dx = ∑ i, 2*dx[i] := by simp done
  --   example : δ (λ x => (∑ i, x[i]*x[i])) x dx = ∑ i, dx[i]*x[i] + x[i]*dx[i] := by autodiff done
  --   example : ∇ (λ x => ∑ i, x[i]) x = lmk (λ i => 1) := by autograd done
  --   example : ∇ (λ x => ∑ i, x[i]*x[i]) x = (2:ℝ)*x := by autograd done

  --   example : ∇ (λ x => ∑ i, x[i]*x[i-a]) x = ((lmk λ i => x[i-a]) + (lmk λ i => x[i+a])) := by autograd done
  --   -- example : ∇ (λ x => ∑ i, (x[i+a] - x[i])*(x[i+a] - x[i])) x = 0 := by autograd done -- Needs some more sophisticated simplifications

    -- variable {n : Nat} [NonZero n] (a : Fin n)

    -- example : ∇ (λ (f : Fin n → ℝ) => ∑ i, (f (i+a) - f i)*(f (i+a) - f i)) 
    --           = 
    --           (λ (f : Fin n → ℝ) i => 2 * (f (i - a + a) - f (i - a) - (f (i + a) - f i))) := by autograd done
  --   example (c : ℝ) : ∇ (λ (f : Fin n → ℝ) => ∑ i, c*(f i)*(f i)) = (λ (f : Fin n → ℝ) => (2:ℝ)*c*f) := by autograd done
    
  -- end DifferentiatingSums

  section integral

    variable (f df : ℝ ⟿ ℝ)

    example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, f t)) f df = ∫ t, df t := by
      simp[mkIntegral] done

    instance : IsLin (Subtype.val : (X ⟿ Y) → (X → Y)) := by infer_instance

    @[simp high] theorem differential_of_hom_subtype {X Y} [Vec X] [Vec Y] : δ (Subtype.val : (X ⟿ Y) → (X → Y)) = λ f df => df.1 := sorry

    example : δ (λ (f : (ℝ ⟿ ℝ)) (t : ℝ) => (f t) * (f t)) f df = λ t => (df t) * (f t) + (f t) * (df t) :=
    by
      autodiff done
      done



    -- @[simp] theorem zero_app {α β : Type} [Numerics β] {a : α} : (0 : α → β) a = (0 : β) := sorry

    -- set_option maxHeartbeats 100000

    -- -- set_option trace.Meta.whnf true in
    -- example : δ (λ (f : (ℝ ⟿ ℝ)) (t : ℝ) => (f t) * (f t) + (f t)) f df = λ t => (df t) * (f t) + (f t + 1) * (df t) :=
    -- by
    --   autodiff
    --   done


    -- example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, (f t) * (f t))) f df = 0 := by
    --   simp[mkIntegral]
    --   conv in (δ _) =>
    --     enter [f, df]
    --     simp
    --     ext t
    --   done

    -- instance : IsLin (λ (f : X ⟿ Y) x => f x) := sorry
    -- set_option trace.Meta.Tactic.simp true in
    -- example (f df : ℝ → ℝ) (x : ℝ) : δ (λ (f : ℝ → ℝ) x => (f x) * (f x)) f df x = 0 := by
    -- simp
    -- done

    -- example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, (f t) * (f t))) f df = ∫ t, (df t)*(f t) + (f t)*(df t) := 
    -- by
    --   simp[mkIntegral]
    --   done

  end integral

end Differential.Tests
