import SciLean.Operators.Calculus.Differential

namespace SciLean.BackPropagation

variable {α β γ α' β': Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {U V W : Type} [Hilbert U] [Hilbert V] [Hilbert W]

instance (f : U → V) [IsSmooth f] : IsSmooth (𝓑 f) := sorry

-- def Prod.fmap (f : α → β) (g : α' → β') : α×α' → β×β' := λ (a,a') => (f a, g a')

@[simp]
theorem backprop_of_linear 
        (f : U → V) [IsLin f] 
        (x : U)
        : 𝓑 f x = (f x, f†) := 
by 
  simp[backprop]; conv in (δ _ _) => enter [dx]
  done

-- @[simp]
-- theorem backprop_of_uncurried_linear_1 (f : U → V → W) [IsLin (λ xy : U×V => f xy.1 xy.2)]
--     (x : U) (y : V)
--     : 𝓑 (λ x => f x y) x = (f x y, (λ x => f x 0)†) :=
-- by 
--   simp[backprop]; conv in (δ _ _) => enter [dx]
--   simp; done

-- @[simp]
-- theorem backprop_of_uncurried_linear_2 
--         (f : U → V → W) [IsLin (λ xy : U×V => f xy.1 xy.2)]
--         (x : U) (y : V)
--         : 𝓑 (f x) y = (f x y, (f 0)†) :=
-- by
--    simp[backprop]; conv in (δ _ _) => enter [dy]
--    simp; done

-- @[simp] 
-- theorem backprop_of_id
--     : 𝓣 (λ (x : X) => x) = (λ xdx => xdx) := 
-- by 
--   funext xdx; simp; done  

-- @[simp] 
-- theorem backprop_of_id'
--     : 𝓣 (id : X → X) = id := 
-- by 
--   funext x; simp[id]; done

-- -- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem backprop_of_composition_1 (f : V → W) [IsSmooth f] (g : U → V) [IsSmooth g]
    : 𝓑 (λ x => f (g x)) = (λ x => (𝓑 f • 𝓑 g) x) := 
by
  funext x; simp[backprop, Function.comp, backcomp]; conv in (δ _ _) => enter [dx]
  done

-- -- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem backprop_of_composition_1_alt (f : V → W) [IsSmooth f] (g : U → V) [IsSmooth g]
    : 𝓑 (f ∘ g) = (𝓑 f • 𝓑 g) := 
by
  simp[Function.comp]; done

-- -- TODO: Change IsSmooth to IsDiff
-- -- TODO: Isn't there a better form of this?
-- @[simp] 
-- theorem backprop_of_composition_2 (f : Y → Z) [IsSmooth f] (gdg : (α → Y)×(α → Y))
--     : 𝓣 (λ (g : α → Y) (a : α) => f (g a)) gdg = (λ a => f (gdg.1 a), λ a => δ f (gdg.1 a) (gdg.2 a)) := 
-- by
--   simp[backprop]; induction gdg; simp; funext a; simp; done

-- -- TODO: Change IsSmooth to IsDiff
-- -- composition is already linear in `f` so probably no need for this other then short-circuiting 
-- -- @[simp] 
-- -- theorem backprop_of_composition_3 (fdf : (β → Z)×(β → Z))
-- --     : 𝓣 (λ (f : β → Z) (g : α → β) (a : α) => f (g a)) = ...


