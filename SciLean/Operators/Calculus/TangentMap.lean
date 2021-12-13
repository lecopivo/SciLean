import SciLean.Operators.Calculus.Differential

namespace SciLean.TangentMap

variable {α β γ α' β': Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]


instance (f : X → Y) [IsSmooth f] : IsSmooth (𝓣 f) := sorry

-- def Prod.fmap (f : α → β) (g : α' → β') : α×α' → β×β' := λ (a,a') => (f a, g a')

-- TODO: Move this elsewhere
@[simp] 
theorem prod_merge_back (ab : α×β) : (ab.1, ab.2) = ab := by induction ab; simp; done

@[simp]
theorem tangent_map_of_linear (f : X → Y) [IsLin f] (xdx : X×X)
    : 𝓣 f xdx = (f xdx.1, f xdx.2) := 
by 
  induction xdx; simp[tangent_map]; done
    -- 𝓣 f xdx = Prod.fmap f f xdx 

-- @[simp]
-- theorem tangent_map_of_uncurried_linear_1 (f : X → Y → Z) [IsLin (λ xy : X×Y => f xy.1 xy.2)]
--     (xdx : X×X)
--     : 𝓣 f xdx = (λ y => f xdx.1 y, λ (y : Y) => f xdx.2 0) :=
-- by 
--   induction xdx; simp[tangent_map]; funext y; simp; done

-- @[simp]
-- theorem tangent_map_of_uncurried_linear_2 (f : X → Y → Z) [IsLin (λ xy : X×Y => f xy.1 xy.2)]
--     (x : X) (ydy : Y×Y)
--     : 𝓣 (f x) ydy = (f x ydy.1, f 0 ydy.2) :=
-- by
--   induction ydy; simp[tangent_map]; done

@[simp] 
theorem tangent_map_of_id
    : 𝓣 (λ (x : X) => x) = (λ xdx => xdx) := 
by 
  funext xdx; simp; done

@[simp] 
theorem tangent_map_of_id'
    : 𝓣 (id : X → X) = id := 
by 
  funext x; simp[id]; done

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem tangent_map_of_composition_1 (f : Y → Z) [IsSmooth f] (g : X → Y) [IsSmooth g]
    : 𝓣 (λ x => f (g x)) = (λ xdx => 𝓣 f (𝓣 g xdx)) := 
by
  funext (x,dx); simp[tangent_map]; done

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem tangent_map_of_composition_1_alt (f : Y → Z) [IsSmooth f] (g : X → Y) [IsSmooth g]
    : 𝓣 (f ∘ g) = (𝓣 f ∘ 𝓣 g) := 
by
  funext xdx; induction xdx; simp[tangent_map, Function.comp]; done

-- TODO: Change IsSmooth to IsDiff
-- TODO: Isn't there a better form of this?
set_option synthInstance.maxHeartbeats 5000
                         
@[simp] 
theorem tangent_map_of_composition_2 (f : Y → Z) [IsSmooth f] (gdg : (α → Y)×(α → Y))
    : 𝓣 (λ (g : α → Y) (a : α) => f (g a)) gdg = (λ a => f (gdg.1 a), λ a => δ f (gdg.1 a) (gdg.2 a)) := 
by  
  simp[tangent_map]; done

-- TODO: Change IsSmooth to IsDiff
-- composition is already linear in `f` so probably no need for this other then short-circuiting 
-- @[simp] 
-- theorem tangent_map_of_composition_3 (fdf : (β → Z)×(β → Z))
--     : 𝓣 (λ (f : β → Z) (g : α → β) (a : α) => f (g a)) = ...

