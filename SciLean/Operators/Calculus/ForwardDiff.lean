import SciLean.Operators.Calculus.DiffAtom

namespace SciLean.ForwardDiff

variable {α β γ α' β': Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

@[simp] 
theorem forward_diff_of_id
    : 𝓣 (λ (x : X) => x) = (λ xdx => xdx) := 
by 
  funext xdx; simp[forward_diff]; done

@[simp] 
theorem forward_diff_of_id'
    : 𝓣 (id : X → X) = id := 
by 
  funext x; simp[id]; done

@[simp] 
theorem forward_diff_of_composition_1 (f : Y → Z) [IsSmooth f] (g : X → Y) [IsSmooth g]
    : 𝓣 (λ x => f (g x)) = (λ xdx => 𝓣 f (𝓣 g xdx)) := 
by
  funext (x,dx); simp[forward_diff]; done

@[simp] 
theorem forward_diff_of_composition_1_alt (f : Y → Z) [IsSmooth f] (g : X → Y) [IsSmooth g]
    : 𝓣 (f ∘ g) = (𝓣 f ∘ 𝓣 g) := 
by
  funext xdx; induction xdx; simp[forward_diff, Function.comp]; done

@[simp] 
theorem forward_diff_of_composition_2 (f : Y → Z) [IsSmooth f] (gdg : (α → Y)×(α → Y))
    : 𝓣 (λ (g : α → Y) (a : α) => f (g a)) gdg = (λ a => f (gdg.1 a), λ a => δ f (gdg.1 a) (gdg.2 a)) := 
by  
  simp[forward_diff]; done

-- @[simp]
-- theorem forward_diff_of_linear (f : X → Y) [IsLin f] (xdx : X×X)
--     : 𝓣 f xdx = (f xdx.1, f xdx.2) := 
-- by 
--   induction xdx; simp[forward_diff]; done

-- @[simp]
-- theorem forward_diff_of_uncurried_linear_1 (f : X → Y → Z) [IsLin (λ xy : X×Y => f xy.1 xy.2)]
--     (xdx : X×X)
--     : 𝓣 f xdx = (λ y => f xdx.1 y, λ (y : Y) => f xdx.2 0) :=
-- by 
--   induction xdx; simp[forward_diff]; done

-- @[simp]
-- theorem forward_diff_of_uncurried_linear_2 (f : X → Y → Z) [IsLin (λ xy : X×Y => f xy.1 xy.2)]
--     (x : X) (ydy : Y×Y)
--     : 𝓣 (f x) ydy = (f x ydy.1, f 0 ydy.2) :=
-- by
--   induction ydy; simp[forward_diff]; done
