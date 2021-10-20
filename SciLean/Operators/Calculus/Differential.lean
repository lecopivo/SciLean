import SciLean.Operators.Calculus.Basic

namespace SciLean.Differential

variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

instance (f : X → Y) [IsSmooth f] (x : X) : IsLin (δ f x) := sorry
-- TODO: Change IsSmooth to IsDiff
instance (f : X → Y) [IsSmooth f] : IsSmooth (δ f) := sorry

@[simp] 
theorem differential_of_linear (f : X → Y) [IsLin f] (x dx : X)
        : δ f x dx = f dx := sorry

-- @[simp] 
-- theorem differential_of_uncurried_linear_1 (f : X → Y → Z) [IsLin (λ xy : X×Y => f xy.1 xy.2)] 
--         (x dx : X) (y : Y)
--         : δ f x dx y = f dx 0 := sorry

-- @[simp] 
-- theorem differential_of_uncurried_linear_2 (f : X → Y → Z) [IsLin (λ xy : X×Y => f xy.1 xy.2)] 
--         (x : X) (y dy : Y)
--         : δ (f x) y dy = f 0 dy := sorry

--- This should follow from something else I think
-- @[simp] 
-- theorem differential_of_uncurried_linear_3 (f : X → Y → Z) [IsLin (λ xy : X×Y => f xy.1 xy.2)] 
--         (x dx: X) (y : Y)
--         : δ (λ x => f x y) x dx = f dx 0 := sorry

@[simp] 
theorem differential_of_id (x dx : X)
        : δ (λ x => x) x dx = dx := by simp

@[simp] 
theorem differential_of_id'  (x dx : X)
        : δ (id) x dx = dx := by simp[id]

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem differential_of_composition_1 (f : Y → Z) [IsSmooth f] (g : X → Y) [IsSmooth g] (x dx : X)
        : δ (λ x => f (g x)) x dx = δ f (g x) (δ g x dx) := sorry

-- TODO: Change IsSmooth to IsDiff
-- Probably not necessary
-- @[simp] 
-- theorem differential_of_composition_1_alt (f : Y → Z) [IsSmooth f] (g : X → Y) [IsSmooth g] (x dx : X)
--         : δ (f∘g) x dx = δ f (g x) (δ g x dx) := by simp[Function.comp]

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem differential_of_composition_2 (f : Y → Z) [IsSmooth f] (g dg : α → Y) (a : α)
        : δ (λ (g : α → Y) (a : α) => f (g a)) g dg a = δ f (g a) (dg a) := sorry


-- @[simp] 
-- theorem asdfasdf (f : X → Y → Z) [IsSmooth f] (x dx : X) (y : Y)
--         : δ (λ x => f x y) x dx = δ f x dx y := sorry

-- @[simp] 
theorem differential_of_composition_2_1 (f : Y → β → Z) (b : β) [IsSmooth (λ y => f y b)] (g dg : α → Y) (a : α)
        : δ (λ (g : α → Y) (a : α) => f (g a) b) g dg a = δ f (g a) (dg a) b := sorry

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem differential_of_composition_3 (f df : β → Z) (g : α → β) (a : α)
        : δ (λ (f : β → Z) (g : α → β) (a : α) => f (g a)) f df g a = df (g a) := by simp

-- @[simp] 
-- theorem differential_of_diag (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
--         (g : W → X) [IsSmooth g]
--         (h : W → Y) [IsSmooth h]
--         (w dw : W)
--         : δ (λ w => f (g w) (h w)) w dw = δ f (g w) (δ g w dw) (h w) + δ (f (g w)) (h w) (δ h w dw) := sorry


@[simp] 
theorem differential_of_subs_1 (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
        (g : X → Y) [IsSmooth g]
        (x dx : X)
        : δ (λ (x : X) => f x (g x)) x dx = δ f x dx (g x) + δ (f x) (g x) (δ g x dx) := sorry


@[simp] 
theorem differential_of_subs_2 (f : α → Y → Z) [∀ a, IsSmooth (f a)]
        (g dg : α → Y) (a : α)
        : δ (λ g (a : α) => f a (g a)) g dg a = δ (f a) (g a) (dg a) := sorry

