import SciLean.Operators.Calculus.Basic

namespace SciLean.Differential

variable {α β γ : Type}
variable {β1 β2 β3 β4 : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y1 Y2 Y3 Y4 : Type} [Vec Y1] [Vec Y2] [Vec Y3] [Vec Y4]

instance (f : X → Y) [IsSmooth f] (x : X) : IsLin (δ f x) := sorry
-- TODO: Change IsSmooth to IsDiff
instance (f : X → Y) [IsSmooth f] : IsSmooth (δ f) := sorry

@[simp] 
theorem differential_at_zero (f : X → Y) [IsSmooth f] (x : X)
        : δ f x 0 = 0 := sorry

-- Maybe this one two? Because we cannot have simp theorem stating `f 0 = 0` for linear `f`.
-- This is a simp theorem with variable head and that is not allowed.
-- @[simp] 
-- theorem differential_at_zero_comp (f : Y → Z) [IsSmooth f] (y : Y) (g : X → Y) [IsLin g]
--         : δ f y (g 0) = 0 := sorry

@[simp] 
theorem differential_of_linear (f : X → Y) [IsLin f] (x dx : X)
        : δ f x dx = f dx := sorry

@[simp] 
theorem differential_of_uncurried_linear_1 (f : X → Y → Z) [IsLin (λ xy : X×Y => f xy.1 xy.2)] 
        (x dx : X) (y : Y)
        : δ f x dx y = f dx 0 := sorry

@[simp] 
theorem differential_of_uncurried_linear_2 (f : X → Y → Z) [IsLin (λ xy : X×Y => f xy.1 xy.2)] 
        (x : X) (y dy : Y)
        : δ (f x) y dy = f 0 dy := sorry

@[simp] 
theorem differential_of_id (x dx : X)
        : δ (λ x => x) x dx = dx := by simp

@[simp] 
theorem differential_of_id'  (x dx : X)
        : δ (id) x dx = dx := by simp[id]

@[simp] 
theorem differential_of_constant (x dx : X) (y : Y)
        : δ (λ x => y) x dx = 0 := sorry

-- For some reason this theorem is usefull even though it is already solvable by simp
@[simp]
theorem differential_of_parm (f : X → β → Y) [IsSmooth f] (x dx)
        : δ (λ x => f x b) x dx = δ f x dx b := sorry

-- @[simp]
-- theorem differential_of_parm_rev (f : X → β → Y) (x dx : X) (b : β) [IsSmooth f] 
--         : δ f x dx b = δ (λ x => f x b) x dx := sorry

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem differential_of_composition_1 (f : Y → Z) (g : X → Y) (x dx : X)
        [IsSmooth f] [IsSmooth g]
        : δ (λ x => f (g x)) x dx = δ f (g x) (δ g x dx) := sorry

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem differential_of_composition_2 (f : Y → Z) (g dg : α → Y) (a : α)
        [IsSmooth f]
        : δ (λ (g : α → Y) (a : α) => f (g a)) g dg a = δ f (g a) (dg a) := sorry

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem differential_of_composition_3 (f df : β → Z) (g : α → β) (a : α)
        : δ (λ (f : β → Z) (g : α → β) (a : α) => f (g a)) f df g a = df (g a) := by simp

-- can have weaker assumption, [IsSmooth (λ y => f y b)]
@[simp]
theorem differential_of_composition_fix_parm_1 (f : Y → β → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] (x dx b) 
        : δ (λ x => f (g x) b) x dx = δ f (g x) (δ g x dx) b := by simp

@[simp]
theorem differential_of_composition_fix_parm_2 (f : Y → β → Z) [IsSmooth f] (a b) (g dg : α → Y)
        : δ (λ (g : α → Y) a => f (g a) b) g dg a = δ f (g a) (dg a) b := sorry

@[simp]
theorem differential_of_composition_parm_1 (f : Y → β → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] (x dx b) 
        : δ (λ x b => f (g x) b) x dx b = δ f (g x) (δ g x dx) b := sorry

@[simp]
theorem differential_of_composition_parm_2 (f : Y → β → Z) [IsSmooth f] (a b) (g dg : α → Y)
        : δ (λ (g : α → Y) a b => f (g a) b) g dg a b = δ f (g a) (dg a) b := sorry

@[simp] 
theorem differential_of_diag_1 (f : Y1 → Y2 → Z) (g1 : X → Y1) (g2 : X → Y2)
        [IsSmooth f] [∀ y1, IsSmooth (f y1)] [IsSmooth g1] [IsSmooth g2]
        (x dx : X)
        : δ (λ (x : X) => f (g1 x) (g2 x)) x dx = δ f (g1 x) (δ g1 x dx) (g2 x) + δ (f (g1 x)) (g2 x) (δ g2 x dx) := sorry

@[simp] 
theorem differential_of_diag_2 (f : Y1 → β2 → Z) (g2 : α → β2)
        [IsSmooth f]
        (g dg a)
        : δ (λ  (g1 : α → Y1) a => f (g1 a) (g2 a)) g dg a = δ f (g a) (dg a) (g2 a) := sorry

@[simp] 
theorem differential_of_diag_3 (f : β1 → Y2 → Z) (g1 : α → β1)
        [∀ y1, IsSmooth (f y1)] 
        (g dg a)
        : δ (λ (g2 : α → Y2) a => f (g1 a) (g2 a)) g dg a = δ (f (g1 a)) (g a) (dg a) := sorry


@[simp] 
theorem differential_of_diag_parm_1 (f : Y1 → Y2 → β → Z) (g1 : X → Y1) (g2 : X → Y2)
        [IsSmooth f] [∀ y1, IsSmooth (f y1)] [IsSmooth g1] [IsSmooth g2]
        (x dx : X) (b : β)
        : δ (λ (x : X) (b : β) => f (g1 x) (g2 x) b) x dx b = δ f (g1 x) (δ g1 x dx) (g2 x) b + δ (f (g1 x)) (g2 x) (δ g2 x dx) b := sorry


@[simp]
theorem differential_of_diag_parm_2 (f : Y1 → Y2 → Z) (g1 : X → β → Y1) (g2 : X → β → Y2)
        [IsSmooth f] [∀ y1, IsSmooth (f y1)] [IsSmooth g1] [IsSmooth g2]
        (x dx : X) (b : β)
        : δ (λ (x : X) (b : β) => f (g1 x b) (g2 x b)) x dx b = δ f (g1 x b) (δ g1 x dx b) (g2 x b) + δ (f (g1 x b)) (g2 x b) (δ g2 x dx b) := sorry 
