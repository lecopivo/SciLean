import SciLean.Operators.Calculus.Basic
import SciLean.Operators.Calculus.AtomicSmoothFun

namespace SciLean.Smooth

variable {α β γ : Type}
variable {β1 β2 β3 β4 : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y1 Y2 Y3 Y4 : Type} [Vec Y1] [Vec Y2] [Vec Y3] [Vec Y4]


asdfasdf make thid fail to compile

@[simp] 
theorem differential_at_zero (f : X → Y) [IsSmooth f] (x : X)
        : δ f x 0 = 0 := sorry

-- Maybe this one too? We cannot have simp theorem stating `f 0 = 0` for linear `f`.
-- This is a simp theorem with variable head and that is not allowed.
-- @[simp] 
-- theorem differential_at_zero_comp (f : Y → Z) [IsSmooth f] (y : Y) (g : X → Y) [IsLin g]
--         : δ f y (g 0) = 0 := sorry

@[simp high] 
theorem differential_of_id 
        : δ (λ x : X => x) = λ x dx => dx := sorry

@[simp low] 
theorem  differential_of_linear (f : X → Y) [IsLin f]
        : δ f = λ x dx => f dx := sorry

@[simp low] 
theorem differential_of_uncurried_linear_1 (f : X → Y → Z) [IsLin (λ xy : X×Y => f xy.1 xy.2)] 
        : δ f = λ x dx (y : Y) => f dx 0 := sorry

@[simp low] 
theorem differential_of_uncurried_linear_2 (f : X → Y → Z) [IsLin (λ xy : X×Y => f xy.1 xy.2)] (x : X)
        : δ (f x) = λ y dy => f 0 dy := sorry

@[simp] 
theorem differential_of_id'
        : δ (id : X → X) = λ x dx => dx := by simp[id]

@[simp] 
theorem differential_of_constant (y : Y)
        : δ (λ x : X => y) = λ x dx => (0 : Y) := sorry

-- For some reason this theorem is usefull even though it is already solvable by simp
@[simp]
theorem differential_of_parm (f : X → β → Y) [IsSmooth f]
        : δ (λ x => f x b) = λ x dx => δ f x dx b := sorry

-- @[simp]
-- theorem differential_of_parm_rev (f : X → β → Y) (x dx : X) (b : β) [IsSmooth f] 
--         : δ f x dx b = δ (λ x => f x b) x dx := sorry

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem differential_of_composition_1 (f : Y → Z) (g : X → Y)
        [IsSmooth f] [IsSmooth g]
        : δ (λ x => f (g x)) = λ x dx => δ f (g x) (δ g x dx) := sorry

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem differential_of_composition_2 (f : Y → Z)
        [IsSmooth f]
        : δ (λ (g : α → Y) (a : α) => f (g a)) = λ g dg a => δ f (g a) (dg a) := sorry 

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem differential_of_composition_3 
        : δ (λ (f : β → Z) (g : α → β) (a : α) => f (g a)) = λ f df (g : α → β) a => df (g a) := sorry

-- can have weaker assumption, [IsSmooth (λ y => f y b)]
@[simp]
theorem differential_of_composition_fix_parm_1 (f : Y → β → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] (b) 
        : δ (λ x => f (g x) b) = λ x dx => δ f (g x) (δ g x dx) b := sorry

@[simp]
theorem differential_of_composition_fix_parm_2 (f : Y → β → Z) [IsSmooth f] (b)
        : δ (λ (g : α → Y) a => f (g a) b) = λ g dg a => δ f (g a) (dg a) b := sorry

@[simp]
theorem differential_of_composition_parm_1 (f : β → Y → Z) (g : β → X → Y) [∀ b, IsSmooth (f b)] [∀ b, IsSmooth (g b)]
        : δ (λ x b => f b (g b x)) = λ x dx b => δ (f b) (g b x) (δ (g b) x dx) := sorry

@[simp]
theorem differential_of_composition_parm_2 (f : Y → β → Z) (g : X → Y) [IsSmooth f] [IsSmooth g]
        : δ (λ x b => f (g x) b) = λ x dx b => δ f (g x) (δ g x dx) b := sorry

@[simp]
theorem differential_of_composition_parm_3 (f : Y → β → Z) [IsSmooth f]
        : δ (λ (g : α → Y) a b => f (g a) b) = λ g dg a b => δ f (g a) (dg a) b := sorry

@[simp] 
theorem differential_of_diag_1 (f : Y1 → Y2 → Z) (g1 : X → Y1) (g2 : X → Y2)
        [IsSmooth f] [∀ y1, IsSmooth (f y1)] [IsSmooth g1] [IsSmooth g2]
        : δ (λ (x : X) => f (g1 x) (g2 x)) = λ x dx => δ f (g1 x) (δ g1 x dx) (g2 x) + δ (f (g1 x)) (g2 x) (δ g2 x dx) := sorry

@[simp] 
theorem differential_of_diag_2 (f : Y1 → β2 → Z) (g2 : α → β2)
        [IsSmooth f]
        (g dg)
        : δ (λ  (g1 : α → Y1) a => f (g1 a) (g2 a)) g dg = λ a => δ f (g a) (dg a) (g2 a) := sorry

@[simp] 
theorem differential_of_diag_3 (f : β1 → Y2 → Z) (g1 : α → β1)
        [∀ y1, IsSmooth (f y1)] 
        : δ (λ (g2 : α → Y2) a => f (g1 a) (g2 a)) = λ g dg a => δ (f (g1 a)) (g a) (dg a) := sorry


@[simp] 
theorem differential_of_diag_parm_1 (f : Y1 → Y2 → β → Z) (g1 : X → Y1) (g2 : X → Y2)
        [IsSmooth f] [∀ y1, IsSmooth (f y1)] [IsSmooth g1] [IsSmooth g2]
        : δ (λ (x : X) (b : β) => f (g1 x) (g2 x) b) = λ x dx b => δ f (g1 x) (δ g1 x dx) (g2 x) b + δ (f (g1 x)) (g2 x) (δ g2 x dx) b := sorry


@[simp]
theorem differential_of_diag_parm_2 (f : Y1 → Y2 → Z) (g1 : X → β → Y1) (g2 : X → β → Y2)
        [IsSmooth f] [∀ y1, IsSmooth (f y1)] [IsSmooth g1] [IsSmooth g2]
        : δ (λ (x : X) (b : β) => f (g1 x b) (g2 x b)) = λ x dx b =>  δ f (g1 x b) (δ g1 x dx b) (g2 x b) + δ (f (g1 x b)) (g2 x b) (δ g2 x dx b) := sorry 


-- variable (X Y : Type) [Vec X] [Vec Y]
-- set_option trace.Meta.Tactic.simp.discharge true in 
@[simp high]
theorem differential_of_fst
  : δ (Prod.fst : X×Y → X) = λ xy (dx,dy) => dx := sorry
@[simp high]
theorem differential_of_snd
  : δ (Prod.snd : X×Y → Y) = λ xy (dx,dy) => dy := sorry

-- @[reducible]
-- instance {X} [Hilbert X] : AtomicSmoothFun (λ x : X => ∥x∥²) where
--   is_smooth := by simp[SemiInner.normSqr] infer_instance done
--   df := λ x dx : X => 2*⟪x, dx⟫
--   is_df := by simp[SemiInner.normSqr, SemiHilbert.semi_inner_sym] done

instance {X} [Hilbert X] : IsSmooth (λ x : X => ∥x∥²) := 
by 
  simp[SemiInner.normSqr]; infer_instance done

@[simp] theorem differential_of_squared_norm {X} [Hilbert X] 
  : δ (λ x : X => ∥x∥²) = λ x dx : X => 2*⟪x, dx⟫ := 
by
  simp[SemiInner.normSqr, SemiHilbert.semi_inner_sym] done


instance : IsLin (λ (f : X ⟿ Y) => δ f.1) := sorry
instance (f : X → Y) [IsSmooth f] : IsSmooth (δ f) := sorry
instance (f : X → Y) [IsSmooth f] (x : X) : IsLin (δ f x) := sorry
-- instance {U V : Type} [SemiHilbert U] [SemiHilbert V] (f : U → V) (u : U) [IsSmooth f] : HasAdjoint (δ f u) := sorry

instance {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y → Z) (x dx : X) 
  [IsSmooth f] [h : ∀ x, IsSmooth (f x)] : IsSmooth (δ f x dx) := sorry

noncomputable
def diff := λ (f : X ⟿ Y) ⊸ (λ x ⟿ λ dx ⊸ δ f.1 x dx)

-- noncomputable
-- def derivative := λ (f : ℝ ⟿ Y) ⊸ (λ x ⟿ (δ f.1 x (1 : ℝ)))


@[simp] 
theorem differential_of_parm_morph {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y → Z) (x dx : X) [IsSmooth f] [h : ∀ x, IsSmooth (f x)] 
  : δ (λ x => (⟨f x, h x⟩ : Y ⟿ Z)) x dx = (⟨δ f x dx, by infer_instance⟩ : Y ⟿ Z) := sorry


-- instance : HasAdjoint (diff (X := ℝ) (Y := ℝ)).1  := sorry

-- @[simp]
-- theorem diff_adjoint : diff† = 

-- #check λ (f : X ⟿ Y) ⟿ (λ x dx ⟿ δ f.1 x dx)
#check λ (f : X ⟿ Y) ⊸ (λ x ⟿ λ dx ⊸ δ f.1 x dx)

#check Smooth.Hom.mk
-- instance : IsSmooth (λ (f : X ⟿ Y) => f.1) := by infer_instance
                   
-- section aa
-- variable {X Y Z : Type} [FinEnumVec X] [Hilbert Y] {S} [Vec S.R] [SemiHilbert' Z S]
-- example : SemiInner.Trait (ℝ ⊸ Y) := by infer_instance
-- example : Hilbert (ℝ ⊸ Y) := by infer_instance
-- example : SemiInner.Trait (ℝ ⟿ Y) := by infer_instance
-- example : SemiInner.Trait Y := by infer_instance
-- example : SemiInner.Trait.sig (ℝ ⟿ Y) = SemiInner.RealSig.addInterval := by rfl

-- -- set_option trace.Meta.synthInstance true in
-- -- example : SemiHilbert' (ℝ ⟿ Y) (SemiInner.Trait.sig (ℝ ⟿ Y)) := by infer_instance
-- -- example : SemiHilbert' (ℝ ⟿ Y) (SemiInner.RealSig.addInterval) := by infer_instance
-- -- example : SemiHilbert' (ℝ ⟿ Z) S.addInterval := by infer_instance
-- -- #check  ((λ (f : ℝ ⟿ Y) => λ x ⟿ λ dx ⊸ δ f.1 x dx))†
-- end aa
