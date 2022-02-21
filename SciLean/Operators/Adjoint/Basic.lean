import SciLean.Prelude
import SciLean.Categories
import SciLean.Operators.Inverse
import SciLean.Operators.Sum

import SciLean.Simp

-- import Init.Classical

namespace SciLean

prefix:max "𝓘" => SemiInner.Signature.Dom

--- Notes on the definition:
---       1. Existence is postulated because we do not work with complete vector spaces
---       2. condition `testFunction D x` is there to prove uniquness of adjoint
---       3. condition `testFunction D y` is there to prove f†† = f
---       4. condition `preservesTestFun` is there to prove (f ∘ g)† = g† ∘ f†
open SemiInner in
class HasAdjoint' {X Y}
  {R D e} [outParam $ Vec R] [outParam $ SemiHilbert X R D e] [outParam $ SemiHilbert Y R D e] (f : X → Y) : Prop  
  where
    hasAdjoint : ∃ (f' : Y → X), ∀ (x : X) (y : Y) (d : (Trait₂.D X Y)), 
                   (testFunction' d x ∨ testFunction' d y) → ⟪f' y, x⟫ = ⟪y, f x⟫
    preservesTestFun : ∀ (x : X) (d : (Trait₂.D X Y)), testFunction' d x → testFunction' d (f x)

-- TODO: Understand why the argument (f : X → Y) has to be at the last position
-- otherwise I'm getting some odd errors when working with reals
open SemiInner in
@[reducible] abbrev HasAdjoint {X Y} 
  [Trait₂ X Y] 
  [Vec (Trait₂.R X Y)] 
  [SemiHilbert X (Trait₂.R X Y) (Trait₂.D X Y) Trait₂.eval]
  [SemiHilbert Y (Trait₂.R X Y) (Trait₂.D X Y) Trait₂.eval]
  (f : X → Y) 
  : Prop 
  := HasAdjoint' (R := (Trait₂.R X Y)) (D := (Trait₂.D X Y)) (e := (Trait₂.eval)) f

open SemiInner in
noncomputable
def adjoint {X Y} 
    [Trait₂ X Y] [Vec (Trait₂.R X Y)] 
    [SemiHilbert X (Trait₂.R X Y) (Trait₂.D X Y) Trait₂.eval] 
    [SemiHilbert Y (Trait₂.R X Y) (Trait₂.D X Y) Trait₂.eval]
    (f : X → Y) 
    : 
      Y → X 
    :=
    match Classical.propDecidable (HasAdjoint f) with
      | isTrue  h => Classical.choose (HasAdjoint'.hasAdjoint (self := h))
      | _ => (0 : Y → X)

-- section AutoCompleteS

--   open SemiInner

--   class PairTrait (X Y : Type) where
--     sig : Signature

--   export PairTrait (sig)
--   attribute [reducible] PairTrait.sig

--   @[reducible] instance {X Y} [Trait X] : PairTrait X Y := ⟨Trait.sig X⟩
--   @[reducible] instance {X Y} [Trait Y] : PairTrait X Y := ⟨Trait.sig Y⟩

--   variable {X Y} [PairTrait X Y] [Vec (sig X Y).R] [SemiHilbert' X (sig X Y)] [SemiHilbert' Y (sig X Y)] 
--   noncomputable
--   abbrev adjoint (f : X → Y) := adjoint' (sig X Y) f

--   abbrev HasAdjoint (f : X → Y) := HasAdjoint' (sig X Y) f

--   -- these might be dangerouds
--   -- @[reducible] instance {X} [Trait X] [Vec (Trait.sig X).R] [SemiHilbert' X (Trait.sig X)] : SemiHilbert X := SemiHilbert.mk (X := X)
--   @[reducible] instance {X S} [SemiInner' X S] : Trait X := ⟨S⟩
--   -- @[reducible] instance {X} [Trait X] [SemiInner' X (Trait.sig X)] : SemiInner X := SemiInner.mk

-- end AutoCompleteS

postfix:max "†" => adjoint

namespace Adjoint

  open SemiInner

  variable {α β γ : Type}
  variable {X Y Z: Type} {R D e} [Vec R] [SemiHilbert X R D e] [SemiHilbert Y R D e] [SemiHilbert Z R D e]

  variable (f : X → Y) (x : X) (y : Y) [HasAdjoint f]

  #check ⟪f† y, x⟫ = ⟪y, f x⟫


  -- open SemiInner in
  -- instance {X S} [SemiHilbert' X (Trait.sig X)] : Vec (Trait.sig X).R := ⟨S⟩
  
  -- set_option synthInstance.maxHeartbeats 5000
                
  -- example : SemiHilbert' X (Trait.sig X) := by infer_instance
  -- example : SemiHilbert X := by infer_instance
  -- example : SemiHilbert Y := by infer_instance
  -- example : SemiHilbert Z := by infer_instance


  @[simp]
  theorem inner_adjoint_fst_right_test
    (f : X → Y) (x : X) (y : Y) (d : D) [HasAdjoint f] 
    : 
      (h : testFunction' d x) 
      → ⟪f† y, x⟫ = ⟪y, f x⟫
    := sorry

  @[simp]
  theorem inner_adjoint_fst_left_test
    (f : X → Y) (x : X) (y : Y) (d : D) [HasAdjoint f] 
    : 
      (h : testFunction' d y) 
      → ⟪f† y, x⟫ = ⟪y, f x⟫ 
    := sorry

  @[simp]
  theorem inner_adjoint_snd_right_test 
    (f : X → Y) (x : X) (y : Y) (d : D) [HasAdjoint f] 
    : 
      (h : testFunction' d x) 
      → ⟪x, f† y⟫ = ⟪f x, y⟫ 
    := sorry

  @[simp]
  theorem inner_adjoint_snd_left_test
    (f : X → Y) (x : X) (y : Y) (d : D) [HasAdjoint f] 
    : 
      (h : testFunction' d y) 
      → ⟪x, f† y⟫ = ⟪f x, y⟫
    := sorry

  theorem inner_ext {X} (x y : X) [Trait X] [Vec (Trait.R X)] [SemiHilbert X (Trait.R X) (Trait.D X) Trait.eval] 
    : 
      (∀ (x' : X) (d : (Trait.D X)), testFunction' d x' → ⟪x, x'⟫ = ⟪y, x'⟫)
       → (x = y)
    := sorry 

  -- TODO: This needs some refinement as currnetly you need to write a semicolon
  --       after `inner_ext` if you do not want to specify all arguments
  syntax "inner_ext" (ident)? (ident)? (ident)? : tactic
  macro_rules
    | `(tactic| inner_ext ) => `(tactic| inner_ext ϕ D h)
    | `(tactic| inner_ext $x) => `(tactic| inner_ext $x D h)
    | `(tactic| inner_ext $x $D) => `(tactic| inner_ext $x $D h)
    | `(tactic| inner_ext $x $D $h) => `(tactic| apply inner_ext; intro $x $D $h)

  -- Having adjoint actually implies linearity. The converse is not true in our 
  -- scenario, Convenient Vector spaces, as we do not have Riesz representation theorem.
  instance (f : X → Y) [HasAdjoint f] : IsLin f := sorry
  instance (f : X → Y) [HasAdjoint f] : IsLin (f†) := sorry
  instance (f : X → Y) [HasAdjoint f] : HasAdjoint (f†) := sorry

  section Core

    instance id_has_adjoint 
      : HasAdjoint λ x : X => x := sorry

    instance const_zero_has_adjoint 
      : HasAdjoint (λ x : X => (0 : Y)) := sorry

    instance parm_has_adjoint {ι} [Enumtype ι] 
      : HasAdjoint (λ (x : X) (i : ι) => x) := sorry

    instance comp_has_adjoint 
      (f : Y → Z) (g : X → Y) 
      [HasAdjoint f] [HasAdjoint g] 
      : 
        HasAdjoint (λ x => f (g x)) := sorry

    -- instance diag_has_adjoint (f : Y1 → Y2 → Z) (g1 : X → Y1) (g2 : X → Y2) [HasAdjoint (λ yy : Y1 × Y2 => f yy.1 yy.2)] [HasAdjoint g1] [HasAdjoint g2] : HasAdjoint (λ x => f (g1 x) (g2 x)) := sorry
    -- instance diag_parm_has_adjoint (f : Y1 → Y2 → Z) (g1 : X → α → Y1) (g2 : X → α → Y2) [HasAdjoint (λ yy : Y1 × Y2 => f yy.1 yy.2)] [HasAdjoint g1] [HasAdjoint g2] : HasAdjoint (λ x a => f (g1 x a) (g2 x a)) := sorry

  end Core

  set_option trace.Meta.Tactic.simp true in
  @[simp]
  theorem adjoint_of_adjoint (f : X → Y) [HasAdjoint f] : f†† = f := 
  by 
    funext x 
    inner_ext;
    simp (discharger := assumption)
    admit

  @[simp high] 
  theorem adjoint_of_id
    : adjoint (λ x : X => x) = id := 
  by 
    funext x; inner_ext; simp (discharger := assumption); admit


  @[simp]
  theorem adjoint_of_const {ι} [Enumtype ι]
    : (λ (x : X) (i : ι) => x)† = sum := 
  by 
    funext x; inner_ext;
    simp (discharger := assumption);
    simp[semiInner, semiInner]
    -- now just propagete sum inside and we are done
    admit

  -- This is unfortunatelly not true with current definition of adjoint
  -- @[simp]
  -- theorem adjoint_of_const_on_real [SemiInnerTrait X] [SemiHilbert X (𝓘 X)]
  --     : (λ (x : X) => (λ (t : ℝ) ⟿ x))† = integral := sorry

  instance {ι} [Enumtype ι] : HasAdjoint (sum : (ι → X) → X) := sorry

  @[simp] theorem adjoint_of_sum {ι} [Enumtype ι]
    : (sum : (ι → X) → X)† = (λ (x : X) (i : ι) => x) := sorry

  @[simp]
  theorem adjoint_of_parm {ι} [Enumtype ι] 
    (f : X → ι → Y) (i : ι) [HasAdjoint f] 
    : 
      (λ x => f x i)† = (λ y => f† (λ j => (kron i j)*y)) 
    := sorry

  instance {ι} [Enumtype ι]
      (f : ι → X → Y)
      [∀ i, HasAdjoint (f i)]
      :
        HasAdjoint (λ x i => f i x)   
      := sorry

  @[simp]
  theorem adjoint_of_swap {ι} [Enumtype ι]
      (f : ι → X → Y)
      [∀ i, HasAdjoint (f i)]
      :
        (λ x i => f i x)† = (λ (y : ι → Y) => ∑ i, (f i)† (y i))
      := 
  by
    funext x
    inner_ext;
    simp (discharger := assumption);
    -- propagate sum outside of ⟪·,·⟫, move (f i)† on ϕ
    -- expand defitions of ⟪·,·⟫ and it should be done
    admit

  @[simp]
  theorem adjoint_of_swap' {ι κ} [Enumtype ι] [Enumtype κ]
    : (λ (f : ι → κ → Y) => (λ j i => f i j))† = λ f i j => f j i := sorry

  instance {ι κ} [Enumtype ι] [Enumtype κ] [Nonempty ι]
    (f : Y → κ → Z) [HasAdjoint f]
    (g1 : X → Y) [HasAdjoint g1]
    (g2 : ι → κ) [IsInv g2]
    :
      HasAdjoint (λ x i => f (g1 x) (g2 i))
    := sorry

  @[simp]
  theorem adjoint_of_arg {ι κ} [Enumtype ι] [Enumtype κ] [Nonempty ι]
    (f : Y → κ → Z) [HasAdjoint f]
    (g1 : X → Y) [HasAdjoint g1]
    (g2 : ι → κ) [IsInv g2]
    : 
      adjoint (λ x i => f (g1 x) (g2 i)) = (adjoint g1) ∘ (adjoint f) ∘ (λ h => h ∘ g2⁻¹) 
    := sorry

  @[simp] 
  theorem adjoint_of_comp 
    (f : Y → Z) (g : X → Y) [HasAdjoint f] [HasAdjoint g] 
    : 
      (adjoint (λ x => f (g x))) = (adjoint g) ∘ (adjoint f)
    := sorry


  instance {ι κ} [Enumtype ι] [Enumtype κ] [Nonempty ι] 
    (g : ι → κ) [IsInv g]
    : 
      HasAdjoint (λ (f : κ → X) i => f (g i))
    := sorry

  @[simp]
  theorem adjoint_of_pullback {ι κ} [Enumtype ι] [Enumtype κ] [Nonempty ι] 
    (g : ι → κ) [IsInv g]
    : 
      adjoint (λ (f : κ → X) i => f (g i)) = (λ f => f ∘ g⁻¹) 
    := 
  by 
    admit

  instance 
    (f : Y → β → Z) (g : X → Y) (b : β) 
    [HasAdjoint (λ y => f y b)] [HasAdjoint g] 
    : 
      HasAdjoint (λ x => f (g x) b) 
    := sorry

  -- Unfortunatelly this theorem is dangerous and causes simp to loop 
  -- indefinitely if used in simp
  theorem adjoint_of_comp_parm 
    (f : Y → β → Z) (g : X → Y) (b : β) 
    [HasAdjoint (λ y => f y b)] [HasAdjoint g] 
    : 
      adjoint (λ x => f (g x) b) = adjoint g ∘ adjoint (λ y => f y b)
    := 
  by 
    admit

  instance (f : Y → β → γ → Z) (g : X → Y) (b c) 
    [HasAdjoint (λ y => f y b c)] [HasAdjoint g] 
    : 
      HasAdjoint (λ x => f (g x) b c)
    := sorry

  -- @[simp]
  theorem adjoint_of_comp_parm' 
    (f : Y → β → γ → Z) (g : X → Y) (b c) 
    [HasAdjoint (λ y => f y b c)] [HasAdjoint g] 
    : 
      adjoint (λ x => f (g x) b c) = adjoint g ∘ adjoint (λ y => f y b c)
    := 
  by
    admit

  instance {ι} [Enumtype ι]
    (f : Y → β → Z) (g1 : X → ι → Y) (g2 : ι → β)
    [∀ b, HasAdjoint (λ y : Y => f y b)] [HasAdjoint g1] 
    :
      HasAdjoint (λ x i => f (g1 x i) (g2 i)) 
    := sorry

  -- This one is dangerous too
  @[simp]
  theorem adjoint_of_comp_arg_1 {ι} [Enumtype ι]
    (f : Y → β → Z) (g1 : X → ι → Y) (g2 : ι → β)
    [∀ b, HasAdjoint (λ y : Y => f y b)] [HasAdjoint g1] 
    : 
      (λ x i => f (g1 x i) (g2 i))†
      = 
      g1† ∘ (λ h i => (λ y => f y (g2 i))† (h i)) 
    := sorry


  instance {ι} [Enumtype ι]
    (f : β → Y → Z) (g1 : ι → β) (g2 : X → ι → Y)
    [∀ b, HasAdjoint (f b)] [HasAdjoint g2] 
    :
      HasAdjoint (λ x i => f (g1 i) (g2 x i)) 
    := sorry

  -- This one is dangerous too
  @[simp]
  theorem adjoint_of_comp_arg_2 {ι} [Enumtype ι]
    (f : β → Y → Z) (g1 : ι → β) (g2 : X → ι → Y)
    [∀ b, HasAdjoint (f b)] [HasAdjoint g2] 
    : 
      (λ x i => f (g1 i) (g2 x i))†
      = 
      g2† ∘ (λ h i => (f (g1 i))† (h i)) 
    := sorry


  open Function

  variable {Y1 Y2} {ι : Type} [SemiHilbert Y1 R D e] [SemiHilbert Y2 R D e] [Enumtype ι]

  instance (f : Y1 → Y2 → Z) (g1 : X → Y1) (g2 : X → Y2) 
    [HasAdjoint g1] [HasAdjoint g2]
    [HasAdjoint (λ yy : Y1 × Y2 => f yy.1 yy.2)] 
    : 
      HasAdjoint (λ x => f (g1 x) (g2 x))
    := sorry


  @[simp]
  theorem adjoint_of_diag 
    (f : Y1 → Y2 → Z) (g1 : X → Y1) (g2 : X → Y2) 
    [HasAdjoint g1] [HasAdjoint g2]
    [HasAdjoint (λ yy : Y1 × Y2 => f yy.1 yy.2)] 
    : 
      (λ x => f (g1 x) (g2 x))†
      = 
      (uncurry HAdd.hAdd) 
      ∘ (Prod.map g1† g2†) 
      ∘ (uncurry f)†
    := 
  by 
    admit

  instance
    (f : Y1 → Y2 → Z) (g1 : X → ι → Y1) (g2 : X → ι → Y2)
    [HasAdjoint g1] [HasAdjoint g2]
    [HasAdjoint (λ yy : Y1 × Y2 => f yy.1 yy.2)] 
    : 
      HasAdjoint (λ x i => f (g1 x i) (g2 x i))
    := sorry

  @[simp]
  theorem adjoint_of_diag_arg
    (f : Y1 → Y2 → Z) (g1 : X → ι → Y1) (g2 : X → ι → Y2)
    [HasAdjoint g1] [HasAdjoint g2]
    [HasAdjoint (λ yy : Y1 × Y2 => f yy.1 yy.2)] 
    : 
      (λ x i => f (g1 x i) (g2 x i))†
      = 
      (uncurry HAdd.hAdd) 
      ∘ (Prod.map g1† g2†) 
      ∘ (λ f => (λ i => (f i).1, λ i => (f i).2)) 
      ∘ (comp (uncurry f)†) 
    := sorry

  instance {ι κ} [Enumtype ι] [Enumtype κ]
      (f : ι → X → Y) (h : ι → κ)
      [∀ i, HasAdjoint (f i)] [IsInv h]
      :
        HasAdjoint (λ (x : κ → X) i => f i (x (h i)))
      := sorry

  @[simp]
  theorem adjoint_of_swap_pullback {ι κ} [Enumtype ι] [Enumtype κ] [Nonempty ι]
      (f : ι → X → Y) (h : ι → κ)
      [∀ i, HasAdjoint (f i)] [IsInv h]
      :
        (λ (x : κ → X) i => f i (x (h i)))† 
        = 
        (λ y j => (f (h⁻¹ j))† (y (h⁻¹ j)))
      := sorry

  --------------------------------------------------------------------------------------------

  macro "autoadjoint" : conv => `(repeat' (conv => 
                                            pattern (adjoint _)
                                            simp
                                            rw[adjoint_of_comp_parm]
                                            simp))
  macro "autoadjoint" : tactic => `(conv => autoadjoint)

  --------------------------------------------------------------------------------------------

end Adjoint
