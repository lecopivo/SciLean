import SciLean.Prelude
import SciLean.Categories
import SciLean.Operators.Inverse
import SciLean.Operators.Sum
import SciLean.Simp

import Init.Classical

namespace SciLean

variable {α β γ : Type}
variable {X Y Z Dom : Type} [SemiHilbert X Dom] [SemiHilbert Y Dom] [SemiHilbert Z Dom]

prefix:max "𝓘" => SemiInnerTrait.domOf 

--- Notes on the definition:
---       1. Existence is postulated because we do not work with complete vector spaces
---       2. condition `testFunction D x` is there to prove uniquness of adjoint
---       3. condition `testFunction D y` is there to prove f†† = f
---       4. condition `preservesTestFun` is there to prove (f ∘ g)† = g† ∘ f†
class HasAdjoint {X Y} [SemiInnerTrait X] [SemiHilbert X (𝓘 X)] [sy : SemiHilbert Y (𝓘 X)] (f : X → Y) : Prop  where
  hasAdjoint : ∃ (f' : Y → X), ∀ (x : X) (y : Y) (D : 𝓘 X), 
                 (testFunction D x ∨ testFunction D y → ⟪f' y, x⟫ = ⟪y, f x⟫)
  preservesTestFun : ∀ (x : X) (D : 𝓘 X), testFunction D x → testFunction D (f x)

noncomputable
def adjoint {X Y} [SemiInnerTrait X] [SemiHilbert X (𝓘 X) ] [SemiHilbert Y (𝓘 X)] (f : X → Y) : Y → X :=
    match Classical.propDecidable (HasAdjoint f) with
      | isTrue  h => Classical.choose (HasAdjoint.hasAdjoint (self := h))
      | _ => (0 : Y → X)

postfix:max "†" => adjoint

namespace Adjoint

  @[simp]
  theorem inner_adjoint_fst_right_test
          (f : X → Y) (x : X) (y : Y) (D : Dom) [HasAdjoint f] : (h : testFunction D x) → ⟪f† y, x⟫ D = ⟪y, f x⟫ D := sorry
  @[simp]
  theorem inner_adjoint_fst_left_test
          (f : X → Y) (x : X) (y : Y) (D : Dom) [HasAdjoint f] : (h : testFunction D y) → ⟪f† y, x⟫ D = ⟪y, f x⟫ D := sorry
  @[simp]
  theorem inner_adjoint_snd_right_test 
          (f : X → Y) (x : X) (y : Y) (D : Dom) [HasAdjoint f] : (h : testFunction D x) → ⟪x, f† y⟫ D = ⟪f x, y⟫ D := sorry
  @[simp]
  theorem inner_adjoint_snd_left_test
          (f : X → Y) (x : X) (y : Y) (D : Dom) [HasAdjoint f] : (h : testFunction D y) → ⟪x, f† y⟫ D = ⟪f x, y⟫ D := sorry

  theorem inner_ext {X} [SemiInnerTrait X] [SemiHilbert X (𝓘 X)] (x y : X) 
    : (∀ (x' : X) (D : 𝓘 X), testFunction D x' → (⟪x, x'⟫ D) = (⟪y, x'⟫ D)) → (x = y) := sorry 

  -- TODO: This needs some refinement as currnetly you need to write a semicolon after `inner_ext` if you do not want to specify all arguments
  syntax "inner_ext" (ident)? (ident)? (ident)? : tactic
  macro_rules
    | `(tactic| inner_ext ) => `(tactic| inner_ext ϕ D h)
    | `(tactic| inner_ext $x) => `(tactic| inner_ext $x D h)
    | `(tactic| inner_ext $x $D) => `(tactic| inner_ext $x $D h)
    | `(tactic| inner_ext $x $D $h) => `(tactic| apply inner_ext; intro $x $D $h)

  -- Having adjoint actually implies linearity. The converse is not true in our scenario, Convenient Vector spaces, as we do not have Riesz representation theorem.
  instance (f : X → Y) [HasAdjoint f] : IsLin f := sorry
  instance (f : X → Y) [HasAdjoint f] : IsLin f† := sorry
  instance (f : X → Y) [HasAdjoint f] : HasAdjoint f† := sorry

  section Core

    instance id_has_adjoint : HasAdjoint λ x : X => x := sorry
    instance const_zero_has_adjoint : HasAdjoint (λ x : X => (0 : Y)) := sorry

    instance comp_has_adjoint (f : Y → Z) (g : X → Y) [HasAdjoint f] [HasAdjoint g] : HasAdjoint (λ x => f (g x)) := sorry

    -- instance diag_has_adjoint (f : Y1 → Y2 → Z) (g1 : X → Y1) (g2 : X → Y2) [HasAdjoint (λ yy : Y1 × Y2 => f yy.1 yy.2)] [HasAdjoint g1] [HasAdjoint g2] : HasAdjoint (λ x => f (g1 x) (g2 x)) := sorry
    -- instance diag_parm_has_adjoint (f : Y1 → Y2 → Z) (g1 : X → α → Y1) (g2 : X → α → Y2) [HasAdjoint (λ yy : Y1 × Y2 => f yy.1 yy.2)] [HasAdjoint g1] [HasAdjoint g2] : HasAdjoint (λ x a => f (g1 x a) (g2 x a)) := sorry

  end Core

  @[simp]
  theorem adjoint_of_adjoint (f : X → Y) [HasAdjoint f] : f†† = f := 
  by
    funext x
    inner_ext;
    simp (discharger := assumption)
    done

  @[simp] 
  theorem adjoint_of_id
      : (λ x : X => x)† = id := sorry

  @[simp]
  theorem adjoint_of_const {ι} [Enumtype ι]
      : (λ (x : X) (i : ι) => x)† = sum := sorry

  -- This is unfortunatelly not true with current definition of adjoint
  -- @[simp]
  -- theorem adjoint_of_const_on_real [SemiInnerTrait X] [SemiHilbert X (𝓘 X)]
  --     : (λ (x : X) => (λ (t : ℝ) ⟿ x))† = integral := sorry

  @[simp]
  theorem adjoint_of_sum {ι} [Enumtype ι]
      : (sum)† = (λ (x : X) (i : ι) => x) := sorry

  @[simp]
  theorem adjoint_of_swap {ι κ} [Enumtype ι] [Enumtype κ]
      : (λ (f : ι → κ → Y) => (λ j i => f i j))† = λ f i j => f j i := sorry

  @[simp]
  theorem adjoint_of_parm {ι : Type} (f : X → ι → Y) (i : ι) [Enumtype ι] [HasAdjoint f] 
      : (λ x => f x i)† = (λ y => f† (λ j => (kron i j)*y)) := sorry

  @[simp]
  theorem adjoint_of_arg {n} [NonZero n] 
      (f : Y → Fin n → Z) [HasAdjoint f]
      (g1 : X → Y) [HasAdjoint g1]
      (g2 : Fin n → Fin n) [IsInv g2]
      : (λ x i => f (g1 x) (g2 i))† = g1† ∘ f† ∘ (λ h => h ∘ g2⁻¹) := sorry

  @[simp] 
  theorem adjoint_of_comp (f : Y → Z) [HasAdjoint f] (g : X → Y) [HasAdjoint g] 
      : (λ x => f (g x))† = g† ∘ f† := sorry

  @[simp] 
  theorem adjoint_of_comp_arg {n} (f : β → Y → Z) [∀ b, HasAdjoint (f b)] (g1 : Fin n → β) (g2 : X → Fin n → Y) [HasAdjoint g2] 
      : (λ x i => (f (g1 i) (g2 x i)))† = g2† ∘ (λ z i => (f (g1 i))† (z i)) := sorry

  @[simp]
  theorem adjoint_of_pullback {ι κ} [Enumtype ι] [Enumtype κ] [Inhabited ι] (g : ι → κ) [IsInv g]
      : (λ (f : κ → X) i => f (g i))† = (λ f => f ∘ g⁻¹) := sorry

  -- Unfortunatelly this theorem is dangerous and causes simp to loop indefinitely if used in simp
  theorem adjoint_of_comp_parm (f : Y → β → Z) (b : β) [HasAdjoint (λ y => f y b)] (g : X → Y) [HasAdjoint g] 
      : (λ x => f (g x) b)† = g† ∘ (λ y => f y b)† := sorry

  open Function

  variable {Y1 Y2 : Type} [SemiHilbert Y1 Dom] [SemiHilbert Y2 Dom]

  @[simp]
  theorem adjoint_of_diag 
      (f : Y1 → Y2 → Z) (g1 : X → Y1) (g2 : X → Y2) 
      [HasAdjoint (λ yy : Y1 × Y2 => f yy.1 yy.2)] [HasAdjoint g1] [HasAdjoint g2]
      : (λ x => f (g1 x) (g2 x))† = (uncurry HAdd.hAdd) ∘ (Prod.map g1† g2†) ∘ (uncurry f)† := sorry

  @[simp]
  theorem adjoint_of_diag_arg
      (f : Y1 → Y2 → Z) (g1 : X → Fin n → Y1) (g2 : X → Fin n → Y2)
      [HasAdjoint (λ yy : Y1 × Y2 => f yy.1 yy.2)] [HasAdjoint g1] [HasAdjoint g2]
      : (λ x i => f (g1 x i) (g2 x i))† = (uncurry HAdd.hAdd) ∘ (pmap g1† g2†) ∘ (λ f => (λ i => (f i).1, λ i => (f i).2)) ∘ (comp (uncurry f)†) := sorry


  --------------------------------------------------------------------------------------------

  macro "autoadjoint" : conv => `(repeat' (conv => pattern (inverse _); simp; rw[adjoint_of_comp_parm]; simp))
  macro "autoadjoint" : tactic => `(conv => autoadjoint)

  --------------------------------------------------------------------------------------------

end Adjoint
