import SciLean.Prelude
import SciLean.Categories
import SciLean.Operators.Inverse
import SciLean.Operators.Sum

import SciLean.Simp

-- import Init.Classical

namespace SciLean

prefix:max "𝓘" => SemiInner.Signature.Dom

open SemiInner in
class HasDual {X} [SemiHilbert X] (f : X → 𝓓 X → ℝ) : Prop where
  hasDual : ∃ (x : X), ∀ (y : X) (Ω : 𝓓 X), testFunction Ω y → f y Ω = ⟪x, y⟫[Ω]

open SemiInner in
noncomputable
def dual {X} [SemiHilbert X] (f : X → 𝓓 X → ℝ) : X
    :=
    match Classical.propDecidable (HasDual f) with
      | isTrue h => Classical.choose (HasDual.hasDual (self := h))
      | _ => (0 :X)

-- Probably well behaved only on HasAdjoint functions

open SemiInner in
instance {X} [SemiHilbert X] : LT (𝓓 X) := ⟨λ Ω Ω' => ∀ (x : X), testFunction Ω x → testFunction Ω' x⟩

open SemiInner in
class PreservesTestFunctions {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) : Prop where
  preservesTestFun : ∀ (Ω : 𝓓 X), ∃ (Ω' : 𝓓 Y), 
    (∀ (x : X), testFunction Ω x → testFunction Ω' (f x)) ∧                         -- preserves test functions
    (∀ (Ω'' : 𝓓 Y), (Ω'' < Ω') → ∃ x, testFunction Ω x → ¬testFunction Ω'' (f x))  -- can not be smaller

open SemiInner in
noncomputable
def domain_pushforward {X Y} [SemiHilbert X] [SemiHilbert Y]
    (f : X → Y) : 𝓓 X → 𝓓 Y
    :=
    λ Ω =>
    match Classical.propDecidable (PreservesTestFunctions f) with
      | isTrue  h => Classical.choose (PreservesTestFunctions.preservesTestFun (self := h) Ω)
      | _ => default

postfix:max "‡" => domain_pushforward


--- Notes on the definition:
---       1. Existence is postulated because we do not work with complete vector spaces
---       2. condition `testFunction D x` is there to prove uniquness of adjoint
---       3. condition `testFunction D y` is there to prove f†† = f
---       4. condition `preservesTestFun` is there to prove (f ∘ g)† = g† ∘ f†
open SemiInner in
class HasAdjoint {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) 
  extends PreservesTestFunctions f : Prop where
    has_dual : ∀ y, HasDual (λ x Ω => ⟪y, f x⟫[f‡ Ω])

instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) [HasAdjoint f] (y : Y)
  : HasDual (λ x Ω => ⟪y, f x⟫[f‡ Ω]) := sorry

open SemiInner in
noncomputable
def adjoint {X Y} [SemiHilbert X] [SemiHilbert Y] 
    (f : X → Y) : Y → X 
    :=
    λ y => dual (λ x Ω => ⟪y, f x⟫[f‡ Ω])

postfix:max "†" => adjoint

namespace Adjoint

  open SemiInner

  variable {α β γ : Type}
  variable {X Y Z: Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]

 
  @[simp]
  theorem semiinner_of_dual (f : X → 𝓓 X → ℝ) [HasDual f]
    (x : X) (Ω : 𝓓 X)
    : testFunction Ω x → 
      ⟪dual f, x⟫[Ω] = f x Ω
    := sorry

  instance (f : Y → Z) (g : X → Y)
    [PreservesTestFunctions f] [PreservesTestFunctions g]
    : PreservesTestFunctions (λ x => f (g x)) 
    := sorry

  @[simp]
  theorem domain_pushforward_of_comp (f : Y → Z) (g : X → Y)
    [PreservesTestFunctions f] [PreservesTestFunctions g] (Ω : 𝓓 X)
    : (λ x => f (g x))‡ Ω = f‡ (g‡ Ω)
    := sorry

  @[simp]
  theorem inner_adjoint_fst_right_test
    (f : X → Y) (x : X) (y : Y) (Ω : 𝓓 X) [HasAdjoint f] 
    : 
      testFunction Ω x →
      ⟪f† y, x⟫[Ω] = ⟪y, f x⟫[f‡ Ω]
    := 
  by
    intro h;
    simp[adjoint]
    rw[semiinner_of_dual]
    apply h
    done

  -- This is probably not true in general
  -- @[simp]
  -- theorem inner_adjoint_fst_left_test
  --   (f : X → Y) (x : X) (y : Y) (d : D) [HasAdjoint f] 
  --   : 
  --     (h : testFunction' d y) 
  --     → ⟪f† y, x⟫ = ⟪y, f x⟫ 
  --   := sorry

  @[simp]
  theorem inner_adjoint_snd_right_test 
    (f : X → Y) (x : X) (y : Y) (Ω : 𝓓 X) [HasAdjoint f] 
    : 
      testFunction Ω x →
      ⟪x, f† y⟫[Ω] = ⟪f x, y⟫[f‡ Ω]
    := sorry

  -- This is probably not true in general
  -- @[simp]
  -- theorem inner_adjoint_snd_left_test
  --   (f : X → Y) (x : X) (y : Y) (d : D) [HasAdjoint f] 
  --   : 
  --     (h : testFunction' d y) 
  --     → ⟪x, f† y⟫ = ⟪f x, y⟫
  --   := sorry

  theorem inner_ext {X} (x y : X) [SemiHilbert X] 
    : 
      (∀ (x' : X) (Ω : 𝓓 X), testFunction Ω x' → ⟪x, x'⟫[Ω] = ⟪y, x'⟫[Ω]) → (x = y)
    := sorry 

  -- syntax "inner_ext" (ident)? (ident)? (ident)? : tactic
  -- macro_rules
  --   | `(tactic| inner_ext ) => `(tactic| inner_ext ϕ D h)
  --   | `(tactic| inner_ext $x) => `(tactic| inner_ext $x D h)
  --   | `(tactic| inner_ext $x $D) => `(tactic| inner_ext $x $D h)
  --   | `(tactic| inner_ext $x $D $h) => `(tactic| apply inner_ext; intro $x $D $h)

  -- Having adjoint actually implies linearity. The converse is not true in our 
  -- scenario, Convenient Vector spaces, as we do not have Riesz representation theorem.
  -- instance (f : X → Y) [HasAdjoint f] : IsLin f := sorry
  -- instance (f : X → Y) [HasAdjoint f] : IsLin (f†) := sorry
  -- instance (f : X → Y) [HasAdjoint f] : HasAdjoint (f†) := sorry

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

    instance eval_has_adjoint {ι} (i : ι) [Enumtype ι]
      : HasAdjoint (λ (f : ι → X) => f i) := sorry

  end Core

  -- For this to be true we need `inner_adjoint_fst_left_test` 
  -- Is this theorem important?
  -- @[simp]
  -- theorem adjoint_of_adjoint (f : X → Y) [HasAdjoint f] : f†† = f := 
  -- by 
  --   funext x
  --   apply inner_ext
  --   intro ϕ Ω h
  --   simp (discharger := assumption)
  --   done

  @[simp] 
  theorem domain_pushforward_of_id (Ω : 𝓓 X)
    : (λ x : X => x)‡ Ω = Ω
    := sorry

  @[simp high] 
  theorem adjoint_of_id
    : adjoint (λ x : X => x) = id := 
  by 
    funext x; apply inner_ext; intro y Ω h; simp (discharger := assumption); done

  @[simp]
  theorem domain_pushforward_of_const 
    {ι} [Enumtype ι] (Ω : 𝓓 (ι → X))
    : (λ (x : X) (i : ι) => x)‡ Ω = Ω
    := sorry

  @[simp]
  theorem adjoint_of_const {ι} [Enumtype ι]
    : (λ (x : X) (i : ι) => x)† = sum := 
  by 
    funext x; apply inner_ext; intro y Ω h;
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    simp[semiInner]
    rw[!?((∑ i, ⟪x i, y⟫[Ω]) = ⟪∑ i, x i, y⟫[Ω])]
    done

  instance {ι} [Enumtype ι] : HasAdjoint (sum : (ι → X) → X) := sorry

  @[simp] theorem domain_pushforward_of_sum {ι} [Enumtype ι] (Ω)
    : (sum : (ι → X) → X)‡ Ω = Ω
    := sorry

  @[simp] theorem adjoint_of_sum {ι} [Enumtype ι]
    : (sum : (ι → X) → X)† = (λ (x : X) (i : ι) => x) :=
  by
    funext f; apply inner_ext; intro g Ω h;
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    simp[semiInner]
    rw [!?((∑ i, ⟪f, g i⟫[Ω]) = ⟪f, ∑ i, g i⟫[Ω])]
    done

  instance {ι} [Enumtype ι] 
    (f : X → ι → Y) (i : ι) [HasAdjoint f] 
    : HasAdjoint (λ x => f x i)
    := sorry

  @[simp]
  theorem domain_pushforward_of_parm {ι} [Enumtype ι] 
    (f : X → ι → Y) (i : ι) [PreservesTestFunctions f] (Ω )
    : (λ x => f x i)‡ Ω = f‡ Ω
    := sorry

  @[simp]
  theorem adjoint_of_parm {ι} [Enumtype ι] 
    (f : X → ι → Y) (i : ι) [HasAdjoint f] 
    : 
      (λ x => f x i)† = (λ y => f† (λ j => (kron i j)*y)) 
    :=
  by
    funext y; apply inner_ext; intro x Ω h;
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    simp[semiInner]
    rw[!?((∑ j, ⟪(kron i j) * y, (f x j)⟫[f‡ Ω]) = ⟪y, (f x i)⟫[f‡ Ω])]
    done

  instance {ι} [Enumtype ι]
      (f : ι → X → Y)
      [∀ i, HasAdjoint (f i)]
      :
        HasAdjoint (λ x i => f i x)   
      := sorry

  -- Is this realy true??
  -- theorem domain_pushforward_of_swap  {ι} [Enumtype ι]
  --     (f : ι → X → Y)
  --     [∀ i, HasAdjoint (f i)] (Ω j)
  --     : (f j)‡ Ω < (f (fun x i => f i x)‡ Ω
  --     := sorry

  -- @[simp]
  -- theorem adjoint_of_swap {ι} [Enumtype ι]
  --     (f : ι → X → Y)
  --     [∀ i, HasAdjoint (f i)]
  --     :
  --       (λ x i => f i x)† = (λ (y : ι → Y) => ∑ i, (f i)† (y i))
  --     := 
  -- by
  --   funext y; apply inner_ext; intro x Ω h;
  --   rw[inner_adjoint_fst_right_test]
  --   . simp[semiInner]

  --     -- This is a form of more general statement:
  --     --   testFunction Ω x → Ω < Ω' → 
  --     --   ⟪y, x⟫[Ω'] = ⟪y, x⟫[Ω] 
  --     conv =>
  --       lhs; enter [1,i]
  --       rw[!?(⟪y i, f i x⟫[(fun x j => f j x)‡ Ω] = ⟪y i, f i x⟫[(f i)‡ Ω])]

  --     -- simple linearity
  --     rw[!?(⟪∑ i, (f i)† (y i), x⟫[Ω] = ∑ i, ⟪(f i)† (y i), x⟫[Ω])]
  --     conv =>
  --       rhs; enter [1,i]
  --       rw[inner_adjoint_fst_right_test _ _ _ _ h]
  --     done
  --   . apply h
  --   done

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
    := by infer_instance

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

  variable {Y1 Y2} {ι : Type} [SemiHilbert Y1] [SemiHilbert Y2] [Enumtype ι]

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

  instance has_adjoint_of_diag_arg
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

  instance has_adjoint_of_swap_pullback {ι κ} [Enumtype ι] [Enumtype κ]
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
