import SciLean.Prelude
import SciLean.Categories
-- import SciLean.Operators.Inverse
import SciLean.Operators.Sum
import SciLean.Simp

namespace SciLean

open SemiInner in
class HasDual {X} [SemiHilbert X] (f : X → 𝓓 X → ℝ) : Prop where
  hasDual : ∃ (f' : X), ∀ (x : X) (Ω : 𝓓 X), testFunction Ω x → ⟪f', x⟫[Ω] = f x Ω

open SemiInner in
noncomputable
def dual {X} [SemiHilbert X] (f : X → 𝓓 X → ℝ) : X
    :=
    match Classical.propDecidable (HasDual f) with
      | isTrue h => Classical.choose (HasDual.hasDual (self := h))
      | _ => (0 :X)

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

open SemiInner in
class HasAdjoint {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) 
  extends PreservesTestFunctions f, IsLin f : Prop where
    has_dual : ∀ y, HasDual (λ x Ω => ⟪y, f x⟫[f‡ Ω])

-- attribute [instance low] HasAdjoint.toIsLin

instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) [HasAdjoint f] (y : Y)
  : HasDual (λ x Ω => ⟪y, f x⟫[f‡ Ω]) := sorry

open SemiInner in
noncomputable
def adjoint {X Y} [SemiHilbert X] [SemiHilbert Y] 
    (f : X → Y) : Y → X 
    :=
    λ y => dual (λ x Ω => ⟪y, f x⟫[f‡ Ω])

postfix:max "†" => adjoint

  open SemiInner

  variable {α β γ : Type}
  variable {X Y Z: Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
  variable {ι κ} [Enumtype ι] [Enumtype κ]
 
  @[simp]
  theorem semiinner_of_dual 
    (f : X → 𝓓 X → ℝ) [hf : HasDual f]
    (x : X) (Ω : 𝓓 X)
    : testFunction Ω x → 
      ⟪dual f, x⟫[Ω] = f x Ω
  := by
    intro hx
    have hc : (Classical.propDecidable (HasDual f)) = isTrue hf := sorry
    simp only [hc,dual]
    apply (Classical.choose_spec (HasDual.hasDual (f := f)))
    apply hx
    done

  theorem test_function_of_pushforward 
    (f : X → Y) (x : X) (Ω : 𝓓 X) (h : testFunction Ω x) [PreservesTestFunctions f]
    : testFunction (f‡ Ω) (f x) := sorry

  instance preserves_test_functions_id
    : PreservesTestFunctions (λ x : X => x) := sorry

  @[simp]
  theorem hilbert_domain {X} [Hilbert X] (Ω : 𝓓 X)
    : Ω = uniqueDomain := sorry

  @[simp]
  theorem domain_pushforward_of_hilbert {Y} [Hilbert Y] (Ω : 𝓓 X)
    (f : X → Y) [PreservesTestFunctions f]
    : f‡ Ω = uniqueDomain
  := sorry


  @[simp]
  theorem domain_pushforward_of_id (Ω : 𝓓 X)
    : (λ x : X => x)‡ Ω = Ω
    := sorry

  instance preserves_test_functions_parm
    (f : X → ι → Z) [PreservesTestFunctions f]
    (i : ι)
    : PreservesTestFunctions (λ x => f x i) := sorry

  @[simp]
  theorem domain_pushforward_of_parm 
    (f : X → ι → Z) [PreservesTestFunctions f]
    : (λ x => f x i)‡ Ω = f‡ Ω i
    := sorry

  @[simp]
  theorem domain_pushforward_of_swap (Ω : 𝓓 X)
    (f : ι → X → Y) (i : ι) [∀ i, PreservesTestFunctions (f i)]
    : (λ x j => f j x)‡ Ω i = (f i)‡ Ω
  := sorry

  instance (f : Y → Z) (g : X → Y)
    [PreservesTestFunctions f] [PreservesTestFunctions g]
    : PreservesTestFunctions (λ x => f (g x)) 
    := sorry

  -- Not sure about this 
  -- there might be just inequality
  -- (f ∘ g))‡ Ω < f‡ (g‡ Ω)
  @[simp]
  theorem domain_pushforward_of_comp (f : Y → Z) (g : X → Y)
    [PreservesTestFunctions f] [PreservesTestFunctions g] (Ω : 𝓓 X)
    : (λ x => f (g x))‡ Ω = f‡ (g‡ Ω)
    := sorry

  @[simp]
  theorem domain_pushforward_of_fst (Ω : 𝓓 (X×Y))
    : Prod.fst‡ Ω = Ω.1 := sorry

  @[simp]
  theorem domain_pushforward_of_snd (Ω : 𝓓 (X×Y))
    : Prod.snd‡ Ω = Ω.2 := sorry

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

  instance (f : X → Y) [HasAdjoint f] : IsLin (f†) := sorry
