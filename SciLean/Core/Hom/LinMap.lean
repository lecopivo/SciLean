import SciLean.Core.Mor
import SciLean.Core.Fun
import SciLean.Core.Functions
import SciLean.Core.Obj.FinVec

namespace SciLean

  abbrev LinMap (X Y : Type) [Vec X] [Vec Y] := (f : X → Y) ×' (IsLin f)

  infixr:25 " ⊸ " => LinMap

  variable {X Y} [Vec X] [Vec Y]

  variable (f : X → Y) [IsLin f]
  variable (g : X → Y) [IsLin g]
  variable (r : ℝ)

  instance : IsLin (-f)    := by (conv => enter [1,x]); simp; infer_instance done
  instance : IsLin (f + g) := by (conv => enter [1,x]); simp; infer_instance done
  instance : IsLin (f - g) := by (conv => enter [1,x]); simp; infer_instance done
  instance : IsLin (r * f) := by (conv => enter [1,x]); simp; infer_instance done
  instance : IsLin (0 : X → Y) :=  by (conv => enter [1,x]); simp; infer_instance done

  instance : Neg (X⊸Y) := ⟨λ f   => ⟨-f.1, by have hf := f.2; infer_instance⟩⟩
  instance : Add (X⊸Y) := ⟨λ f g => ⟨f.1 + g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
  instance : Sub (X⊸Y) := ⟨λ f g => ⟨f.1 + g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
  instance : Mul (X⊸ℝ) := ⟨λ f g => ⟨f.1 + g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
  instance : HMul ℝ (X⊸Y) (X⊸Y) := ⟨λ r f => ⟨r * f.1, by have hf := f.2; infer_instance⟩⟩
 
  instance : Zero (X ⊸ Y) := ⟨⟨0, by (conv => enter [1,x]); simp; infer_instance done⟩⟩

  instance : AddSemigroup (X ⊸ Y) := AddSemigroup.mk sorry
  instance : AddMonoid (X ⊸ Y)    := AddMonoid.mk sorry sorry nsmul_rec sorry sorry
  instance : SubNegMonoid (X ⊸ Y) := SubNegMonoid.mk sorry gsmul_rec sorry sorry sorry
  instance : AddGroup (X ⊸ Y)     := AddGroup.mk sorry
  instance : AddCommGroup (X ⊸ Y) := AddCommGroup.mk sorry

  instance : MulAction ℝ (X ⊸ Y) := MulAction.mk sorry sorry
  instance : DistribMulAction ℝ (X ⊸ Y) := DistribMulAction.mk sorry sorry
  instance : Module ℝ (X ⊸ Y) := Module.mk sorry sorry

  instance : Vec (X ⊸ Y) := Vec.mk

  instance : CoeFun (X⊸Y) (λ _ => X→Y) := ⟨λ f => f.1⟩

  def LinMap.mk {X Y  : Type} [Vec X] [Vec Y] (f : X → Y) [IsLin f] : X ⊸ Y := ⟨f, by infer_instance⟩

  -- Right now, I prefer this notation
  macro "fun" xs:Lean.explicitBinders " ⊸ " b:term : term => Lean.expandExplicitBinders `SciLean.LinMap.mk xs b
  macro "λ"   xs:Lean.explicitBinders " ⊸ " b:term : term => Lean.expandExplicitBinders `SciLean.LinMap.mk xs b


  -- @[inferTCGoalsRL]
  instance {X Y ι} [Enumtype ι] [FinVec X ι] [Vec Y] [SemiInner Y] : SemiInner (X ⊸ Y) :=
  {
    Domain := SemiInner.Domain Y
    domain := SemiInner.domain
    semiInner := λ f g Ω => ∑ i, ⟪f (𝔼 i), g (𝔼 i)⟫[Ω]
    testFunction := λ Ω f => ∀ x, SemiInner.testFunction Ω (f x)
  }

  instance {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] : SemiHilbert (X ⊸ Y) :=
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
    semi_inner_gtr := sorry
  }

  instance {X Y ι} [Enumtype ι] [FinVec X ι] [Vec Y] [SemiInner Y] [UniqueDomain Y] : UniqueDomain (X ⊸ Y) :=
  {
    uniqueDomain := UniqueDomain.uniqueDomain (X:=Y)
  }

  instance {X Y ι} [Enumtype ι] [FinVec X ι] [Hilbert Y] : Hilbert (X⊸Y) := Hilbert.mk


  instance (f : X ⊸ Y) : IsLin (λ x => f x) := f.2

  example {X Y Z} [Vec X] [Vec Y] [Vec Z] : Vec ((X ⊸ Y) → Z) := by infer_instance

  variable {W X Y Z : Type} [Vec W] [Vec X] [Vec Y] [Vec Z]
  variable (L : X → Y → Z) [IsLin L] [∀ x, IsLin (L x)]

  example : IsLin (λ (x : W) (f : W ⊸ Y) (a : X) => L a (f x)) := by infer_instance
  example : IsLin (λ (a : X) (f : W → Y) (x : W) => L a (f x)) := by infer_instance
  example : IsLin (λ (f : W → Y) (a : X) (x : W) => L a (f x)) := by infer_instance


  example {α β X Z : Type} [Vec X]  [Vec Z]
    (L : X → β → Z) [IsLin L]
    : IsLin (λ (x : X) (f : α → β) (a : α) => L x (f a)) := by infer_instance
