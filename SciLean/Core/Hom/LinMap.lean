import SciLean.Core.Mor
import SciLean.Core.Fun
import SciLean.Core.Functions
import SciLean.Core.Obj.FinVec
import SciLean.Core.Hom.SmoothMap

namespace SciLean

  abbrev LinMap (X Y : Type) [Vec X] [Vec Y] := {f : X → Y // IsLin f}

  infixr:25 " ⊸ " => LinMap

  variable {X Y} [Vec X] [Vec Y]

  section BasicInstances

    variable (f : X → Y) [IsLin f]
    variable (g : X → Y) [IsLin g]
    variable (r : ℝ)

    instance : IsLin (-f)    := by (conv => enter [1,x]); simp; infer_instance; done
    instance : IsLin (f + g) := by (conv => enter [1,x]); simp; infer_instance; done
    instance : IsLin (f - g) := by (conv => enter [1,x]); simp; infer_instance; done
    instance : IsLin (r * f) := by (conv => enter [1,x]); simp; infer_instance; done
    instance : IsLin (0 : X → Y) :=  by (conv => enter [1,x]); simp; infer_instance; done

    instance : Neg (X⊸Y) := ⟨λ f   => ⟨-f.1, by have hf := f.2; infer_instance⟩⟩
    instance : Add (X⊸Y) := ⟨λ f g => ⟨f.1 + g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
    instance : Sub (X⊸Y) := ⟨λ f g => ⟨f.1 + g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
    instance : Mul (X⊸ℝ) := ⟨λ f g => ⟨f.1 + g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
    instance : HMul ℝ (X⊸Y) (X⊸Y) := ⟨λ r f => ⟨r * f.1, by have hf := f.2; infer_instance⟩⟩

    instance : Zero (X ⊸ Y) := ⟨⟨0, by (conv => enter [1,x]); simp; infer_instance; done⟩⟩

    instance : AddSemigroup (X ⊸ Y) := AddSemigroup.mk sorry
    instance : AddMonoid (X ⊸ Y)    := AddMonoid.mk sorry sorry nsmulRec sorry sorry
    instance : SubNegMonoid (X ⊸ Y) := SubNegMonoid.mk sorry zsmulRec sorry sorry sorry
    instance : AddGroup (X ⊸ Y)     := AddGroup.mk sorry
    instance : AddCommGroup (X ⊸ Y) := AddCommGroup.mk sorry

    instance : MulAction ℝ (X ⊸ Y) := MulAction.mk sorry sorry
    instance : DistribMulAction ℝ (X ⊸ Y) := DistribMulAction.mk sorry sorry
    instance : Module ℝ (X ⊸ Y) := Module.mk sorry sorry

    instance : Vec (X ⊸ Y) := Vec.mk

    instance : Coe (X⊸Y) (X⟿Y) := ⟨λ f => ⟨f.1, by have h := f.2; apply linear_is_smooth⟩⟩
    instance : CoeFun (X⊸Y) (λ _ => X→Y) := ⟨λ f => f.1⟩

  end BasicInstances


  --------------------------------------------------------------------

  @[inline]
  abbrev LinMap.mk {X Y  : Type} [Vec X] [Vec Y] (f : X → Y) [inst : IsLin f] : X ⊸ Y := ⟨f, inst⟩

  -- Right now, I prefer this notation
  open Lean.TSyntax.Compat in
  macro "fun" xs:Lean.explicitBinders " ⊸ " b:term : term => Lean.expandExplicitBinders `SciLean.LinMap.mk xs b
  open Lean.TSyntax.Compat in
  macro "λ"   xs:Lean.explicitBinders " ⊸ " b:term : term => Lean.expandExplicitBinders `SciLean.LinMap.mk xs b

  --------------------------------------------------------------------

  instance (f : X ⊸ Y) : IsLin f.1 := f.2
  instance (f : X ⊸ Y) : IsSmooth f.1 := linear_is_smooth f.1

  @[ext] 
  theorem LinMap.ext {X Y} [Vec X] [Vec Y] (f g : X ⊸ Y) : (∀ x, f x = g x) → f = g := sorry

  @[simp] 
  theorem LinMap.beta_reduce (f : X ⊸ Y) 
      : (λ (x : X) ⊸ f x) = f := by simp

  -- @[simp]
  theorem LinMap.mk.eval (f : X → Y) [IsLin f] (x : X) 
    : (LinMap.mk f) x = f x := by simp

  -- This simp theorem does not work for unbundled morphisms because it contains variable head
  @[simp]
  theorem LinMap.mk.arg_f.diff_simp {X Y} [Vec X] [Vec Y] 
    (f : X → Y) [IsLin f] 
    : ∂ (LinMap.mk f).1 = λ _ dx => f dx := by simp[LinMap.mk]; apply diff_of_linear; done

  @[simp]
  theorem LinMap.mk.arg_x.diff_simp {X Y Z} [Vec X] [Vec Y] [Vec Z]
    (f : X → Y → Z) [IsSmooth f] [∀ x, IsLin (f x)]
    : ∂ (λ x => LinMap.mk (f x)) = λ x dx => LinMap.mk (∂ f x dx) := by simp

  -- This instance is still necessary to typecheck: `λ x ⟿ λ dx ⊸ ∂ f x dx`
  -- I do not understand why is it necessary if it can be infered automatically
  instance LinMap.mk.arg_x.isSmooth {X Y Z} [Vec X] [Vec Y] [Vec Z] 
    (f : X → Y → Z) [IsSmooth f] [∀ x, IsLin (f x)]
    : IsSmooth λ x => LinMap.mk (f x) := by infer_instance

  instance LinMap.mk.arg_x.isLin {X Y Z} [Vec X] [Vec Y] [Vec Z] 
    (f : X → Y → Z) [IsLin f] [∀ x, IsLin (f x)]
    : IsLin λ x => LinMap.mk (f x) := by infer_instance


   section differential_map_test

    variable (f : X → Y) [IsSmooth f] (A : X → Y) [IsLin A] (g : X ⟿ Y)

    #check λ x ⊸ A x
    #check λ x dx ⟿ ∂ f x dx
    #check λ x ⟿ λ dx ⊸ ∂ f x dx
    #check λ x ⟿ λ dx ⊸ ∂ g.1 x dx


  end differential_map_test

  --------------------------------------------------------------------

  -- @[inferTCGoalsRL]
  instance {X Y ι} [Enumtype ι] [FinVec X ι] [Vec Y] [Inner Y] : Inner (X ⊸ Y) where
    inner := λ f g => ∑ i, ⟪f (𝔼 i), g (𝔼 i)⟫

  instance {X Y ι} [Enumtype ι] [FinVec X ι] [Vec Y] [TestFunctions Y] : TestFunctions (X ⊸ Y) where
    TestFun f := ∀ x, TestFun (f x)
    is_lin_subspace := sorry

  instance {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] : SemiHilbert (X ⊸ Y) where
    inner_add := sorry
    inner_mul := sorry
    inner_sym := sorry
    inner_pos := sorry
    inner_ext := sorry

  instance {X Y ι} [Enumtype ι] [FinVec X ι] [Hilbert Y] : Hilbert (X⊸Y) where
    all_are_test := sorry

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


  ----------------------------------------------------------------------------------------

  noncomputable
  instance : Differential (X ⟿ Y) (X ⟿ X ⊸ Y) where
    differential := λ f => λ x ⟿ λ dx ⊸ ∂ f.1 x dx

  class Compose (HomYZ HomXY : Type) (HomXZ : outParam Type) where
    compose : HomYZ → HomXY → HomXZ 

  instance {X Y Z : Type} : Compose (Y → Z) (X → Y) (X → Z) where
    compose f g x := f (g x)

  instance {X Y Z : Type} [Vec X] [Vec Y] [Vec Z] : Compose (Y ⟿ Z) (X ⟿ Y) (X ⟿ Z) where
    compose f g := λ x ⟿ f (g x)

  macro(priority := high) f:term "∘" g:term :term => `(Compose.compose $f $g)

  @[simp]
  theorem differential_normalize_on_smooth_map (f : X ⟿ Y) 
    : (λ x ⟿ λ dx ⊸ ∂ f.1 x dx) = ∂ f := by simp[Differential.differential]; done

  @[simp]
  theorem differential_normalize_on_smooth_map_2 (f : X → Y) [IsSmooth f]
    : ∂ (λ x ⟿ f x) = (λ x ⟿ λ dx ⊸ ∂ f x dx) := by simp[Differential.differential]; done


  -- variable (f : Y ⟿ Z) (g : X ⟿ Y) (x : X) (A : X ⊸ Y) (y : Y)
    -- : ∂ (f ∘ g) = 


  -- #check λ x ⟿ A x
  -- set_option trace.Meta.synthInstance true in
  -- #check λ x ⟿ λ dx ⟿ ∂ f (g x) (g dx)
  -- #check λ x ⟿ (λ dx ⊸ ∂ f.1 (g x) (∂ g.1 x dx))
