import SciLean.Core.Mor
import SciLean.Core.Fun
import SciLean.Core.Functions
import SciLean.Core.Obj.FinVec

namespace SciLean

  structure SmoothMap (X Y : Type) [Vec X] [Vec Y] where
    val : X → Y 
    is_smooth : IsSmooth val

  infixr:25 " ⟿ " => SmoothMap

  variable {X Y} [Vec X] [Vec Y]

  variable (f : X → Y) [IsSmooth f]
  variable (g : X → Y) [IsSmooth g]
  variable (r : ℝ)

  instance : IsSmooth (-f)    := by (conv => enter [1,x]); simp; infer_instance; done
  instance : IsSmooth (f + g) := by (conv => enter [1,x]); simp; infer_instance; done
  instance : IsSmooth (f - g) := by (conv => enter [1,x]); simp; infer_instance; done
  instance : IsSmooth (r * f) := by (conv => enter [1,x]); simp; infer_instance; done
  instance (f g : X → ℝ) [IsSmooth f] [IsSmooth g]
    : IsSmooth (f * g) := by (conv => enter [1,x]); simp; infer_instance; done
  instance : IsSmooth (0 : X → Y) :=  by (conv => enter [1,x]); simp; infer_instance; done
  instance : IsSmooth (1 : X → ℝ) :=  by (conv => enter [1,x]); simp; infer_instance; done

  instance : Neg (X⟿Y) := ⟨λ f   => ⟨-f.1, by have hf := f.2; infer_instance⟩⟩
  instance : Add (X⟿Y) := ⟨λ f g => ⟨f.1 + g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
  instance : Sub (X⟿Y) := ⟨λ f g => ⟨f.1 - g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
  instance : Mul (X⟿ℝ) := ⟨λ f g => ⟨f.1 * g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
  instance : HMul ℝ (X⟿Y) (X⟿Y) := ⟨λ r f => ⟨r * f.1, by have hf := f.2; infer_instance⟩⟩
  instance : HMul (X⟿ℝ) (X⟿Y) (X⟿Y) := ⟨λ g f => ⟨λ x => g.1 x * f.1 x, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
 
  instance : Zero (X ⟿ Y) := ⟨⟨0, by (conv => enter [1,x]); simp; infer_instance; done⟩⟩
  instance [One Y] : One (X ⟿ Y) := ⟨⟨1, by (conv => enter [1,x]); simp; infer_instance; done⟩⟩

  instance : AddSemigroup (X ⟿ Y) := AddSemigroup.mk sorry
  instance : AddMonoid (X ⟿ Y)    := AddMonoid.mk sorry sorry nsmulRec sorry sorry
  instance : SubNegMonoid (X ⟿ Y) := SubNegMonoid.mk sorry zsmulRec sorry sorry sorry
  instance : AddGroup (X ⟿ Y)     := AddGroup.mk sorry
  instance : AddCommGroup (X ⟿ Y) := AddCommGroup.mk sorry

  instance : MulAction ℝ (X ⟿ Y) := MulAction.mk sorry sorry
  instance : DistribMulAction ℝ (X ⟿ Y) := DistribMulAction.mk sorry sorry
  instance : Module ℝ (X ⟿ Y) := Module.mk sorry sorry

  -- IMPORTANT: I think that `X → Y` and `X ⟿ Y` should not have the same
  -- topology. `X → Y` is just a product topology/initial topology based on all
  -- evaluations for every `x : X`. However `X ⟿ Y` has topology given by point 5 in:
  -- https://en.wikipedia.org/wiki/Convenient_vector_space#Main_properties_of_smooth_calculus
  instance : Vec (X ⟿ Y) := Vec.mk

  -- instance : Coe (X⟿Y) (X→Y) := ⟨λ f => f.1⟩
  instance : CoeFun (X⟿Y) (λ _ => X→Y) := ⟨λ f => f.1⟩


  --- TODO: This should fail fast!!! but it does not :(
  -- set_option synthInstance.maxHeartbeats 5000 in
  -- example {X Y} [Vec X] [Vec Y] (f df : X ⟿ Y) : IsLin (∂ (λ (f : X ⟿ Y) => ∂ f.1) f df) := 
  -- by
  --   infer_instance

  instance {X Y : Type} [Vec X] [Vec Y] : VecProp (X := X → Y) IsSmooth := sorry

  --------------------------------------------------------------------

  instance (f : X ⟿ Y) : IsSmooth f.1 := f.2

  @[ext] 
  theorem SmoothMap.ext {X Y} [Vec X] [Vec Y] (f g : X ⟿ Y) : (∀ x, f x = g x) → f = g := sorry

  --------------------------------------------------------------------

  @[macro_inline]
  abbrev SmoothMap.mk' {X Y  : Type} [Vec X] [Vec Y] (f : X → Y) [inst : IsSmooth f] : X ⟿ Y := ⟨f, inst⟩

  def SmoothMap.incl {X Y : Type} [Vec X] [Vec Y] (f : {f' : X → Y // IsSmooth f'}) : X ⟿ Y := ⟨f.1, f.2⟩

  -- TODO: This is a big big question if this is actually correct
  instance {X Y : Type} [Vec X] [Vec Y] : IsSmooth (SmoothMap.incl (X := X) (Y := Y)) := sorry

  -- Right now, I prefer this notation
  open Lean.TSyntax.Compat in
  macro "fun" xs:Lean.explicitBinders " ⟿ " b:term : term => Lean.expandExplicitBinders `SciLean.SmoothMap.mk' xs b
  open Lean.TSyntax.Compat in
  macro "λ"   xs:Lean.explicitBinders " ⟿ " b:term : term => Lean.expandExplicitBinders `SciLean.SmoothMap.mk' xs b

  @[simp] 
  theorem SmoothMap.beta_reduce (f : X ⟿ Y) 
      : (λ (x : X) ⟿ f x) = f := by simp; done

  -- @[simp]
  -- theorem SmoothMap.mk.eval (f : X → Y) [IsSmooth f] (x : X) 
  --   : (SmoothMap.mk f) x = f x := by simp
  -- The above theorem causes this example to fail with a very obscure error
  -- example {X Y} [Vec Y] (r : ℝ) : (λ (f : X→Y) (x : X) => r * f x) = (λ (f : X→Y) => r * f) := by funext f x; simp;; done

  @[simp]
  theorem SmoothMap.mk.arg_f.diff_simp {X Y} [Vec X] [Vec Y] 
    (f : X → Y) [IsSmooth f] 
    : ∂ (SmoothMap.mk' f).1 = ∂ f := by simp; done

  -- TODO: IMPORTANT: I'm really uncertain about this theorem. Is it really true.
  -- If not then then whole thing might fall apart :(
  instance SmoothMap.mk.arg_x.isSmooth {X Y Z} [Vec X] [Vec Y] [Vec Z] 
    (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
    : IsSmooth λ x => SmoothMap.mk' (f x) := 
  by
    let h : (λ x => SmoothMap.mk' (f x))
            =
            λ x => SmoothMap.incl ⟨f x, by infer_instance⟩
          := by rfl
    rw [h]
    apply @comp.arg_x.isSmooth _ _ _ _ _ _ _ (by infer_instance) _ (by admit)
    done

  @[simp]
  theorem SmoothMap.mk.arg_x.diff_simp {X Y Z} [Vec X] [Vec Y] [Vec Z]
    (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
    : ∂ (λ x => SmoothMap.mk' (f x)) = λ x dx => SmoothMap.mk' (∂ f x dx) := sorry_proof


  instance SmoothMap.mk.arg_x.isLin {X Y Z} [Vec X] [Vec Y] [Vec Z] 
    (f : X → Y → Z) [IsLin f] [∀ x, IsSmooth (f x)]
    : IsLin λ x => SmoothMap.mk' (f x) := sorry_proof

  -- instance SmoothMap.mk.arg_x.parm1.isSmooth {X Y Z} [Vec X] [Vec Y] [Vec Z] 
  --   (f : X → Y → α → Z) (a : α) [IsSmooth λ x y => f x y a] [∀ x, IsSmooth (λ y => f x y a)]
  --   (g : X → Y → Y) [IsSmooth g] [∀ x, IsSmooth (g x)]
  --   : IsSmooth λ x => SmoothMap.mk (λ y => f x (g x y) a) := by infer_instance

  --------------------------------------------------------------------

  -- This times out when we try to synthetize it :( It should just fail.
  -- Can we somehow make sure that is fails fast?
  instance differential.arg_f.isSmooth : IsSmooth (λ (f : X⟿Y) => ∂ f.1) := sorry

  -- This times out as it tries to prove:
  --       IsSmooth (λ (f : X→Y) => ∂ f x dx)
  -- which is not true.
  -- With sufficient heartbeats it can be proven, we add it to create a quick path
  -- set_option synthInstance.maxHeartbeats 500000 in
  instance differential.arg_f.parm_dx.isSmooth (dx : X) 
    : IsSmooth (λ (f : X⟿Y) (x : X) => ∂ f.1 x dx) := sorry

  @[simp]
  theorem differential.arg_f.diff_simp : ∂ (λ (f : X⟿Y) => ∂ f.1) = λ f df => ∂ df.1 := sorry

  -- @[simp]
  -- theorem differential.arg_f.parm_x.diff_simp (dx : X) : ∂ (λ (f : X⟿Y) (x : X) => ∂ f.1 x dx) = λ f df  x=> ∂ df.1 x dx := by simp

  --------------------------------------------------------------------

  instance {X Y ι} [Enumtype ι] [FinVec X ι] [Vec Y] [Inner Y] : Inner (X ⟿ Y) where
    inner := sorry

  instance {X Y ι} [Enumtype ι] [FinVec X ι] [Vec Y] [TestFunctions Y] : TestFunctions (X ⟿ Y) where
    TestFun := sorry -- compactly supported functions with values in test functions    
    is_lin_subspace := sorry


  instance {X Y} {ι : Type} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] : SemiHilbert (X ⟿ Y) where
    inner_add := sorry
    inner_mul := sorry
    inner_sym := sorry
    inner_pos := sorry
    inner_ext := sorry

  variable {Z} [SemiHilbert Z]

  example : SemiHilbert (ℝ ⟿ Z) := 
  by 
    infer_instance
    -- apply instSemiHilbertSmoothMapToVecToSemiHilbertToHilbert (X:= ℝ) (Y:=Z) (ι := Unit)

