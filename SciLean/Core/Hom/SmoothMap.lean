import SciLean.Core.Mor
import SciLean.Core.Fun
import SciLean.Core.Functions
import SciLean.Core.Obj.FinVec


namespace SciLean

  abbrev SmoothMap (X Y : Type) [Vec X] [Vec Y] := (f : X → Y) ×' (IsSmooth f)

  infixr:25 " ⟿ " => SmoothMap

  variable {X Y} [Vec X] [Vec Y]

  variable (f : X → Y) [IsSmooth f]
  variable (g : X → Y) [IsSmooth g]
  variable (r : ℝ)

  instance : IsSmooth (-f)    := by (conv => enter [1,x]); simp; infer_instance done
  instance : IsSmooth (f + g) := by (conv => enter [1,x]); simp; infer_instance done
  instance : IsSmooth (f - g) := by (conv => enter [1,x]); simp; infer_instance done
  instance : IsSmooth (r * f) := by (conv => enter [1,x]); simp; infer_instance done
  instance (f g : X → ℝ) [IsSmooth f] [IsSmooth g]
    : IsSmooth (f * g) := by (conv => enter [1,x]); simp; infer_instance done
  instance : IsSmooth (0 : X → Y) :=  by (conv => enter [1,x]); simp; infer_instance done
  instance : IsSmooth (1 : X → ℝ) :=  by (conv => enter [1,x]); simp; infer_instance done

  instance : Neg (X⟿Y) := ⟨λ f   => ⟨-f.1, by have hf := f.2; infer_instance⟩⟩
  instance : Add (X⟿Y) := ⟨λ f g => ⟨f.1 + g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
  instance : Sub (X⟿Y) := ⟨λ f g => ⟨f.1 + g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
  instance : Mul (X⟿ℝ) := ⟨λ f g => ⟨f.1 + g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
  instance : HMul ℝ (X⟿Y) (X⟿Y) := ⟨λ r f => ⟨r * f.1, by have hf := f.2; infer_instance⟩⟩
  instance : HMul (X⟿ℝ) (X⟿Y) (X⟿Y) := ⟨λ g f => ⟨λ x => g.1 x * f.1 x, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
 
  instance : Zero (X ⟿ Y) := ⟨⟨0, by (conv => enter [1,x]); simp; infer_instance done⟩⟩
  instance : One (X ⟿ ℝ) := ⟨⟨1, by (conv => enter [1,x]); simp; infer_instance done⟩⟩

  instance : AddSemigroup (X ⟿ Y) := AddSemigroup.mk sorry
  instance : AddMonoid (X ⟿ Y)    := AddMonoid.mk sorry sorry nsmul_rec sorry sorry
  instance : SubNegMonoid (X ⟿ Y) := SubNegMonoid.mk sorry gsmul_rec sorry sorry sorry
  instance : AddGroup (X ⟿ Y)     := AddGroup.mk sorry
  instance : AddCommGroup (X ⟿ Y) := AddCommGroup.mk sorry

  instance : MulAction ℝ (X ⟿ Y) := MulAction.mk sorry sorry
  instance : DistribMulAction ℝ (X ⟿ Y) := DistribMulAction.mk sorry sorry
  instance : Module ℝ (X ⟿ Y) := Module.mk sorry sorry

  instance : Vec (X ⟿ Y) := Vec.mk

  instance : Coe (X⟿Y) (X→Y) := ⟨λ f => f.1⟩
  instance : CoeFun (X⟿Y) (λ _ => X→Y) := ⟨λ f => f.1⟩

  --------------------------------------------------------------------

  instance (f : X ⟿ Y) : IsSmooth f.1 := f.2

  @[ext] 
  theorem SmoothMap.ext {X Y} [Vec X] [Vec Y] (f g : X ⟿ Y) : (∀ x, f x = g x) → f = g := sorry

  --------------------------------------------------------------------

  -- Ideally abbrev but it causes some problems with infinite simp loop
  def SmoothMap.mk {X Y  : Type} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f] : X ⟿ Y := ⟨f, by infer_instance⟩

  -- Right now, I prefer this notation
  macro "fun" xs:Lean.explicitBinders " ⟿ " b:term : term => Lean.expandExplicitBinders `SciLean.SmoothMap.mk xs b
  macro "λ"   xs:Lean.explicitBinders " ⟿ " b:term : term => Lean.expandExplicitBinders `SciLean.SmoothMap.mk xs b


  @[simp] 
  theorem SmoothMap.beta_reduce (f : X ⟿ Y) 
      : (λ (x : X) ⟿ f x) = f := sorry

  @[simp]
  theorem SmoothMap.mk.eval (f : X → Y) [IsSmooth f] (x : X) 
    : PSigma.fst (SmoothMap.mk f) x = f x := sorry

  instance SmoothMap.mk.arg_x.isSmooth {X Y Z} [Vec X] [Vec Y] [Vec Z] 
    (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
    : IsSmooth λ x => SmoothMap.mk (f x) := sorry

  -- instance SmoothMap.mk.arg_x.parm1.isSmooth {X Y Z} [Vec X] [Vec Y] [Vec Z] 
  --   (f : X → Y → α → Z) (a : α) [IsSmooth λ x y => f x y a] [∀ x, IsSmooth (λ y => f x y a)]
  --   (g : X → Y → Y) [IsSmooth g] [∀ x, IsSmooth (g x)]
  --   : IsSmooth λ x => SmoothMap.mk (λ y => f x (g x y) a) := by infer_instance

  @[simp]
  theorem SmoothMap.mk.arg_f.diff_simp {X Y} [Vec X] [Vec Y] 
    (f : X → Y) [IsSmooth f] 
    : δ (SmoothMap.mk f).1 = δ f := by simp[SmoothMap.mk] done

  @[simp]
  theorem SmoothMap.mk.arg_x.diff_simp {X Y Z} [Vec X] [Vec Y] [Vec Z]
    (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
    : δ (λ x => SmoothMap.mk (f x)) = λ x dx => SmoothMap.mk (δ f x dx) := sorry

  instance PSigma.mk.arg_x.isSmooth
           (P : Y → Prop) [Vec ((y : Y) ×' P y)] 
           (f : X → Y) [IsSmooth f] 
           (p : (x : X) → P (f x)) 
           : IsSmooth λ x => PSigma.mk (f x) (p x) := sorry

  -- @[simp]
  -- theorem PSigma.mk.arg_x.diff_simp
  --          (P : Y → Prop) [Vec ((y : Y) ×' P y)] 
  --          (f : X → Y) [IsSmooth f] 
  --          (p : (x : X) → P (f x)) 
  --          : (δ λ x => PSigma.mk (f x) (p x)) = λ x dx => PSigma.mk (δ f x dx) sorry := sorry

  --------------------------------------------------------------------
  
  instance differential.arg_f.isSmooth : IsSmooth (λ (f : X⟿Y) => δ f.1) := sorry

  @[simp]
  theorem differential.arg_f.diff_simp : δ (λ (f : X⟿Y) => δ f.1) = λ f df => δ df.1 := sorry


  --------------------------------------------------------------------

  instance {X Y ι} [Enumtype ι] [FinVec X ι] [Vec Y] [SemiInner Y] : SemiInner (X ⟿ Y) :=
  {
    Domain := sorry
    domain := sorry
    semiInner := sorry
    testFunction := sorry
  }

  instance {X Y} {ι : Type} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] : SemiHilbert (X ⟿ Y) :=
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
    semi_inner_gtr := sorry
  }

  variable {Z} [SemiHilbert Z]

  set_option pp.all true in
  example : SemiHilbert (ℝ ⟿ Z) := 
  by 
    try infer_instance
    -- apply instSemiHilbertSmoothMapToVecToSemiHilbertToHilbert (X:= ℝ) (Y:=Z) (ι := Unit)

  
