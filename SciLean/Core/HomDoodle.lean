import SciLean.Core.Mor
import SciLean.Core.Fun
import SciLean.Core.Functions
import SciLean.Core.Hom.SmoothMap
import SciLean.Core.Hom.LinMap
import SciLean.Core.Obj.FinVec

set_option synthInstance.maxSize 2048

namespace SciLean

  namespace HomProps
  
    variable {X Y Z} [Vec X] [Vec Y] [Vec Z]

    instance (P : Y → Prop) [Vec ((y : Y) ×' P y)] 
             (f : X → Y) [IsLin f] 
             (p : (x : X) → P (f x)) 
             : IsLin λ x => PSigma.mk (f x) (p x) := sorry

    instance (f : X → Y → Z) [IsSmooth f] [∀ x, IsLin (f x)] : IsSmooth λ x => LinMap.mk (f x) := sorry


    -- noncomputable
    -- def smoothDiff (f : X ⟿ Y) : X ⟿ X ⊸ Y := 
    --   ⟨λ x => ⟨λ dx => δ f x dx, by infer_instance⟩, by infer_instance⟩

    function_properties PSigma.fst {X} {P : X → Prop} [Vec X] [Vec ((x : X) ×' P x)] (x : ((x : X) ×' P x)) : X
    argument x
      isLin := sorry,
      isSmooth, diff_simp

    instance : IsLin    λ (f : X⟿Y) => δ f.1 := sorry
    instance : IsSmooth λ (f : X⟿Y) => δ f.1 := sorry
    instance {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y]
      : HasAdjoint λ (f : X⟿Y) => λ x ⟿ λ dx ⊸ δ f.1 x dx := sorry
    

  end HomProps

  --------------------------------------------------------------------

  -- function_properties differential {X Y} [Vec X] [Vec Y] (f : X→Y) : X → X → Y
  -- argument f
  --   isLin := by admit,
  --   isSmooth, diff_simp

  namespace tests

    variable {X Y Z} [Vec X] [Vec Y] [Vec Z]

    example : (δ λ (f : X⟿Y) => f) = λ f df => df := 
    by simp

    example : (δ λ (f : X⟿Y) x => f x) = λ f df x => df x := 
    by simp

    example (r : ℝ) : (δ λ (f : X⟿Y) => r*f) = λ (f df : X⟿Y) => r*df := 
    by simp

    example (g : X⟿Y) : (δ λ (f : X⟿Y) => f + g) = λ f df => df := 
    by simp

    example : (δ λ (f : X⟿Y) => δ f.1) = λ f df x dx => δ df.1 x dx := 
    by simp

    example : (δ λ (f : X⟿Y) => δ f.1) = λ f df x dx => δ df.1 x dx := 
    by simp

  end tests

  variable {X Y Z ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] [SemiHilbert Z] [SemiHilbert W]

  instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) [HasAdjoint f] : IsSmooth (f†) := sorry
  instance {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
    (A : X → Y → Z) [IsSmooth A] [∀ x, HasAdjoint (A x)] : IsSmooth λ x => (A x)† := sorry

  @[simp] 
  theorem elem_wise_comp_arg (A : X → Y → Z) [IsSmooth A] [∀ x, HasAdjoint (A x)] [∀ x, IsSmooth (A x)]
    : (λ (f : X ⟿ Y) => λ (x : X) ⟿ (A x) (f x))† = λ (f' : X⟿Z) => λ x ⟿ (A x)† (f' x) := sorry

  @[simp] 
  theorem elem_wise_comp_arg.parm1 (A : X → Y → α → Z) (a : α) [IsSmooth λ x y => A x y a] [∀ x, HasAdjoint (λ y => A x y a)] [∀ x, IsSmooth (λ y => A x y a)]
    : (λ (f : X ⟿ Y) => λ (x : X) ⟿ (A x (f x) a))† = λ (f' : X⟿Z) => λ x ⟿ (λ y => A x y a)† (f' x) := sorry

  @[simp] 
  theorem elem_wise_comp_arg' (A : X → Z → W) [IsSmooth A] [∀ x, HasAdjoint (A x)] [∀ x, IsSmooth (A x)]
    (F : (X⟿Y) → X → Z) [IsSmooth F] [∀ f, IsSmooth (F f)] [HasAdjoint (λ f => λ x ⟿ F f x)]
    : (λ (f : X ⟿ Y) => λ (x : X) ⟿ (A x) (F f x))† = λ (f' : X⟿W) => (λ f => λ x ⟿ F f x)† (λ x ⟿ (A x)† (f' x)) := sorry

  @[simp] 
  theorem elem_wise_comp_arg'.parm1 
    (a : α)
    (A : X → Z → α → W) [IsSmooth λ x z => A x z a] [∀ x, HasAdjoint (λ z => A x z a)] [∀ x, IsSmooth (λ z => A x z a)]
    (F : (X⟿Y) → X → Z) [IsSmooth F] [∀ f, IsSmooth (F f)] [HasAdjoint (λ f => λ x ⟿ F f x)]
    : (λ (f : X ⟿ Y) => λ (x : X) ⟿ (A x (F f x) a))† = λ (f' : X⟿W) => (λ f => λ x ⟿ F f x)† (λ x ⟿ (λ z => A x z a)† (f' x)) := sorry

  noncomputable
  abbrev divergence {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] (f : X⟿X⊸Y) : X⟿Y :=
    λ x ⟿ ∑ i : ι, δ f.1 x (𝔼 i) (𝔼 i)

  noncomputable
  abbrev div {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] (f : X⟿X) : X⟿ℝ :=
    divergence (λ x ⟿ λ dx ⊸ ⟪f x, dx⟫)

  set_option trace.Meta.Tactic.simp.discharge true in
  @[simp]
  theorem differential.adj_f.adj_simp {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y]
    : (λ (f : X⟿Y) => (λ x ⟿ λ dx ⊸ δ f.1 x dx))† 
      = 
      (λ (f' : X ⟿ X ⊸ Y) => λ (x : X) ⟿ - (divergence f' x)) := sorry

  set_option trace.Meta.Tactic.simp.discharge true in
  @[simp]
  theorem differential.adj_f.adj_simp' {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] (v : X)
    : (λ (f : X⟿Y) => (λ x ⟿ δ f.1 x v))† 
      = 
      (λ (f' : X ⟿ Y) => λ (x : X) ⟿ - δ f'.1 x v) := sorry

  -- set_option trace.Meta.synthInstance true in
  example (A : X → Y → Z) [IsSmooth A] [∀ x, HasAdjoint (A x)] [∀ x, IsSmooth (A x)] (f : X → Z) [IsSmooth f]
    : IsSmooth λ x => (A x)† (f x) := by infer_instance

  -- set_option trace.Meta.Tactic.simp.rewrite true in
  -- set_option trace.Meta.Tactic.simp.discharge true in
  example (r : ℝ) : (λ (f : X ⟿ Y) => λ x ⟿ r * f x)† = λ (f' : X⟿Y) =>  (r * f') := by funext f'; ext x; simp[HMul.hMul] done

  example (r : ℝ) : (λ (f : X→Y) (x : X) => r * f x) = (λ (f : X→Y) => r * f) := by simp; funext f x; simp

  example (g : X⟿ℝ)
    : (λ (f : X⟿Y) => λ x ⟿ g x * f x)† = λ (f' : X⟿Y) => (λ x ⟿ g x * f' x) := by simp

  set_option trace.Meta.Tactic.simp.discharge true in
  example {Y} [Hilbert Y] (g : X⟿Y)
    : (λ (f : X⟿Y) => λ x ⟿ ⟪g x, f x⟫)† = λ (f' : X⟿ℝ) => (λ x ⟿ f' x * g x) := 
  by simp done

  example {Y} [Hilbert Y] (A : X⊸Y) : IsSmooth (λ B => ⟪A,B⟫) := by infer_instance

  -- set_option trace.Meta.Tactic.simp.discharge true in
  -- set_option trace.Meta.synthInstance true in
  example {Y} [Hilbert Y] (g : X⟿X⊸Y)
    : (λ (f : X⟿Y) => λ x ⟿ ⟪g x, λ dx ⊸ δ f.1 x dx⟫)† = 0 := 
  by 
    simp


/-
v  @[simp]
  theorem diff_adj' (v : X)
    : δ (λ (f : ℝ⟿ℝ) => integral (λ x ⟿ (δ f.1 x 1)*(δ f.1 x 1))) 
      = 
      λ f df => integral (λ x ⟿ ((δ df.1 x (1:ℝ))*(δ f.1 x 1) + (δ f.1 x 1)*(δ df.1 x 1))) :=  
  by simp

  @[simp]
  theorem asdf (P : (X → Y) → Prop) [Vec ((h : X → Y) ×' P h)] (f g : (h : X → Y) ×' P h) (x : X) : (f + g).1 x = f.1 x + g.1 x := sorry
  @[simp]
  theorem asdf2 (P : (X → Y) → Prop) [Vec ((h : X → Y) ×' P h)] (f g : (h : X → Y) ×' P h) (x : X) : (f - g).1 x = f.1 x + g.1 x := sorry

  example (f g : X⟿Y) (x : X) : (f + g) x = f x + g x := by simp

  @[simp]
  theorem hmul_fun_adj (g : X⟿ℝ) [SemiHilbert (X⟿ℝ)] : (λ (f : X⟿ℝ) => λ x ⟿ g x * f x)† = λ f' => λ x ⟿ g x * f' x := sorry



  @[simp]
  theorem smul_adj_arg (g : X⟿ℝ) [SemiHilbert (X⟿Y)] : (λ (f : X⟿Y) => λ x ⟿ g x * f x)† = λ (f' : X⟿Y) => λ x ⟿ g x * f' x := sorry
  
  @[simp]
  theorem smul_pointwise_adj (g : X⟿ℝ) [SemiHilbert (X⟿Y)] : (λ (f : X⟿Y) => g * f)† = λ (f' : X⟿Y) => g * f' := 
  by
    rw[!?((λ (f : X⟿Y) => g * f) = λ (f : X⟿Y) => λ x ⟿ g x * f x)]
    simp

  instance : SemiInner (X ⟿ Y) := SemiInner.mk sorry sorry sorry sorry
  instance : SemiHilbert (X ⟿ Y) := SemiHilbert.mk sorry sorry sorry sorry sorry sorry

  set_option pp.all true in
  @[simp]
  theorem smul_adj (r : ℝ) : (λ (f : X⟿Y) => r * f)† = λ (f' : X⟿Y) => r * f' := 
  by
    simp

-/


  def integral {X Y ι} [Enumtype ι] [FinVec X ι] [Vec Y] (f : X ⟿ Y) : 𝓓 X → Y := sorry


  instance : IsLin    (λ (f : X ⟿ Y) => integral f) := sorry
  instance : IsSmooth (λ (f : X ⟿ Y) => integral f) := sorry

  @[simp]
  theorem integral.arg_f.diff_simp : δ (λ (f : X ⟿ Y) => integral f) = λ f df => integral df := sorry

  @[simp]
  theorem integral_diff_simp 
    : δ (λ (f : X⟿Y) => integral f)  = λ f df => integral df := sorry

  example
    : δ (λ (f : X⟿Y) => integral ((2:ℝ)*f))  = λ f df => integral ((2:ℝ)*df) := by simp

  example (g : X⟿Y)
    : δ (λ (f : X⟿Y) => integral (f + g))  = λ f df => integral (df) := by simp

  example (g : X⟿Y)
    : δ (λ (f : X⟿Y) => integral (λ x ⟿ f x + g x))  = λ f df => integral (df) := by simp

  example (g : X⟿ℝ)
    : δ (λ (f : X⟿Y) => integral (λ x ⟿ g x * f x))  = λ (f df : X⟿Y) => integral (λ x ⟿ g x * df x) := by simp

  example (g : X⟿ℝ)
    : δ (λ (f : X⟿Y) => integral (λ x ⟿ g x * δ f.1 x x))  = λ (f df : X⟿Y) => integral (λ x ⟿ g x * δ df.1 x x) := by simp

