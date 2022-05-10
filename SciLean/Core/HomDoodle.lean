import SciLean.Core.Mor
import SciLean.Core.Fun
import SciLean.Core.Functions
import SciLean.Core.Hom.SmoothMap
import SciLean.Core.Hom.LinMap

namespace SciLean


  variable {X Y Z} [Vec X] [Vec Y] [Vec Z]

  --------------------------------------------------------------------

  instance (f : X ⟿ Y) : IsSmooth f.1 := f.2

  instance (P : Y → Prop) [Vec ((y : Y) ×' P y)] 
           (f : X → Y) [IsSmooth f] 
           (p : (x : X) → P (f x)) 
           : IsSmooth λ x => PSigma.mk (f x) (p x) := sorry

  instance (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)] (x dx) : IsSmooth (δ f x dx) := sorry

  instance (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)] : IsSmooth λ x => SmoothMap.mk (f x) := sorry
  @[simp]
  theorem smoothmap_mk.arg_x.diff_simp (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)] 
    : δ (λ x => SmoothMap.mk (f x)) = λ x dx => SmoothMap.mk (δ f x dx) := sorry

  --------------------------------------------------------------------

  noncomputable
  def smoothDiff (f : X ⟿ Y) : X ⟿ X ⊸ Y := 
    ⟨λ x => ⟨λ dx => δ f x dx, by infer_instance⟩, by infer_instance⟩

  variable (f : X ⟿ Y)

  #check λ x dx ⟿ δ f.1 x dx

  function_properties PSigma.fst {X} {P : X → Prop} [Vec X] [Vec ((x : X) ×' P x)] (x : ((x : X) ×' P x)) : X
  argument x
    isLin := sorry,
    isSmooth, diff_simp

  function_properties differential {X Y} [Vec X] [Vec Y] (f : X→Y) : X → X → Y
  argument f
    isLin := by admit,
    isSmooth, diff_simp 
  
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
  
  @[simp]
  theorem diff_adj (v : X) [SemiHilbert (X⟿Y)] 
    : (λ (f : X⟿Y) => (λ x ⟿ δ f.1 x v))† = (λ f' => λ x ⟿ - δ f.1 x v) := sorry

  def integral (f : X ⟿ Y) : Y := sorry

  instance : IsLin (λ (f : X ⟿ Y) => integral f) := sorry
  instance : IsSmooth (λ (f : X ⟿ Y) => integral f) := sorry

  @[simp]
  theorem integral.arg_f.diff_simp : δ (λ (f : X ⟿ Y) => integral f) = λ f df => integral df := sorry

  @[simp]
  theorem diff_adj' (v : X) [SemiHilbert (ℝ⟿ℝ)]
    : δ (λ (f : ℝ⟿ℝ) => integral (λ x ⟿ (δ f.1 x 1)*(δ f.1 x 1))) = 
      λ f df => integral (λ x ⟿ ((δ df.1 x (1:ℝ))*(δ f.1 x 1) + (δ f.1 x 1)*(δ df.1 x 1))) :=  
  by 
    simp

  
  
