import SciLean.Data.PowType
import SciLean.Core.Hom.SmoothMap
import SciLean.Core.Hom.LinMap

namespace SciLean

  -- #check Set
  
  -- class HasIntegral {X} (X : Type) [Vec X] where
  --   intDom : Set (Set X) -- integrable domains
  --   isIntegrable {Y} [Vec Y] (f : X → Y) : Prop
  --   integral (f : X → Y) (h : isIntegrable f) (Ω ∈ intDom) 


  -- The argument are most likely:
  --  Fun    = X → Y or X ⟿ Y or X ⊸ Y
  --  Dom    = open sets of X
  --  Result = Y

  -- class Integral (Fun : Type) (Dom : outParam Type) (Result : outParam Type) /- (Integrable : outParam $ Fun → Dom → Prop) -/ where
  --   integral : Fun → Dom → Result
  -- class HasVarDual {Fun Dom Result} [SemiHilbert Fun] [Integral Fun Dom Result] (f : Fun → Dom → Result) : Prop where
  --   has_var_dual : ∃ f' : Fun, ∀ (g : Fun) (r : Result) (Ω : Dom) (h : TestFunctionOn g Ω) (hr : TestFunction r),
  --     ⟪f g Ω, r⟫[hr] = ⟪⟪f',g⟫[h], r⟫[hr]

  class IntegrableDomain (X : Type) where
    Dom : Type

  def TestFunction [SemiHilbert X] (x : X) : Prop := sorry

  variable {ι} [Enumtype ι]

  def IsOpen {X} [FinVec X ι] (Ω : Set X) : Prop := sorry
  def IsBounded {X} [FinVec X ι] (Ω : Set X) : Prop := sorry

  def IntDom (X : Type) [FinVec X ι] : Type := {Ω : Set X // IsOpen Ω}
  def LocIntDom (X : Type) [FinVec X ι] : Type := {Ω : Set X // IsOpen Ω ∧ IsBounded Ω}

  -- Probably Riemann integrability on domain Ω
  class IsIntegrable [FinVec X ι] [Vec Y] (f : X → Y) (Ω : IntDom X) : Prop
  class IsLocIntegrable [FinVec X ι] [Vec Y] (f : X → Y) : Prop where
    is_loc_integrable : ∀ Ω : LocIntDom X, IsIntegrable f ⟨Ω.1, Ω.2.1⟩


  -- If `f` is integrable on `Ω` return integral otherwise return zero
  -- We choose to integrate only over bounded domains.
  -- This way the function `λ (f : X⟿Y) => ∫ x, f x` can be linear.
  def integral {X Y : Type} [FinVec X ι] [Vec Y] (f : X → Y) (Ω : LocIntDom X) : Y := sorry

  class Integral (α : Type) (β : outParam Type) where
    integral : α → β

  attribute [reducible] Integral.integral

  @[reducible]
  instance {X Y : Type} [FinVec X ι] [Vec Y] : Integral (X → Y) (LocIntDom X → Y) where
    integral f := integral f

  @[reducible]
  instance {X Y : Type} [FinVec X ι] [Vec Y] : Integral (X ⟿ Y) (LocIntDom X → Y) where
    integral f := integral f

   -- some basic properties about linearity, domain and relation to derivative
    
  -- class HasVarDual {X Y : Type} {P : (X → Y) → Prop} [FinVec X ι] [Hilbert Y] (F : {g : X → Y // P g} → IntDom X → ℝ) where
  --   has_var_dual : ∃ f' : X → Y, ∀ g,
  --     F g = integral λ x => ⟪f' x, g.1 x⟫

    -- some continuity condition on smooth or integrable functions or something like that
    -- F should be trivial on non-smooth/non-integrable functions
    -- Effectivelly functions like F = λ f => ∫ x, (f x) 
      
  -- export Integral (integral)

  -- abbrev integral {Fun : Type} {Dom Result : outParam Type} [outParam $ Integral Fun Dom Result] (f : Fun) (Ω : Dom) : Result := Integral.integral f Ω

  --- Notation 
  --  - ∫ f          -- shorthand for the next
  --  - ∫ x, f x     -- Return function from subset to integral over that subset
  --  - ∫ x ∈ Ω, f x -- Integrate over particular subset
  --  - ∫ x : X, f x -- Integrate over the whole set

  macro "∫" f:term : term => `(Integral.integral $f)
  macro "∫" x:ident "," fx:term : term => `(integral λ $x => $fx)
  
  variable {X Y Z} [Vec Y] [FinVec X ι] [Vec Z]

  instance SmoothMap.val.arg_f.isLin : IsLin (λ f : X⟿Y => f.1) := sorry
  instance SmoothMap.val.arg_f.isSmooth : IsSmooth (λ f : X⟿Y => f.1) := sorry

  @[simp]
  theorem SmoothMap.val.arg_f.diff_simp 
    : ∂ (λ f : X⟿Y => f.1) = λ f df => df.1 := 
  by 
    apply diff_of_linear; done

  -- We can't prove linearity of differential directly
  -- instance (F : (X⟿Y) → (X → Y)) [IsLin F] [∀ f, IsSmooth (F f)] 
  --   : IsLin λ (f : X⟿Y) => ∂ (F f) := by infer_instance
  -- instance (F : (X⟿Y) → (X → Y)) [IsSmooth F] [∀ f, IsSmooth (F f)] 
  --   : IsSmooth λ (f : X⟿Y) => ∂ (F f) := by infer_instance

  instance (F : Z → X → Y) [IsLin F] [∀ f, IsSmooth (F f)] 
    : IsLin λ (z : Z) => ∫ x, F z x := sorry
  instance (F : Z → X → Y) [IsSmooth F] [∀ f, IsSmooth (F f)] 
    : IsSmooth λ (z : Z) => ∫ x, F z x := sorry

  @[simp] 
  theorem integral_diff (F : Z → X → Y) [IsSmooth F] [∀ f, IsSmooth (F f)]
    : (∂ λ (z : Z) => ∫ x, F z x) = λ z dz => ∫ x, ∂ F z dz x := sorry

  #check λ f : X⟿Y => ∫ f
  #check λ f : X⟿Y => ∫ λ x => f x

  example : IsLin λ (f : X⟿Y) => ∫ f := by infer_instance
  example : IsLin λ (f : X⟿Y) => ∫ x, f x := by infer_instance
  example : IsLin λ (f : X⟿Y) => ∫ x, (2 : ℝ) * f x := by infer_instance
  example : IsSmooth λ (f : X⟿Y) => ∫ x, f x := by infer_instance
  example : IsSmooth λ (f : X⟿Y) => ∫ x, (2 : ℝ) * f x := by infer_instance
  example : (∂ λ (f : X⟿Y) => ∫ x, f x) = (λ _ df : X⟿Y => ∫ x, df x) := by simp

  example (u : X) : IsSmooth λ (f : X⟿Y) (x : X) => ∂ f.1 x u := by infer_instance
  example (u : X) : IsSmooth (λ (f : X⟿Y) => ∫ x, ∂ f.1 x u) := by infer_instance
  example (u : X) : (∂ λ (f : X⟿Y) => ∫ x, ∂ f.1 x u) = λ _ df : X⟿Y => ∫ x, ∂ df.1 x u := by simp

  example [Hilbert Y] : IsSmooth λ (f : X⟿Y) (x : X) => ∂† f.1 x := sorry
  -- example (u : X) : IsSmooth λ (f : X⟿ℝ) (x : X) => ∂⁻¹ f.1 x := by infer_instance


  #check λ (f : X⟿ℝ) => ∇ f.1
  example : (∂ λ (f : X⟿ℝ) => ∫ x, ∥∂† f.1 x 1∥²) = λ (f df : X⟿ℝ) => ∫ x, (2:ℝ)*⟪∇ df.1 x, ∇ f.1 x⟫ := sorry
  example : (∂ λ (f : X⟿ℝ) => ∫ x, ∥∇ f.1 x∥²) = λ (f df : X⟿ℝ) => ∫ x, (2:ℝ)*⟪∇ df.1 x, ∇ f.1 x⟫ := sorry
  -- example : (δ λ (f : X⟿ℝ) => ∫ x, ∥∇ f.1 x∥²) = λ (f : X⟿ℝ) => 2 * f := by simp

  -- example (L : X → X → ℝ) [IsSmooth L] [∀ x, IsSmooth (L x)] 
  --   : ∂ (λ (x : ℝ ⟿ X) => ∫ t, L (x t) (∂ x.1 t 1)) 
  --     = 
  --     λ x dx => ∫ t, ∂ L (x t) (dx t) (∂ x.1 t 1) + 
  --                    ∂ (L (x t)) (∂ x.1 t 1) (∂ dx.1 t 1) := sorry

  -- ∫ t ∈ ∂ Ω, 
  class PartialDifferential (α : Type) (β : outParam Type) where
    partialDifferential : α → β

  class AdjointPartialDifferential (α : Type) (β : outParam Type) where
    adjointPartialDifferential : α → β

  class Nabla (α : Type) (β : outParam Type) where
    nabla : α → β

  prefix:max (priority:=high) "∂" => PartialDifferential.partialDifferential
  prefix:max (priority:=high) "∇" => Nabla.nabla

  export PartialDifferential (partialDifferential)
  attribute [reducible] partialDifferential

  @[reducible]
  noncomputable
  instance {X Y} [Vec X] [Vec Y] : PartialDifferential (X → Y) (X → X → Y) where
    partialDifferential f := differential f

  @[reducible]
  noncomputable
  instance {X Y} [SemiHilbert X] [SemiHilbert Y] : AdjointPartialDifferential (X → Y) (X → Y → X) where
    adjointPartialDifferential f := adjDiff f

  @[reducible]
  noncomputable
  instance {X} [SemiHilbert X] : Nabla (X → ℝ) (X → X) where
    nabla f x := adjDiff f x (1 : ℝ)

  instance LinMap.mk.arg_x.isSmooth {X Y Z} [Vec X] [Vec Y] [Vec Z] 
    (f : X → Y → Z) [IsSmooth f] [∀ x, IsLin (f x)]
    : IsSmooth λ x => LinMap.mk (f x) := by infer_instance

  @[reducible]
  noncomputable
  instance {X Y} [Vec X] [Vec Y] : PartialDifferential (X ⟿ Y) (X ⟿ (X ⊸ Y)) where
    partialDifferential f := λ x ⟿ λ dx ⊸ differential f.1 x dx

    -- partialDifferential f := ⟨λ x => ⟨λ dx => partialDifferential f.1 x dx, by simp[partialDifferential]; infer_instance⟩, by simp[partialDifferential]; infer_instance⟩

  variable (X Y Z) [Vec X] [Vec Y] [Vec Z] (f : Y ⟿ Z) (g : X ⟿ Y) (h : X → Y → Z)

  #check ∂ (Function.uncurry λ x y => h x y)

  #check λ x ⟿ ∂ f x    
  #check λ x dx ⟿ ∂ f x dx
  #check λ x ⟿ λ dx ⊸ ∂ f x dx

  #check AutoImpl.val
  #check ((∂ λ x => f (g x)) rewrite_by simp)
  set_option trace.Meta.Tactic.simp.discharge true in
  #check ((∂ (λ x ⟿ f (g x))) rewrite_by (simp[partialDifferential]))

  @[reducible]
  noncomputable
  instance {X Y} [SemiHilbert X] [SemiHilbert Y] : AdjointPartialDifferential {f : X → Y // HasAdjDiff f} (X ⟿ Y ⊸ X) where
    adjointPartialDifferential f := ⟨λ x => ⟨λ df' => adjDiff f x df', sorry⟩, sorry⟩

  @[reducible]
  noncomputable
  instance {X} [SemiHilbert X] : Nabla {f : X → ℝ // HasAdjDiff f} (X ⟿ ℝ) where
    nabla f := ⟨λ x => ⟨λ df' => adjDiff f x df', sorry⟩, sorry⟩

  -- Set boundary
  noncomputable
  instance {X Y} [Vec X] [Vec Y] : PartialDifferential (Set X) (Set X) where
    partialDifferential Ω := sorry


  variable (f : X → Y) (g : X ⟿ Y) (Ω : Set X)

  #check partialDifferential f
  #check λ x dx => partialDifferential g x dx
  #check partialDifferential Ω

  example (L : X → X → ℝ) [IsSmooth L] [∀ x, IsSmooth (L x)] 
    : δ (λ (x : ℝ ⟿ X) => ∫ t, L (x t) (∂ x.1 t 1)) 
      = 
      λ (x : ℝ ⟿ X) => λ (t : ℝ) => 
        ∂† L (x t) 1 (∂ x.1 t 1) + 
        ∂ (λ s : ℝ => ∂† (L (x s)) (∂ x.1 t 1) 1) 1 := sorry

  -- x /! y
  -- x / y
  -- function_properties integral {Fun Dom Result : Type} [Integral Fun Dom Result] (f : Fun) (Ω : Dom) : Result
  -- argument f [Vec Fun] [Vec Result]
  --   isLin := sorry,
  --   isSmooth, diff

  def varGrad [Integral Fun Dom Result] (F : Fun → Dom → Result) : Fun → Result → Fun := sorry

  class HasVarDual [Integral Fun Dom Result] (f : Fun → Dom → Result) where
    has_var_dual : ∃ f' : Fun, 
                 
  def varDual [Integral Fun Dom Result] (F : Fun → Dom → Result) : Fun := sorry
  theorem
  
  example {n : Nat} {Dom : Type} [Integral (ℝ^{n} → ℝ) Dom ℝ] 
    : (varGrad λ (f : ℝ^{n} → ℝ) => integral λ x => ∥f x∥²) 
      = 
      λ (f : ℝ^{n} → ℝ) (df' : ℝ) (x : ℝ^{n}) => 2 * df' * f x := sorry

  @[simp]
  theorem asdf [SemiHilbert Fun₁] [SemiHilbert Fun₂] (F : Fun₁ → Fun₂) : (varGrad λ (f : Fun₁) : Fun => integral F f) = λ 

  #check SmoothMap
  
  example {X Y} [Vec X] [Vec Y] : (λ (f : X ⟿ Y) => ∂ f.1) = λ f df => ∂ df.1 := by simp
