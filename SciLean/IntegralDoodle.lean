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

  noncomputable 
  def indicatorFunction {α} (Ω : α → Prop) (a : α) : ℝ :=
    match Classical.propDecidable (Ω a) with
      | isTrue  _ => 1
      | isFalse _ => 0

  -- prefix:max "𝟙" => indicatorFunction

  variable {ι} [Enumtype ι]

  def IsOpen {X} [FinVec X ι] (Ω : Set X) : Prop := sorry
  def IsBounded {X} [FinVec X ι] (Ω : Set X) : Prop := sorry

  def IntDom (X : Type) [FinVec X ι] : Type := {Ω : Set X // IsOpen Ω}

  -- TODO: LocIntDom should form an Abelian group, so we can write
  --   1. ∫ x ∈ [1,-1], f x         -- usefull for the differentiation under the integral sign
  --   1. ∫ x ∈ 3*Ω₁ - Ω₂, f x      -- usefull for working with chains and cochains
  -- def LocIntDom (X : Type) [FinVec X ι] : Type := {Ω : Set X // IsOpen Ω ∧ IsBounded Ω}

  inductive LocIntDom.Repr(X : Type) [FinVec X ι] where
  | set (Ω : Set X) : IsOpen Ω → IsBounded Ω → LocIntDom.Repr X
  | sum (Ω₁ Ω₂ : LocIntDom.Repr X) : LocIntDom.Repr X
  | smul (s : ℝ) (Ω : LocIntDom.Repr X) : LocIntDom.Repr X

  noncomputable
  def LocIntDom.Repr.indicatorFun {X} [FinVec X ι] (Ω : LocIntDom.Repr X) : X → ℝ := 
  match Ω with
  | set Ω' _ _ => indicatorFunction Ω'
  | sum Ω₁ Ω₂  => Ω₁.indicatorFun + Ω₂.indicatorFun
  | smul s Ω   => s * Ω.indicatorFun

  def LocIntDom.Repr.Eq {X} [FinVec X ι] (Ω₁ Ω₂ : LocIntDom.Repr X) : Prop :=
    (Ω₁.indicatorFun = Ω₂.indicatorFun)

  def LocIntDom (X : Type) [FinVec X ι] : Type := Quot (LocIntDom.Repr.Eq (X:=X))

  instance {X} [FinVec X ι] : Add (LocIntDom X) := 
    ⟨(λ Ω₁ => (λ Ω₂ => Quot.mk _ (.sum Ω₁ Ω₂)) |> (Quot.lift · sorry)) |> (Quot.lift · sorry)⟩
 
  instance {X} [FinVec X ι] : HMul ℝ (LocIntDom X) (LocIntDom X) := 
    ⟨λ s => (λ Ω => Quot.mk _ (.smul s Ω)) |> (Quot.lift · sorry)⟩

  -- Empty set
  instance {X} [FinVec X ι] : Zero (LocIntDom X) := 
    ⟨Quot.mk _ (.set (λ _ => False) sorry sorry)⟩
 

  -- Probably Riemann integrability on domain Ω
  class IsIntegrable [FinVec X ι] [Vec Y] (f : X → Y) (Ω : IntDom X) : Prop
  class IsLocIntegrable [FinVec X ι] [Vec Y] (f : X → Y) : Prop where
    is_loc_integrable : ∀ Ω : LocIntDom X, IsIntegrable f sorry -- ⟨Ω.1, Ω.2.1⟩

  -- If `f` is integrable on `Ω` return integral otherwise return zero
  -- IMPORTANT: We choose to integrate only over **bounded** domains.
  --            This way the function `λ (f : X⟿Y) => ∫ x, f x` can be linear.
  -- QUESTION: Do we need Y to be complete? For example smooth function
  --   with compact support do not form closed subspace in `ℝ ⟿ ℝ`. 
  --   Can we have `γ : ℝ ⟿ {f : ℝ ⟿ ℝ // TestFun f}` such that 
  --   `∫ t ∈ [0,1], γ.1` is not a `TestFun`?
  def integral {X Y : Type} [FinVec X ι] [Vec Y] (f : X → Y) (Ω : LocIntDom X) : Y := sorry

  class Integral (Fun : Type) (R : outParam Type) where
    integral : Fun → R

  attribute [reducible] Integral.integral

  @[reducible, defaultInstance, inferTCGoalsRL]
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

  --  The paper 'I♥LA: compilable markdown for linear algebra' https://doi.org/10.1145/3478513.3480506
  --  claims on page 5 that conservative sum is more common then greedy
  --  We addopt this for integral too, hence the priority `fx:term:66`

  macro "∫" f:term:66 : term => `(Integral.integral $f)
  macro "∫" x:Lean.Parser.Term.funBinder "," fx:term:66 : term => `(∫ λ $x => $fx)
  -- ∫ (x,y), f x y  -- does not work :(
  
  -- We should probably require for `R` to be of the form `... → ℝ`
  -- Otherwise it does not make sense
  -- Unfortunatelly I do not know how to nest integrals :( 
  -- class HasVarDual {Fun R} [SemiHilbert Fun] [One Fun] [Integral Fun R] (F : Fun → R) : Prop where
  --   hasVarDual : ∃ A : Fun → Fun, HasAdjoint A ∧ (∀ f, F f = ∫ (A f))
    -- There is something magical about the type `R` that ensures uniqueness of A
    -- Ohh yeah `R` is really big ... 
    --   for example for `Fun = ℝ^{n}` the `R` would be `(Fin n → Bool) → ℝ` 
    --   i.e. we have to provide `Fin n → Bool` to specify over which indices to sum over
    --   the `(Fin n → Bool) → ℝ` is waaay bigger then `ℝ^{n}`

  class FullIntegral (Fun : Type) (R : outParam Type) where
    integral : Fun → R           -- R plays a bit similar role of ℝ

  instance {X ι} [Enumtype ι] [FinVec X ι] : FullIntegral (X ⟿ ℝ) (LocIntDom X → ℝ) where
    integral f := ∫ f

  instance {X ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] [FullIntegral Y R] [Vec R]
    : FullIntegral (X ⟿ Y) (LocIntDom X → R) where
    integral f := ∫ x, FullIntegral.integral (f x)

  def HasVarDual {Fun R} [SemiHilbert Fun] [FullIntegral Fun R] (F : Fun → R) : Prop :=
    ∃ A : Fun → Fun, HasAdjoint A ∧ (∀ f, F f = FullIntegral.integral (A f))

  noncomputable
  def varDual {Fun R} [SemiHilbert Fun] [One Fun] [FullIntegral Fun R] (F : Fun → R) : Fun :=
    match Classical.propDecidable (HasVarDual F) with
    | isTrue h =>
      let A := Classical.choose h
      A† 1
    | isFalse _ => 0

  #check Vec 

  -- This should be immediate from the definition
  @[simp]
  theorem varDual_smooth_fun {X Y ι} [Enumtype ι] [FinVec X ι] [Hilbert Y]
    (F : (X ⟿ ℝ) → (X ⟿ ℝ)) [HasAdjoint F]
    : varDual (λ f => ∫ F f) = F† 1 := sorry


  -- instance {X ι} [Enumtype ι] [FinVec X ι] : VarDual (X ⟿ ℝ) (LocIntDom X → ℝ) where
  --   -- hasVarDual F := ∃ A : (X ⟿ ℝ) → (X ⟿ ℝ), HasAdjoint A ∧ (∀ f, F f = ∫ (A f))
  --   integral f := ∫ f
  --   varDual := sorry

  -- instance {X ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] [VarDual Y R] : VarDual (X ⟿ Y) (LocIntDom X → R) where
  --   hasVarDual F := ∃ A : (X ⟿ Y) → (X ⟿ Y), HasAdjoint A ∧ (∀ f, F f = ∫ (A f))
  --   varDual := sorry


  -- instance VarDual (X → ℝ) (LocIntDom X → ℝ) where
  --   varDual := sorry


  -- noncomputable 
  -- def varDual {Fun R} [SemiHilbert Fun] [One Fun] [Integral Fun R] (F : Fun → R) : Fun := 
  --   match Classical.propDecidable (HasVarDual F) with
  --   | isTrue h => 
  --     let A := Classical.choose h.hasVarDual
  --     A† 1
  --   | isFalse _ => 0
  
  variable {X Y Z} [FinVec X ι] [Vec Y] [Vec Z]

  #check varDual λ (f : X ⟿ ℝ) => ∫ x, f x
  #check_failure varDual λ (f : X ⟿ X ⟿ ℝ) => ∫ x, f x  -- this should not typecheck fail
  #check varDual λ (f : X ⟿ X ⟿ ℝ) => ∫ x, ∫ y, f x y -- this shoud typecheck

  -- instance SmoothMap.val.arg_f.isLin : IsLin (λ f : X⟿Y => f.1) := by infer_instance
  -- instance SmoothMap.val.arg_f.isSmooth : IsSmooth (λ f : X⟿Y => f.1) := by infer_instance

  -- We can't prove linearity of differential directly
  -- instance (F : (X⟿Y) → (X → Y)) [IsLin F] [∀ f, IsSmooth (F f)] 
  --   : IsLin λ (f : X⟿Y) => ∂ (F f) := by infer_instance
  -- instance (F : (X⟿Y) → (X → Y)) [IsSmooth F] [∀ f, IsSmooth (F f)] 
  --   : IsSmooth λ (f : X⟿Y) => ∂ (F f) := by infer_instance

  instance (F : Z → X → Y) [IsLin F] [∀ f, IsSmooth (F f)] 
    : IsLin λ (z : Z) => ∫ x, F z x := sorry
  instance (F : Z → X → Y) [IsSmooth F] [∀ f, IsSmooth (F f)] 
    : IsSmooth λ (z : Z) => ∫ x, F z x := sorry

  -- IMPORTANT: This is true only when we integrate over bounded domains!
  --            Double check this is really true
  @[simp]
  theorem diff_integral (F : Z → X → Y) [IsSmooth F] [∀ f, IsSmooth (F f)] 
    : ∂ (λ z => ∫ x, F z x) = λ z dz => ∫ x, ∂ F z dz x := sorry

  -- instance (f : X → Y → Z) [IsSmooth F] [∀ f, IsSmooth (F f)] 
  --   (g : X → Y) [IsSmooth
  --   : IsSmooth λ (z : Z) => ∫ x, F z x := sorry
  example : IsSmooth fun (f : X ⟿ Y) x => (2 : ℝ) * f x := by infer_instance

  example : IsSmooth λ f : ℝ⟿ℝ => λ x => differential f.1 x 1 := by infer_instance

  instance diff.arg_x.comp.isSmooth' {X Y Z} [Vec X] [Vec Y] [Vec Z] [Vec W]
    (f : Y → Z → W) [IsSmooth f] [∀ y, IsSmooth (f y)] 
    (g : X → Y) [IsSmooth g]
    : IsSmooth (λ x => ∂ (f (g x))) := sorry

  example (f : ℝ⟿ℝ) : IsSmooth λ x => ∂ f x 1 := by infer_instance
  
  instance : IsSmooth fun (f : ℝ⟿ℝ) => ∂ f := sorry
  
  -- set_option trace.Meta.synthInstance true in
  -- TODO: Simplify
  instance {X Y} [Vec X] [Vec Y] : IsSmooth fun (f : X⟿Y) x dx  => ∂ f x dx := sorry
  instance {X Y} [Vec X] [Vec Y] (x : X) : IsSmooth fun (f : X⟿Y) => ∂ f x := sorry
  instance {X Y} [Vec X] [Vec Y] (x dx : X) : IsSmooth fun (f : X⟿Y) => (∂ f) x dx := sorry
  instance {X Y} [Vec X] [Vec Y] : IsLin fun (f : X⟿Y) x dx  => ∂ f x dx := sorry
  instance {X Y} [Vec X] [Vec Y] (x : X) : IsLin fun (f : X⟿Y) => ∂ f x := sorry
  instance {X Y} [Vec X] [Vec Y] (x dx : X) : IsLin fun (f : X⟿Y) => (∂ f) x dx := sorry
  instance {X Y} [SemiHilbert X] [SemiHilbert Y] : IsSmooth fun (f : X⟿Y) x dy  => ∂† f.1 x dy := sorry
  instance {X Y} [SemiHilbert X] [SemiHilbert Y] (x : X) : IsSmooth fun (f : X⟿Y) => ∂† f.1 x := sorry
  instance {X Y} [SemiHilbert X] [SemiHilbert Y] (x : X) (dy : Y) : IsSmooth fun (f : X⟿Y) => (∂† f.1) x dy := sorry

  instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) [HasAdjDiff f] : IsSmooth fun x dy => ∂† f x dy := sorry
  instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) [HasAdjDiff f] (x : X) : IsSmooth fun dy => ∂† f x dy := sorry
  instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) [HasAdjDiff f] (x : X) : IsLin fun dy => ∂† f x dy := sorry

  example (Ω : LocIntDom ℝ) : IsSmooth λ (f : ℝ ⟿ ℝ) => (∫ x, f x) Ω := by infer_instance

  set_option synthInstance.maxSize 2048 in
  example : ∀ (Ω : LocIntDom ℝ), IsSmooth λ (f : ℝ ⟿ ℝ) => (∫ x, ∥∂ f x 1∥²) Ω := by infer_instance
  example: IsSmooth fun (f : ℝ ⟿ ℝ) => (fun x => ∥Subtype.val (Subtype.val (∂f) x ) 1∥²) := by infer_instance
  example (i : LocIntDom ℝ) : IsSmooth fun (f : ℝ ⟿ ℝ) => Integral.integral (fun x => ∥Subtype.val (Subtype.val (∂f) x ) 1∥²) i := by infer_instance
  set_option synthInstance.maxSize 2048 in
  example : ∀ (i : LocIntDom ℝ), IsSmooth fun (f : ℝ ⟿ ℝ) => Integral.integral (fun x => ∥Subtype.val (Subtype.val (∂f) x ) 1∥²) i := by infer_instance

  variable (f  : X⟿ℝ) (g : X→ℝ)
  #check Integral.integral f

  #check ∫ x, f x
  #check ∫ x, g x
  
  example : ∂ (λ f : X⟿ℝ => ∫ x, f x) = λ (f df : X⟿ℝ) => ∫ x, df x := by simp
  example : ∂ (λ f : X⟿ℝ => ∫ x, ∥f x∥²) = λ (f df : X⟿ℝ) => ∫ x, 2 * df x * f x := by simp

  -- set_option trace.Meta.Tactic.simp.discharge true in
  example : ∂ (λ f : ℝ⟿ℝ => ∫ x, ∂ f x 1) = λ (f df : ℝ⟿ℝ) => ∫ x, ∂ df x 1 := by simp; done
  set_option synthInstance.maxSize 2048 in
  example : ∂ (λ f : ℝ⟿ℝ => ∫ x, ∥∂ f x 1∥²) = λ (f df : ℝ⟿ℝ) => ∫ x, 2 *  ∂ df x 1 * ∂ f x 1 := by simp; done

  -- class HasVarDual {Y} [Hilbert Y] (F : (X ⟿ Y) → LocIntDom X → ℝ) where
  --   has_var_dual : ∃ (f : X ⟿ Y), ∀ (g : X ⟿ Y), F g = ∫ x, ⟪f x, g x⟫ -- maybe g true only for domains Ω on which g is a test function

  -- -- Defined only if it has variational dual otherwise zero function
  -- def varDual : ((X ⟿ Y) → LocIntDom X → ℝ) → (X ⟿ Y) := sorry

      

  -- instance {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] : VarDual (X ⟿ Y) (LocIntDom X → ℝ) where
  --   varDual := varDual

  -- instance hoho {X Y R} [FinVec X ι] [SemiHilbert Y] [VarDual Y R] : VarDual (X ⟿ Y) (LocIntDom X → R) where
  --   varDual := sorry

  -- example : VarDual (ℤ → ℝ) (LocIntDom ℤ → ℝ) := by infer_instance
  -- example : VarDual (X ⟿ ℤ → ℝ) (LocIntDom X → LocIntDom ℤ → ℝ) := by infer_instance
  -- example : VarDual (ℤ → X ⟿ ℝ) (LocIntDom ℤ → LocIntDom X → ℝ) := by infer_instance

  -- example {Y Z} [FinVec Y ι] [SemiHilbert Z] : VarDual (Y ⟿ Z) (LocIntDom Y → ℝ) := by infer_instance
  -- example {X Y Z} [FinVec X ι] [FinVec Y ι] [SemiHilbert Z] : VarDual (X ⟿ Y ⟿ Z) (LocIntDom X → LocIntDom Y → ℝ) := by infer_instance
  -- example {X Y Z} [FinVec X ι] [FinVec Y ι] [SemiHilbert Z] : VarDual (X×Y ⟿ Z) (LocIntDom (X × Y) → ℝ) := by infer_instance


  @[simp]
  theorem varDual_fun {Y} [Hilbert Y] (F : (X ⟿ Y) → (X ⟿ ℝ)) [HasAdjoint F] 
    : varDual (λ f : X ⟿ Y => ∫ x, F f x) = F† (λ _ ⟿ 1) := by simp

  -- @[simp]
  -- theorem integral_normalize_to_smooth (f : X → Y) [IsSmooth f]
  --   : (∫ x, f x) = ∫ x, (λ x' ⟿ f x') x := sorry

  instance pointwise_has_adjoint {Y Z} [Hilbert Y] [Hilbert Z] (A : X → Y → Z) [∀ x, HasAdjoint (A x)] [IsSmooth A] [∀ x, IsSmooth (A x)]
    : HasAdjoint (λ f : X ⟿ Y => λ x ⟿ A x (f x)) := sorry

  instance pointwise_has_adjoint' {Y Z} [Hilbert Y] [Hilbert Z] (A : Y → X → Z) [∀ x, HasAdjoint (λ y => A y x)] [IsSmooth A] [∀ y, IsSmooth (A y)]
    : HasAdjoint (λ f : X ⟿ Y => λ x ⟿ A (f x) x) := sorry

  -- instance comp_adjoint {A B C} [Hilbert A] [Hilbert B] [Hilbert C] 
  --   (F : (X → B) → X → (X → C)) [∀ (f : X -> B) y, IsSmooth (λ x => F f y x)] --[HasAdjoint (λ f : X ⟿ B => λ x ⟿ F f.1 x)] [IsSmooth λ f : X->B => F f]
  --   (G : (X → A) → X → (X → B)) [∀ (f : X -> A) y, IsSmooth (λ x => G f y x)] --[HasAdjoint (λ f : X ⟿ A => λ x ⟿ G f.1 x)] [IsSmooth λ f : X->A => G f]
  --   : HasAdjoint (λ f : X ⟿ A => λ x ⟿ F (G f.1 x) x x) := sorry

  example {Y} [Hilbert Y] (c : ℝ)
    : HasAdjoint (λ f : X ⟿ Y => λ x ⟿ c * f x) := by infer_instance

  def smoothEval {X Y} [Vec X] [Vec Y] (x : X) (f : X ⟿ Y) : Y  := f x

  theorem smooth_eval {X Y} [Vec X] [Vec Y] (x : X) (f : X ⟿ Y)
    : Subtype.val f x = smoothEval x f := by simp[smoothEval]

  -- @[simp]
  -- theorem hihih {A B C} [Hilbert A] [Hilbert B] [Hilbert C] 
  --   (G : X → (X → A) → (X → B)) [∀ f, IsSmooth (G f)]
  --   (F : X → (X → B) → (X → C)) [∀ f, IsSmooth (F f)]
  --   [∀ f, IsSmooth (λ x => F x (G x f) x)]
  --   [∀ f, IsSmooth (λ x => F x f x)]
  --   [∀ f, IsSmooth (λ x => G x f x)]
  --   : (λ f : X ⟿ A => λ x ⟿ F x (G x f) x) 
  --     = 
  --     (λ f : X ⟿ B => λ x ⟿ F x f x) ∘ (λ f : X ⟿ A => λ x ⟿ G x f x)
  --   := by funext f; ext x; simp[Compose.compose]; done

  example : HasAdjoint (λ f : ℝ ⟿ ℝ => λ x ⟿ x * f x) := by infer_instance
  example : HasAdjoint (λ f : ℝ ⟿ ℝ => λ x ⟿ f x * x) := by infer_instance

  @[simp]
  theorem smooth_mul_norm {X} [Vec X] (f g : X → ℝ) [IsSmooth f] [IsSmooth g]
    : (λ x ⟿ f x * g x) = (λ x ⟿ f x) * (λ x ⟿ g x) := by ext x; simp[HMul.hMul, Mul.mul]

  @[simp]
  theorem smooth_smul_norm_v1 {X} [Vec X] (f : X → Y) [IsSmooth f] (c : ℝ)
    : (λ x ⟿ c * f x) = c * (λ x ⟿ f x) := by ext x; simp[HMul.hMul, Mul.mul]

  theorem smooth_smul_norm_v1_id {X} [Vec X] (c : ℝ)
    : (λ (x : X) ⟿ c * x) = c * (λ (x : X) ⟿ x) := by ext x; simp[HMul.hMul, Mul.mul]

  @[simp]
  theorem pointwise_smul_smooth_map {X Y} [Vec X] [Vec Y] (f : X ⟿ Y) (c : ℝ) (x : X)
    : (c * f) x = c * f x := by simp only [HMul.hMul, Mul.mul]

  -- instance {X Y} [Vec X] [Vec Y] : HMul (X ⟿ ℝ) (X ⟿ Y) (X ⟿ Y) := ⟨λ f g => λ x ⟿ f x * g x⟩

  instance {W X Y Z} [Vec W] [Vec X] [Vec Y] [Vec Z] 
    [HMul X Y Z] [IsSmooth λ (x : X) (y : Y) => x * y] [∀ x : X, IsSmooth (λ (y : Y) => x * y)]
    : HMul (W ⟿ X) (W ⟿ Y) (W ⟿ Z) := ⟨λ f g => λ x ⟿ f x * g x⟩

  @[simp]
  theorem pointwise_mul_smooth_map {W X Y Z} [Vec W] [Vec X] [Vec Y] [Vec Z] 
    [HMul X Y Z] [IsSmooth λ (x : X) (y : Y) => x * y] [∀ x : X, IsSmooth (λ (y : Y) => x * y)]
    (f : W ⟿ X) (g : W ⟿ Y) (w : W)
    : (f * g) w = f w * g w := by simp[HMul.hMul, Mul.mul]; done

  @[simp]
  theorem pointwise_add_smooth_map {X Y} [Vec X] [Vec Y]
    (f g : X ⟿ Y) (x : X)
    : (f + g) x = f x + g x := by simp[HAdd.hAdd, Add.add]; done

  instance {W X Y Z} [Vec W] [Vec X] [Vec Y] [Vec Z] 
    [HMul X Y Z] [IsSmooth λ (x : X) (y : Y) => x * y] [∀ x : X, IsSmooth (λ (y : Y) => x * y)]
    : IsSmooth (λ (f : W ⟿ X) (g : W ⟿ Y) => f * g) := by simp[HMul.hMul, Mul.mul]; infer_instance; done

  instance {W X Y Z} [Vec W] [Vec X] [Vec Y] [Vec Z] 
    [HMul X Y Z] [IsSmooth λ (x : X) (y : Y) => x * y] [∀ x : X, IsSmooth (λ (y : Y) => x * y)]
    (f : W ⟿ X) 
    : IsSmooth (λ (g : W ⟿ Y) => f * g) := by simp[HMul.hMul, Mul.mul]; infer_instance; done

  -- theorem smooth_smul_norm_v2 (y : Y)
  --   : (λ (x : ℝ) ⟿ x * y) = (λ (x : ℝ) ⟿ x) * (λ (_ : ℝ) ⟿ y) := by ext x; simp[HMul.hMul, Mul.mul]

  theorem smooth_hmul_norm {W X Y Z} [Vec W] [Vec X] [Vec Y] [Vec Z] 
    [HMul X Y Z] [IsSmooth λ (x : X) (y : Y) => x * y] [∀ x : X, IsSmooth (λ (y : Y) => x * y)]
    (f : W → X) [IsSmooth f]
    (g : W → Y) [IsSmooth g]
    : (λ (w : W) ⟿ f w * g w) = (λ (w : W) ⟿ f w) * (λ (w : W) ⟿ g w) := by ext x; simp[HMul.hMul, Mul.mul]

  @[simp]
  theorem smooth_comp {X} [Vec X] (f : Y → Z) [IsSmooth f] (g : X → Y) [IsSmooth g]
    : (λ x ⟿ f (g x)) = (λ y ⟿ f y) ∘ (λ x ⟿ g x) := by ext x; simp[Compose.compose]

  -- def Smooth.scomb {X} [Vec X] (f : X ⟿ Y ⟿ Z) (g : X ⟿ Y) : X ⟿ Z := λ x ⟿ f x (g x)

  -- @[simp]
  -- theorem smooth_scomb {X} [Vec X] (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)] (g : X → Y) [IsSmooth g]
  --   : (λ x ⟿ f x (g x)) = Smooth.scomb (λ x y ⟿ f x y) (λ x ⟿ g x) := by ext x; simp[Smooth.scomb]

  def Smooth.comp {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : Y ⟿ Z) (g : X ⟿ Y) := λ x ⟿ f (g x)

  def smooth_mor_comp {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : Y → Z) [IsSmooth f] (g : X → Y) [IsSmooth g]
    : (λ x ⟿ f (g x)) = Smooth.comp (λ y ⟿ f y) (λ x ⟿ g x) := by simp[Smooth.comp]

  def Smooth.diag {X Y₁ Y₂} [Vec X] [Vec Y₁] [Vec Y₂] (f : Y₁ ⟿ Y₂ ⟿ Z) (g₁ : X ⟿ Y₁) (g₂ : X ⟿ Y₂) : X ⟿ Z := λ x ⟿ f (g₁ x) (g₂ x)

  instance {X Y₁ Y₂} [Vec X] [Vec Y₁] [Vec Y₂]
    : IsSmooth λ (f : Y₁ ⟿ Y₂ ⟿ Z) (g₁ : X ⟿ Y₁) (g₂ : X ⟿ Y₂) => Smooth.diag f g₁ g₂ := sorry

  instance {X Y₁ Y₂} [Vec X] [Vec Y₁] [Vec Y₂] (f : Y₁ ⟿ Y₂ ⟿ Z)
    : IsSmooth λ (g₁ : X ⟿ Y₁) (g₂ : X ⟿ Y₂) => Smooth.diag f g₁ g₂ := sorry

  instance {X Y₁ Y₂} [Vec X] [Vec Y₁] [Vec Y₂] (f : Y₁ ⟿ Y₂ ⟿ Z) (g₁ : X ⟿ Y₁)
    : IsSmooth λ (g₂ : X ⟿ Y₂) => Smooth.diag f g₁ g₂ := sorry

  @[simp]
  theorem smooth_diag {X Y₁ Y₂} [Vec X] [Vec Y₁] [Vec Y₂] 
    (f : Y₁ → Y₂ → Z)  [IsSmooth f] [∀ y₁, IsSmooth (f y₁)]
    (g₁ : X → Y₁) [IsSmooth g₁]
    (g₂ : X → Y₂) [IsSmooth g₂]
    : (λ x ⟿ f (g₁ x) (g₂ x)) = Smooth.diag (λ y₁ y₂ ⟿ f y₁ y₂) (λ x ⟿ g₁ x) (λ x ⟿ g₂ x) := by simp[Smooth.diag]

  -- this is causing some issues
  -- @[simp mid-1]
  theorem smooth_diag_parm1 {X Y₁ Y₂} [Vec X] [Vec Y₁] [Vec Y₂] (a : α)
    (f : Y₁ → Y₂ → α → Z)  [IsSmooth λ y₁ y₂ => f y₁ y₂ a] [∀ y₁, IsSmooth (λ y₂ => f y₁ y₂ a)]
    (g₁ : X → Y₁) [IsSmooth g₁]
    (g₂ : X → Y₂) [IsSmooth g₂]
    : (λ x ⟿ f (g₁ x) (g₂ x) a) = Smooth.diag (λ y₁ y₂ ⟿ f y₁ y₂ a) (λ x ⟿ g₁ x) (λ x ⟿ g₂ x) := by simp[Smooth.diag]

  -- @[simp mid-1]
  theorem smooth_diag_inner {X Y} [Vec X] [Hilbert Y]
    (g₁ : X → Y) [IsSmooth g₁]
    (g₂ : X → Y) [IsSmooth g₂]
    : (λ x ⟿ ⟪g₁ x, g₂ x⟫) = Smooth.diag (λ y₁ y₂ ⟿ ⟪y₁, y₂⟫) (λ x ⟿ g₁ x) (λ x ⟿ g₂ x) := by simp[Smooth.diag]

  /- point wise inner product -/
  def Smooth.pw_inner {X Y ι} [Enumtype ι] [FinVec X ι] [Hilbert Y] (f g : X ⟿ Y) : X ⟿ ℝ := λ x ⟿ ⟪f x, g x⟫
  argument f
    isLin := sorry,
    isSmooth, diff_simp,
    hasAdjoint := sorry,
    adj_simp := f' * g by sorry,
    hasAdjDiff := by constructor; infer_instance; simp; infer_instance,
    adjDiff_simp 
  argument g
    isLin := sorry,
    isSmooth, diff_simp,
    hasAdjoint := sorry,
    adj_simp := g' * f by sorry,
    hasAdjDiff := by constructor; infer_instance; simp; infer_instance,
    adjDiff_simp 

  @[simp]
  theorem smooth_diag_pw_inner {Y} [Hilbert Y]
    (g₁ : X → Y) [IsSmooth g₁]
    (g₂ : X → Y) [IsSmooth g₂]
    : (λ x ⟿ ⟪g₁ x, g₂ x⟫) = Smooth.pw_inner (λ x ⟿ g₁ x) (λ x ⟿ g₂ x) := by simp[Smooth.pw_inner]

  @[simp]
  theorem smooth_diag_pw_inner_alt {Y} [Hilbert Y]
    (g₁ : X → Y) [IsSmooth g₁]
    (g₂ : X → Y) [IsSmooth g₂]
    : (λ x => ⟪g₁ x, g₂ x⟫) = (Smooth.pw_inner (λ x ⟿ g₁ x) (λ x ⟿ g₂ x)).1 := by unfold Smooth.pw_inner; simp

  @[simp]
  theorem smooth_diag_eval {X Y₁ Y₂} [Vec X] [Vec Y₁] [Vec Y₂] 
    (f : Y₁ ⟿ Y₂ ⟿ Z) (g₁ : X ⟿ Y₁) (g₂ : X ⟿ Y₂) (x : X)
    : (Smooth.diag f g₁ g₂ x) = f (g₁ x) (g₂ x) := by unfold Smooth.diag; simp

  @[simp]
  theorem smooth_diag_hmul  {W X Y Z} [Vec W] [Vec X] [Vec Y] [Vec Z]
    [HMul X Y Z] [IsSmooth λ (x : X) (y : Y) => x * y] [∀ x : X, IsSmooth (λ (y : Y) => x * y)]
    (f : W ⟿ X) (g : W ⟿ Y)
    : Smooth.diag (λ (x : X) (y : Y) ⟿ x * y) f g = f * g := by ext x; simp[Smooth.diag, HMul.hMul, Mul.mul]; done

  @[simp]
  theorem smooth_diag_add  {X Y} [Vec X] [Vec Y] (f g : X ⟿ Y)
    : Smooth.diag (λ (x y : Y) ⟿ x + y) f g = f + g := by ext x; simp[Smooth.diag, HAdd.hAdd, Add.add]; done

  def Smooth.id {X} [Vec X] := λ (x : X) ⟿ x
  @[simp]
  theorem smooth_id_norm {X} [Vec X] : (λ (x : X) ⟿ x) = Smooth.id := by rfl
  @[simp]
  theorem smooth_id_eval {X} [Vec X] (x : X) : Smooth.id x = x := by unfold Smooth.id; simp

  def Smooth.const {X Y} [Vec X] [Vec Y] := λ (x : X) (_ : Y) ⟿ x
  @[simp]
  theorem smooth_const_norm_v1 {X Y} [Vec X] [Vec Y] : (λ (x : X) (_ : Y) ⟿ x) = Smooth.const := by rfl
  @[simp]
  theorem smooth_const_norm_v2 {X Y} [Vec X] [Vec Y] (x : X) : (λ (_ : Y) ⟿ x) = Smooth.const x := by rfl
  @[simp]
  theorem smooth_const_eval {X Y} [Vec X] [Vec Y] (x : X) (y : Y) : Smooth.const x y = x := by rfl

  -- example : (λ (x y : ℝ) ⟿ x * y * x) = 0 :=
  -- by 
  --   simp
  --   simp only [smooth_smul_norm_v1_id]
  --   simp only [smooth_hmul_norm]
  --   simp
  --   -- simp only[smooth_smul_norm_v2]
  --   done

  instance {Y₁ Y₂ Z} [Vec Y₁] [SemiHilbert Y₂] [SemiHilbert Z]
    (f : Y₁ ⟿ Y₂ ⟿ Z) [∀ y₁, HasAdjoint (λ y₂ => f y₁ y₂)]
    (g₁ : X ⟿ Y₁)
    : HasAdjoint (fun (g₂ : X ⟿ Y₂) => Smooth.diag f g₁ g₂) := by sorry

  @[simp]
  theorem diag_adj_arg2 {Y₁ Y₂ Z} [Vec Y₁] [SemiHilbert Y₂] [SemiHilbert Z]
    (f : Y₁ ⟿ Y₂ ⟿ Z) [∀ y₁, HasAdjoint (λ y₂ => f y₁ y₂)]
    (g₁ : X ⟿ Y₁)
    : (fun (g₂ : X ⟿ Y₂) => Smooth.diag f g₁ g₂)†
      =
      (fun (g₂' : X ⟿ Z) => Smooth.diag (λ y₁ y₂' ⟿ (f y₁)† y₂') g₁ g₂')
    := sorry

  @[simp]
  theorem diag_adj_arg1 {Y₁ Y₂ Z} [SemiHilbert Y₁] [Vec Y₂] [SemiHilbert Z]
    (f : Y₁ ⟿ Y₂ ⟿ Z) [∀ y₂, HasAdjoint (λ y₁ => f y₁ y₂)]
    (g₂ : X ⟿ Y₂)
    : (fun (g₁ : X ⟿ Y₁) => Smooth.diag f g₁ g₂)†
      =
      (fun (g₁' : X ⟿ Z) => Smooth.diag (λ y₁' y₂ ⟿ (λ y₁ => f y₁ y₂)† y₁') g₁' g₂)
    := sorry

  @[simp]
  theorem diag_adj_arg_uncurry {W Y₁ Y₂ Z} [SemiHilbert W] [SemiHilbert Y₁] [SemiHilbert Y₂] [SemiHilbert Z]
    (f : Y₁ ⟿ Y₂ ⟿ Z) [HasAdjoint (λ (y₁,y₂) => f y₁ y₂)]
    (g₁ : W → (X ⟿ Y₁)) [HasAdjoint g₁]
    (g₂ : W → (X ⟿ Y₂)) [HasAdjoint g₂]
    : (fun (w : W) => Smooth.diag f (g₁ w) (g₂ w))†
      =
      let F := (λ (y₁,y₂) => f y₁ y₂)†
      let G₁ := g₁†
      let G₂ := g₂†
      let G₁₂ := λ (f : X ⟿ Y₁ × Y₂) => (G₁ (λ x ⟿ (f x).1) + G₂ (λ x ⟿ (f x).2))
      (fun (w' : X ⟿ Z) => G₁₂ (λ x ⟿ F (w' x)))
    := sorry

  /- not true, it is missing jacobian !!! -/
  theorem comp_adj_arg1 {Y Z} {κ} [Enumtype κ] [FinVec Y κ] [SemiHilbert Z]
    (g : X ⟿ Y) [IsInv (λ x => g x)] [IsSmooth (λ y => g.1⁻¹ y)]
    : (fun (f : Y ⟿ Z) => Smooth.comp f g)†
      =
      (fun (f' : X ⟿ Z) => Smooth.comp f' (λ y ⟿ g.1⁻¹ y)) /- missing jacobian -/
    := sorry

  @[simp]
  theorem comp_adj_arg2 {Y Z} [SemiHilbert Y] [SemiHilbert Z]
    (f : Y ⟿ Z) [HasAdjoint (λ y => f y)]
    : (fun (g : X ⟿ Y) => Smooth.comp f g)†
      =
      (fun (g' : X ⟿ Z) => Smooth.comp (λ z ⟿ f.1† z) g')
    := sorry

  example (f : ℝ ⟿ ℝ) : (λ x ⟿ x * f x) = Smooth.id * f := by simp

  instance {Y} [SemiHilbert Y] (g : X ⟿ ℝ)
    : HasAdjoint (λ (f : X ⟿ Y) => g * f) := sorry

  @[simp]
  theorem mor_mul_adj_left {Y} [SemiHilbert Y] (g : X ⟿ ℝ)
    : (λ (f : X ⟿ Y) => g * f)† = (λ (f' : X ⟿ Y) => g * f') := sorry

  instance (g : X ⟿ ℝ) 
    : HasAdjoint (λ (f : X ⟿ ℝ) => f * g) := sorry

  @[simp]
  theorem mor_mul_adj_right_general {Y} [Hilbert Y] (g : X ⟿ Y)
    : (λ (f : X ⟿ ℝ) => f * g)† = (λ (f' : X ⟿ Y) => Smooth.diag (λ x y ⟿ ⟪x,y⟫) f' g) := sorry

  -- @[simp]
  -- theorem mor_mul_adj_right (g : X ⟿ ℝ)
  --   : (λ (f : X ⟿ ℝ) => f * g)† = (λ (f' : X ⟿ ℝ) => f' * g) := sorry

  example : (λ (f : ℝ ⟿ ℝ) => (λ x ⟿ x * f x))† = λ f' => Smooth.id * f' := by simp
  example (g : ℝ ⟿ ℝ) 
    : (λ (f : ℝ ⟿ ℝ) => (λ x ⟿ g x * f x * x))† 
      = 
      λ f' => λ x ⟿ g x * f' x * x := 
  by 
    simp[hold]; funext f'; ext x; simp

  example : (λ (f : ℝ ⟿ ℝ) => (λ x ⟿ f x + f x * x))† = λ (f' : ℝ ⟿ ℝ) (x : ℝ) ⟿ f' x + f' x * x:= by simp[hold]

  -- example (f : ℝ ⟿ ℝ) : (λ x ⟿ x * f x * x) = Smooth.id * f * Smooth.id := by simp
  -- example (c : ℝ) : (λ x ⟿ c * x) = c * Smooth.id := by simp

  example
    : let G := (λ f : ℝ ⟿ ℝ => f * (λ x ⟿ x))
      (λ f : ℝ ⟿ ℝ => G f)
      =
      (λ f : ℝ ⟿ ℝ => λ x ⟿ f x * x) :=
  by 
    simp only[]; simp only[smooth_mul_norm]; done
      
  -- set_option trace.Meta.synthInstance true in
  example {Y} [Hilbert Y]
    : HasAdjoint (λ f : ℝ ⟿ ℝ => λ x ⟿ x * f x * x) :=
  by
    simp; infer_instance
  
  example
    : SciLean.HasAdjoint fun (f : X ⟿ ℝ) => λ x ⟿ f x := by simp; infer_instance

  example (c : ℝ)
    : SciLean.HasAdjoint fun (f : X ⟿ ℝ) => λ x ⟿ c * f x := by simp; infer_instance

  example (c : ℝ)
    : SciLean.HasAdjoint fun (f : X ⟿ ℝ) => λ x ⟿ f x * c := by simp; infer_instance

  example (g : X ⟿ ℝ)
    : SciLean.HasAdjoint fun (f : X ⟿ ℝ) => λ x ⟿ (g x * f x) := by simp; infer_instance

  example (g : X ⟿ ℝ) (c : ℝ)
    : SciLean.HasAdjoint fun (f : X ⟿ ℝ) => λ x ⟿ c * (g x * f x) := by simp; infer_instance

  example {X} [Hilbert X] (x : X)
    : HasAdjoint (λ (y : X) ⟿ ⟪x, y⟫).1 := by infer_instance

  example {X} [Hilbert X] (y : X)
    : HasAdjoint (λ (x : X) ⟿ ⟪x, y⟫).1 := by infer_instance

  set_option pp.funBinderTypes true in
  -- set_option trace.Meta.Tactic.simp.rewrite true in
  example {Y} [Hilbert Y] (g : X ⟿ Y)
    : SciLean.HasAdjoint fun (f : X ⟿ Y) => λ x ⟿ ⟪g x, f x⟫ :=
  by
    simp; infer_instance

  example (g : X ⟿ ℝ)
    : SciLean.HasAdjoint fun (f : X ⟿ ℝ) => λ x ⟿ ⟪f x, g x⟫ := by infer_instance

  example : IsSmooth fun x y : ℝ => y * (2 * x) := by infer_instance

  example (g : X ⟿ ℝ)
    : SciLean.HasAdjoint fun (f : X ⟿ ℝ) => λ x ⟿ (g x * ((2 : ℝ) * f x)) := by simp; infer_instance

  example (g : X ⟿ ℝ)
    : SciLean.HasAdjoint fun (f : X ⟿ ℝ) => λ x ⟿ f x * g x := by infer_instance
  
  -- set_option trace.Meta.Tactic.simp.discharge true in
  -- set_option trace.Meta.Tactic.simp.rewrite true in
  example (g : X ⟿ ℝ)
    : varDual (λ f : X ⟿ ℝ => ∫ λ x ⟿ g x * f x) = g := 
  by 
    simp; ext x; simp; done

  example {Y} [Hilbert Y] (g : X ⟿ Y) :
      SciLean.HasAdjoint fun f : X ⟿ Y => fun x' ⟿ ⟪f x', g x'⟫ :=
  by
    simp; infer_instance

  example {X Y ι} [Enumtype ι] [FinVec X ι] [Hilbert Y] (g : X ⟿ Y) 
    : varDual (λ f : X ⟿ Y => ∫ λ x ⟿ ⟪f x, g x⟫) = g := 
  by 
    simp; ext x; simp; done

  example {X Y ι} [Enumtype ι] [FinVec X ι] [Hilbert Y] (g : X ⟿ Y) (c : ℝ)
    : varDual (λ f : X ⟿ Y => ∫ λ x ⟿ c * ⟪f x, g x⟫) = c * g := 
  by 
    simp; ext x; simp; done

  class Divergence (Fun : Type) (Diff : outParam Type) where
    divergence : Fun → Diff

  export Divergence (divergence)
  
  @[defaultInstance]
  noncomputable
  instance divergence_of_differential_mor {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] 
    : Divergence (X ⟿ X ⊸ Y) (X ⟿ Y) where
    divergence f := λ x ⟿ ∑ i, ∂ f x (𝔼 i) (𝔼 i)

  noncomputable
  instance divergence_of_differential {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] 
    : Divergence (X → X → Y) (X → Y) where
    divergence f := λ x => ∑ i, ∂ f x (𝔼 i) (𝔼 i)

  noncomputable
  instance divergence_of_endomorphism_mor {X ι} [Enumtype ι] [FinVec X ι]
    : Divergence (X ⟿ X) (X ⟿ ℝ) where
    divergence f := λ x ⟿ ∑ i, ⟪∂ f x (𝔼 i), 𝔼 i⟫

  noncomputable
  instance divergence_of_endomorphism {X ι} [Enumtype ι] [FinVec X ι]
    : Divergence (X → X) (X → ℝ) where
    divergence f := λ x => ∑ i, ⟪∂ f x (𝔼 i), 𝔼 i⟫

  prefix:max "∇·" => divergence

  syntax "∇·" diffBinder "," term:66 : term
  syntax "∇·" "(" diffBinder ")" "," term:66 : term
  macro_rules 
  | `(∇· $x:ident, $f) =>
    `(∇· λ $x => $f)
  | `(∇· $x:ident : $type:term, $f) =>
    `(∇· λ $x : $type => $f)
  | `(∇· $x:ident := $val:term, $f) =>
    `((∇· λ $x => $f) $val)
  | `(∇· ($b:diffBinder), $f) =>
    `(∇· $b, $f)

  instance {Y} [SemiHilbert Y] 
    : HasAdjoint (λ f : X ⟿ Y => ∂ f) := sorry

  @[simp]
  theorem diff_adjoint {Y} [SemiHilbert Y]
    : (λ f : X ⟿ Y => ∂ f)† = λ f' : X ⟿ X ⊸ Y => - ∇· f' := sorry

  @[simp]
  theorem divergence_adjoint {Y} [SemiHilbert Y]
    : (λ f : X ⟿ X ⊸ Y => ∇· f)† = λ f' : X ⟿ Y => - ∂ f' := sorry

  theorem linear_has_adjoint_on_finvec {X Y ι κ} [Enumtype ι] [Enumtype κ] [FinVec X ι] [FinVec Y κ] (f : X → Y) [IsLin f] : HasAdjoint f := sorry
  theorem smooth_has_adjdiff_on_finvec {X Y ι κ} [Enumtype ι] [Enumtype κ] [FinVec X ι] [FinVec Y κ] (f : X → Y) [IsSmooth f] : HasAdjDiff f := 
    ⟨by infer_instance, by intro x; apply linear_has_adjoint_on_finvec⟩

  -- On finite dimensional vector spaces, every linear map has adjoint
  -- Therefore we can prove these theorems
  instance {X Y ι κ} [Enumtype ι] [Enumtype κ] [FinVec X ι] [FinVec Y κ] (f : X → Y) [IsSmooth f] : IsSmooth λ x dy => ∂† f x dy := sorry
  instance {X Y ι κ} [Enumtype ι] [Enumtype κ] [FinVec X ι] [FinVec Y κ] (f : X → Y) [IsSmooth f] (x : X) : IsSmooth λ dy => ∂† f x dy := sorry
  instance {X Y ι κ} [Enumtype ι] [Enumtype κ] [FinVec X ι] [FinVec Y κ] (f : X → Y) [IsSmooth f] (x : X) : IsLin λ dy => ∂† f x dy := sorry

  instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) [HasAdjDiff f] : IsSmooth λ x dy => ∂† f x dy := sorry
  instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) [HasAdjDiff f] (x : X) : IsSmooth λ dy => ∂† f x dy := sorry
  instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) [HasAdjDiff f] (x : X) : IsLin λ dy => ∂† f x dy := sorry
  
  -- This can be meaningfully defined only on finitely dimensional vector spaces for now
  -- Otherwise I would need special notation for `{f : X → Y // HasAdjDiff f}` that that is just getting too complicated
  noncomputable 
  instance adjoint_differential_mor {X Y ι κ} [Enumtype ι] [Enumtype κ] [FinVec X ι] [FinVec Y κ]
    : AdjointDifferential (X ⟿ Y) (X ⟿ Y ⊸ X) where
    adjointDifferential f := λ x ⟿ λ dy ⊸ ∂† f.1 x dy
  
  -- fails to prove linearity on rhs
  -- @[simp]
  -- theorem adjDiff_adjoint {Y κ} [Enumtype κ] [FinVec Y κ]
  --   : (λ f : X ⟿ Y => ∂† f)† = λ f' : X ⟿ Y ⊸ X => - ∇· (λ x ⟿ λ dx ⊸ ((f' x).1)† dx) := sorry

  example {Y} [Hilbert Y] (g : X ⟿ Y) (c : X) 
    : IsSmooth (λ (x : X) => ∂ g c) := by infer_instance 

  -- Why does this fail????
  -- #check (λ {Y} [Hilbert Y] (g : X ⟿ Y) (f : X ⟿ Y) => λ x ⟿ ⟪∂ f x, ∂ g x⟫)

  set_option pp.funBinderTypes true in
  set_option synthInstance.maxSize 2048 in
  -- set_option synthInstance.maxHeartbeats 200000 in
  example {Y} [Hilbert Y] (g : X ⟿ Y) 
    : HasAdjoint (λ (f : X ⟿ Y) => λ x ⟿ ⟪∂ f x, ∂ g x⟫) := by simp; infer_instance; done

  set_option synthInstance.maxSize 2048 in
  example {Y} [Hilbert Y] (g : X ⟿ Y) 
    : (λ (f : X ⟿ Y) => λ x ⟿ ⟪∂ f x, ∂ g x⟫)† = λ g' => - divergence (g' * ∂ g) := by simp; unfold hold; simp done 

  -- noncomputable
  -- def dd {X} [Vec X] (f : ℝ ⟿ X) : ℝ ⟿ X := λ t ⟿ ∂ f t 1

  noncomputable
  instance {X} [Vec X] : Derivative (ℝ ⟿ X) (ℝ ⟿ X) where
    derivative f := λ t ⟿ ∂ f t 1

  instance {X} [SemiHilbert X] : HasAdjoint (λ f : ℝ ⟿ X => ⅆ f) := sorry
  @[simp]
  theorem dd_adjoint {X} [SemiHilbert X] : (λ f : ℝ ⟿ X => ⅆ f)† = λ f' => - ⅆ f' := sorry

  instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) [HasAdjDiff f] (x) : HasAdjoint (∂ f x) := sorry
  @[simp]
  theorem adj_of_differential {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) [HasAdjDiff f] (x) : (∂ f x)† = ∂† f x := sorry

  example {X} [Hilbert X] (y : ℝ ⟿ X) (L : X → ℝ) [HasAdjDiff L] [IsSmooth L] : IsSmooth λ t => ∂† L (ⅆ y t) := by infer_instance

  macro (priority := high) "ⅆ" x:Lean.explicitBinders ";" f:term:66 : term => `(ⅆ (λ $x ⟿ $f))

  -- set_option synthInstance.maxSize 2048 in
  example {X} [Hilbert X] (y : ℝ ⟿ X) (L : X → ℝ) [HasAdjDiff L] [IsSmooth L]
    : (λ (dy : ℝ ⟿ X) => λ t ⟿ ∂ L (ⅆ y t) (ⅆ dy t))† 1 
      = 
      - ⅆ t; ∇ L (ⅆ y t)
  :=
  by
    simp[One.one, OfNat.ofNat, gradient]
    done

  example (L : X → ℝ) [HasAdjDiff L] [IsSmooth L]
    : (∇ (y : ℝ ⟿ X), λ t ⟿ L (ⅆ y t))
      = 
      λ y => - ⅆ t; ∇ L (ⅆ y t)
      -- λ y => λ t ⟿ - ∂ (∇ L) (ⅆ y t) (ⅆ (ⅆ y) t) -- can't prove smoothness right now
  :=
  by
    conv => 
      lhs 
      simp[One.one, OfNat.ofNat, gradient]
      simp only [adjointDifferential]
      simp
    done


  example {X} [Hilbert X] (y : ℝ ⟿ X) (L : X → ℝ) [HasAdjDiff L] [IsSmooth L]
    : (λ (dy : ℝ ⟿ X) => λ t ⟿ ∂ L (y t) (dy t))† 1 
      = 
      λ t ⟿ ∇ L (y t)
  :=
  by
    simp[One.one, OfNat.ofNat, gradient]
    done

  example {X} [Hilbert X] (y : ℝ ⟿ X) (L : X → ℝ) [HasAdjDiff L] [IsSmooth L]
    : (∇ (y' : ℝ ⟿ X), λ t ⟿ L (y' t)) y
      = 
      λ t ⟿ ∇ L (y t)
  :=
  by
    simp[One.one, OfNat.ofNat, gradient]
    done

  variable {X : Type} [SemiHilbert X] (L : X → X → ℝ) [IsSmooth L] [∀ x, IsSmooth (L x)] [∀ x, HasAdjDiff λ v => L x v] [∀ v, HasAdjDiff λ x => L x v] (y  : ℝ ⟿ X)

  -- Euler Lagrange equations
  #check λ t => ⅆ (s := t), ∇ (v := ⅆ y s), L (y s) v + ∇ (x := y t), L x (ⅆ y t)
  #check λ s ⟿ (∇ v, L (y s) v) (ⅆ y s)

  #check λ s ⟿ (∇ v, L (y s) v)
  #check λ s ⟿ (∇ (v := ⅆ y s), L (y s) v)

  #check HAdd

  variable (f f' : ℝ → ℝ → ℝ) (s t dt : ℝ) (c : ℝ) (g h : ℝ → ℝ) (ϕ) [IsSmooth g] [IsSmooth h]

  --- ∂ x, f x  vs  ∂ λ x => f x
  --- ∑ i, f i  vs  ∑ λ i => f i
  --- ∫ x, f x  vs  ∫ λ x => f x

  #check ((ⅆ x, g (h x)) rewrite_by (simp))

  #check ∂ t', f t' s
  #check ⅆ t', g t'
  #check ⅆ g
  #check (∂† t', f t' s) t dt
  #check (∇ t', g t')
  #check ∇ g

  -- symbolic differentiation:
  -- ∂  : (X→Y) → (X→X→Y)      -- differential
  -- ∂† : (X→Y) → (X→Y→X)      -- adjoint differential

  -- ⅆ  : (ℝ→X) → (ℝ→X)        -- derivative  (sugar for (∂  · · 1))
  -- ∇  : (X→ℝ) → (X→X)        -- gradient    (sugar for (∂† · · 1))

  -- automatic differentiation
  -- 𝓣 : (X→Y) → (X→X×(X→Y))  -- forward mode AD
  -- 𝓑 : (X→Y) → (X→X×(Y→X))  -- reverse mode AD

  -- ?? : (X→Y) → (X×X→Y×Y)     -- dual number AD

  -- #check (differential · · (1 : ℝ))
  -- #check (∂† · · (1 : ℝ))

  #exit

  -- λ t => - (ⅆ t', (∇ ẋ, L ẋ (y t')) (ⅆ y t)) + (∇ x, L (ⅆ y t) x) (y t)

  example (f df : X ⟿ Y) : IsLin (λ x => ∂ (fun (f : X ⟿ Y) => ∂ f) f df x) :=
  by
    simp[Differential.differential]; infer_instance

  -- This should fail fast !!!
  -- set_option trace.Meta.synthInstance true in
  -- set_option trace.Meta.synthInstance.resume false in
  -- set_option trace.Meta.synthInstance.tryResolve false in
  example (f df : X ⟿ Y) : IsLin λ x => (∂ (fun (f' : X ⟿ Y) => ∂ f') f df) x := 
  by
    admit -- infer_instance



  #exit

  set_option synthInstance.maxSize 2048 in
  example : ∀ (x : X), IsSmooth fun (f : X ⟿ Y) => (2 : ℝ) * f x := by infer_instance

  @[simp] 
  theorem integral_diff (F : Z → X → Y) [IsSmooth F] [∀ f, IsSmooth (F f)]
    : (∂ λ (z : Z) => ∫ x, F z x) = λ z dz => ∫ x, ∂ F z dz x := sorry

  #check λ f : X⟿Y => ∫ f
  #check λ f : X⟿Y => ∫ λ x => f x

  example : IsLin λ (f : X⟿Y) => ∫ f := by infer_instance
  example : IsLin λ (f : X⟿Y) => ∫ x, f x := by infer_instance
  example : IsLin λ (f : X⟿Y) => ∫ x, (2 : ℝ) * f x := by infer_instance
  example : IsSmooth λ (f : X⟿Y) => ∫ x, f x := by infer_instance
  -- set_option trace.Meta.synthInstance true in
  set_option synthInstance.maxSize 2048 in
  example : IsSmooth λ (f : X⟿Y) => ∫ x, (2 : ℝ) * f x := by infer_instance
  example : (∂ λ (f : X⟿Y) => ∫ x, f x) = (λ _ df : X⟿Y => ∫ x, df x) := by simp

  example (u : X) : IsSmooth λ (f : X⟿Y) (x : X) => ∂ f.1 x u := by infer_instance
  example (u : X) : IsSmooth (λ (f : X⟿Y) => ∫ x, ∂ f.1 x u) := by infer_instance
  set_option synthInstance.maxSize 2048 in
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
