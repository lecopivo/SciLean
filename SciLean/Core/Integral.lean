import SciLean.Core.CoreFunctionProperties
import SciLean.Core.FinVec

namespace SciLean



opaque LocIntDom (X : Type) [Vec X] : Type


-- If `f` is integrable on `Ω` return integral otherwise return zero
-- IMPORTANT: We choose to integrate only over **bounded** domains.
--            This way the function `λ (f : X⟿Y) => ∫ x, f x` can be linear.
-- QUESTION: Do we need Y to be complete? For example smooth function
--   with compact support do not form closed subspace in `ℝ ⟿ ℝ`. 
--   Can we have `γ : ℝ ⟿ {f : ℝ ⟿ ℝ // TestFun f}` such that 
--   `∫ t ∈ [0,1], γ.1` is not a `TestFun`?
noncomputable
opaque integral {X Y ι : Type} [Enumtype ι] [FinVec X ι] [Vec Y] (f : X ⟿ Y) (Ω : LocIntDom X) : Y 

noncomputable
opaque limitOverWholeDomain {X Y ι : Type} [Enumtype ι] [FinVec X ι] [Vec Y] (F : LocIntDom X → Y) : Y

instance {X Y ι : Type} [Enumtype ι] [FinVec X ι] [Vec Y] (f : X ⟿ Y) : Integral f (integral f) := ⟨⟩

syntax intBinderType  := ":" term
syntax intBinder := ident (intBinderType)?
syntax "∫" intBinder "," term:66 : term
syntax "∫" "(" intBinder ")" "," term:66 : term
macro_rules
| `(∫ $x:ident, $f) =>
  `(∫ (SmoothMap.mk' λ $x => $f))
| `(∫ $x:ident : $type:term, $f) =>
  `(∫ (SmoothMap.mk' λ ($x : $type) => $f))
| `(∫ ($x:ident : $type:term), $f) =>
  `(∫ $x:ident : $type:term, $f)


variable {X Y ι : Type} [Enumtype ι] [FinVec X ι] [Hilbert Y]


noncomputable
instance : Inner (X⟿Y) where
  inner f g := (∫ x, ⟪f x, g x⟫) |> limitOverWholeDomain

instance : TestFunctions (X⟿Y) where
  TestFun f := sorry -- has compact support

noncomputable
instance : SemiHilbert (X⟿Y) := SemiHilbert.mkSorryProofs


noncomputable
def variationalDual (F : (X⟿Y) → (LocIntDom X → ℝ)) : (X⟿Y) :=
  let has_dual := ∃ A : (X⟿Y) → (X⟿ℝ), HasAdjointT A ∧ ∀ ϕ, F ϕ = ∫ (A ϕ)
  match Classical.propDecidable (has_dual) with
  | isTrue h => 
    let A := Classical.choose h
    A† (λ _ ⟿ 1)
  | isFalse _ => 0


instance (F : (X⟿Y) → (LocIntDom X → ℝ)) 
  : Dagger F (variationalDual F) := ⟨⟩

--------------------------------------------------------------------------------


@[simp ↓, autodiff]
theorem varDual_smooth_fun (F : (X⟿Y) → (X⟿ℝ)) [HasAdjointT F]
  : (λ (f : X ⟿ Y) => ∫ (F f))† = F† (λ _ ⟿ 1) := sorry_proof

-- move somewhere else
instance {X Y Z} [Vec X] [SemiHilbert Y] [SemiHilbert Z]
  (A : X → Y → Z) [∀ x, HasAdjointT (A x)] [IsSmoothNT 2 A]
  : IsSmoothT (λ x => (A x)†) := sorry_proof

@[simp ↓, autodiff]
theorem varDual_smooth_fun_elemwise [Hilbert Y] (A : X → Y → ℝ) [∀ x, HasAdjointT (A x)] [IsSmoothNT 2 A]
  : (λ (g : X ⟿ Y) => ∫ x, A x (g x))† = (λ x ⟿ (A x)† 1) := sorry_proof

-- @[simp ↓, autodiff]
theorem varDual_smooth_fun_elemwise' [Hilbert Y] [Vec Z] (f : X → Z) [IsSmoothT f] (A : Y → Z → ℝ) [∀ z, HasAdjointT (λ y => A y z)] [IsSmoothNT 2 A]
  : (λ (g : X ⟿ Y) => ∫ x, A (g x) (f x))† = (λ x ⟿ (λ y => A y (f x))† 1)  := sorry_proof

-- 

instance {X Y} [Vec X] [SemiHilbert Y] [SemiHilbert (X⟿Y)] [SemiHilbert (X⟿ℝ)]
  (A : Y → ℝ) [HasAdjointT A] [IsSmoothT A] : HasAdjointT (λ (ϕ : X ⟿ Y) => (λ (x : X) ⟿ A (ϕ x))) := sorry

example (f : X⟿Y) : IsSmoothT (SmoothMap.val f) := by infer_instance


example (f : X⟿Y) : (λ g : X⟿Y => ∫ x, ⟪f x, g x⟫)† = f := by simp
-- set_option trace.Meta.Tactic.simp.unify true in
-- set_option trace.Meta.Tactic.simp.discharge true in
example (f : X⟿Y) : (λ g : X⟿Y => ∫ x, ⟪g x, f x⟫)† = f :=
by
  simp
  rw[varDual_smooth_fun_elemwise']
  simp
  done
  


example : HasAdjointT fun (g : X⟿Y) => fun x ⟿ g x := by infer_instance
example : IsSmoothT fun (g : X⟿Y) => fun x ⟿ g x := by infer_instance

#check (fun (g : X⟿Y) => fun x ⟿ g x)† 
       rewrite_by simp; trace_state


-- instance oj  {X Y Y' Z} [Vec X] [Vec Y] [Vec Y'] [Vec Z] 
--   (f : X → Y → Y' → Z) [IsSmoothNT 3 f]  
--   (g' : X → Y') [IsSmoothNT 1 g']
--   : IsSmoothNT 2 λ (g : X⟿Y) x => f x (g x) (g' x) := sorry_proof

-- instance {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y → Z) [IsSmoothNT 2 f] 
--   : IsSmoothNT 2 λ (g : X⟿Y) x => f x (g x) := by apply oj (λ x y _ => f x y) (λ x => x)

-- instance oh {X Y Y₁ Y₂ Z} [Vec X] [Vec Y] [Vec Y₁] [Vec Y₂] [Vec Z] 
--   (f : Y₁ → Y₂ → Z) [IsSmoothNT 2 f]  
--   (g₁ : X → Y → Y₁) [IsSmoothNT 2 g₁]
--   (g₂ : X → Y → Y₂) [IsSmoothNT 2 g₂] 
--   : IsSmoothNT 2 λ (g : X⟿Y) x => f (g₁ x (g x)) (g₂ x (g x)) := sorry_proof

instance {X} [Hilbert X] : HasAdjoint (λ (f : ℝ⟿X) => ⅆ f) := by (try infer_instance); sorry_proof

@[simp ↓,autodiff]
theorem differentialScalar.arg_f.adj_simp : (λ (f : ℝ⟿X) => ⅆ f)† = (λ (f : ℝ⟿X) => - ⅆ f) := by /- simp - maybe fix infinite recursion? -/ sorry_proof

instance thm1 {Y'} [Vec Y'] {Z} [Hilbert Z] (A : X → Y → Y' → Z) [∀ x y', HasAdjointT (λ y => A x y y')] [IsSmoothNT 3 A] 
  (g' : X → Y' := λ _ => 0) [IsSmoothT g']
  : HasAdjointT (λ (g : X⟿Y) => λ x ⟿ A x (g x) (g' x)) := by (try infer_instance); sorry_proof

instance {Z} [Hilbert Z] (A : X → Y → Z) [∀ x, HasAdjointT (A x)] [IsSmoothNT 2 A] 
  : HasAdjointT (λ (g : X⟿Y) => λ x ⟿ A x (g x)) := 
by
  try infer_instance
  apply thm1 (λ x y (y' : X) => A x y) (λ x : X => x) -- I think the unification can't infer the choice of Y' and g'
  done  


instance (Z) [Hilbert Z] (A : Y → Z) [HasAdjointT A] [IsSmoothT A] 
  : HasAdjointT (λ (g : X⟿Y) => λ x ⟿ A (g x)) := by infer_instance


example  : HasAdjointT fun (g : X⟿Y) => fun x ⟿ g x := by infer_instance
example  : HasAdjointT fun (g : X⟿Y) => fun x ⟿ (2:ℝ) * g x := by infer_instance
example  : HasAdjointT fun (g : ℝ⟿ℝ) => fun (x : ℝ) ⟿ x * g x := by infer_instance

example  (f : X⟿Y) : HasAdjointT fun (g : X⟿Y) => fun x ⟿ ⟪g x, f x⟫ := by infer_instance
example  (f : X⟿Y) : HasAdjointT fun (g : X⟿Y) => fun x ⟿ ⟪f x, g x⟫ := by infer_instance

-- set_option trace.Meta.synthPending true in
-- example  (f : ℝ⟿ℝ) : HasAdjointT fun (g : ℝ⟿ℝ) => fun x ⟿ ⟪f x, g x⟫ := by infer_instance

#check Nat

example (D : (ℝ⟿ℝ) → (ℝ⟿ℝ)) [HasAdjointT D] : HasAdjointT fun (g : ℝ⟿ℝ) => fun x ⟿ D g x := by infer_instance

example (D : (ℝ⟿ℝ) → (ℝ⟿ℝ)) [HasAdjointT D] : HasAdjointT fun (g : ℝ⟿ℝ) => fun x ⟿ x * D g x :=
by

  let f₁ := fun (g : ℝ⟿ℝ) => fun x ⟿ x * g x
  have h : (fun (g : ℝ⟿ℝ) => fun x ⟿ x * D g x) = f₁∘D := by rfl
  have af₁ : HasAdjointT f₁ := by infer_instance
  
  rw[h]
  infer_instance
  done

set_option synthInstance.maxSize 2000 in 
example  (f : ℝ⟿ℝ) : HasAdjointT fun (g : ℝ⟿ℝ) => fun x ⟿ ⟪f x, ⅆ g x⟫ :=
by

  let f₁ := fun (g : ℝ⟿ℝ) => fun x ⟿ ⟪f x, g x⟫
  have h : (fun (g : ℝ⟿ℝ) => fun x ⟿ ⟪f x, ⅆ g x⟫) = f₁∘Smooth.differentialScalar := by rfl
  have af₁ : HasAdjointT f₁ := by infer_instance
  
  rw[h]
  infer_instance
  done


set_option synthInstance.maxSize 2000 in 
example (f : ℝ⟿ℝ) : HasAdjointT fun (g : ℝ⟿ℝ) => fun x ⟿ ⟪f x, ⅆ g x⟫ := by infer_instance

-- variable (f : ℝ⟿ℝ)

-- #check ⅆ f  
