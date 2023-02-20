import SciLean.Core.CoreFunctionProperties
import SciLean.Core.FinVec

namespace SciLean


opaque LocIntDom (X : Type) [Vec X] : Type


--------------------------------------------------------------------------------
-- Integral
--------------------------------------------------------------------------------


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

instance integral.instNotationIntegral 
  {X Y ι : Type} [Enumtype ι] [FinVec X ι] [Vec Y] (f : X ⟿ Y) 
  : Integral f (integral f) := ⟨⟩

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


--------------------------------------------------------------------------------
-- SemiHilbert structure on spaces like `ℝ^{n}⟿ℝ`
--------------------------------------------------------------------------------

variable {X Y ι : Type} [Enumtype ι] [FinVec X ι] [Hilbert Y]

noncomputable
instance : Inner (X⟿Y) where
  inner f g := (∫ x, ⟪f x, g x⟫) |> limitOverWholeDomain

instance : TestFunctions (X⟿Y) where
  TestFun f := sorry -- has compact support

noncomputable
instance : SemiHilbert (X⟿Y) := SemiHilbert.mkSorryProofs


--------------------------------------------------------------------------------
-- Variational Dual
--------------------------------------------------------------------------------

-- variational version of †
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

-- variational version of ∇ 
noncomputable
def variationalGradient (F : (X⟿Y) → LocIntDom X → ℝ) (f : X⟿Y) : X ⟿ Y := (∂ F f)†

instance (F : (X⟿Y) → LocIntDom X → ℝ) : Nabla F (variationalGradient F) := ⟨⟩


-- Properties

@[simp ↓, autodiff]
theorem variationalGradient_unfold (F : (X⟿Y) → LocIntDom X → ℝ)
  : ∇ F = λ f => (∂ F f)† := by rfl

@[simp ↓, autodiff]
theorem varDual_smooth_fun (F : (X⟿Y) → (X⟿ℝ)) [HasAdjointT F]
  : (λ (f : X ⟿ Y) => ∫ (F f))† = F† (λ _ ⟿ 1) := sorry_proof

@[simp ↓, autodiff]
theorem varDual_smooth_fun_elemwise [Hilbert Y] (A : X → Y → ℝ) [∀ x, HasAdjointT (A x)] [IsSmoothNT 2 A]
  : (λ (g : X ⟿ Y) => ∫ x, A x (g x))† = (λ x ⟿ (A x)† 1) := sorry_proof

@[simp ↓, autodiff]
theorem varDual_smooth_fun_elemwise' [Hilbert Y] [Vec Z] (f : X → Z) [IsSmoothT f] 
  (A : Y → Z → ℝ) [∀ z, HasAdjointT (λ y => A y z)] [IsSmoothNT 2 A]
  : (λ (g : X ⟿ Y) => ∫ x, A (g x) (f x))† = (λ x ⟿ (λ y => A y (f x))† 1) := 
by apply varDual_smooth_fun_elemwise (λ x y => A y (f x)); done


#exit
--------------------------------------------------------------------------------
-- Junk
--------------------------------------------------------------------------------


example (f : X⟿Y) : (λ g : X⟿Y => ∫ x, ⟪f x, g x⟫)† = f := by simp
example (f : X⟿Y) : (λ g : X⟿Y => ∫ x, ⟪g x, f x⟫)† = f := by simp; done
  


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



instance integral.arg_f.isLin : IsLin (integral : (X⟿Y) → LocIntDom X → Y) := sorry_proof



@[simp ↓,autodiff]
theorem differentialScalar.arg_f.adj_simp 
  : (λ (f : ℝ⟿X) => ⅆ f)† = (λ (f : ℝ⟿X) => - ⅆ f) := 
by /- simp - maybe fix infinite recursion? -/ sorry_proof


instance {X Y } [SemiHilbert X] [SemiHilbert Y]
  (A : X → Y) [HasAdjointT A] [IsSmoothT A]
  : IsSmoothT A† := by infer_instance


instance {X Y Z} [Vec X] [SemiHilbert Y] [SemiHilbert Z]
  (A : X → Y → Z) [∀ x, HasAdjointT (A x)] [IsSmoothNT 2 A]
  : IsSmoothNT 2 (λ x z => (A x)† z) := by (try infer_instance); sorry_proof


-- instance  {Y'} [Vec Y'] {Z} [Hilbert Z]
--   (A : X → Y → Y' → Z) [∀ x y', HasAdjointT (λ y => A x y y')] [IsSmoothNT 3 A]
--   (g' : X → Y' := λ _ => 0) [IsSmoothT g']
--   : HasAdjointT (λ (g : X⟿Y) => λ x ⟿ A x (g x) (g' x)) :=
-- by  sorry_proof


instance scomb_highorder_adjoint {Z W} [SemiHilbert W] [Hilbert Z] 
  (F : (X⟿Y) → W → (X⟿Z)) [HasAdjointNT 2 F]  -- [IsSmoothNT 2 F]
  (G : (X⟿Y) → W) [HasAdjointT G]
  : HasAdjointT (λ (g : X⟿Y) => λ x ⟿ F g (G g) x) := by (try infer_instance); sorry_proof


set_option synthInstance.maxSize 2000 in
instance scomb_highorder_adjoint_simp {Z W} [SemiHilbert W] [Hilbert Z]
  (F : (X⟿Y) → W → (X⟿Z)) [HasAdjointNT 2 F] [IsSmoothNT 2 F]
  (G : (X⟿Y) → W) [HasAdjointT G] [IsSmoothT G]
  : (λ (g : X⟿Y) => λ (x:X) ⟿ (F g (G g) x))†
    =
    λ h => 
      let gw := (uncurryN 2 F)† h
      let (g',w) := gw
      let g'' := G† w
      λ x ⟿ g' x + g'' x 
  := by sorry_proof


instance elemwise_adjoint {Z} [Hilbert Z] (A : X → Y → Z) [∀ x, HasAdjointT (A x)] [IsSmoothNT 2 A]
  : HasAdjointT (λ (g : X⟿Y) => λ x ⟿ A x (g x)) := 
by 
  try infer_instance
  sorry_proof


@[simp ↓, autodiff]
theorem elemwise_adjoint_simp {Z} [Hilbert Z] (A : X → Y → Z) [∀ x, HasAdjointT (A x)] [IsSmoothNT 2 A]
  : (λ (g : X⟿Y) => λ x ⟿ A x (g x))†
    =
    λ g => λ x ⟿ (A x)† (g x) := by sorry_proof


instance elemwise_adjoint_alt1 {X Y ι : Type} [Enumtype ι] [FinVec X ι] [Hilbert Y]
  {X' Y' ι' : Type} [Enumtype ι'] [FinVec X' ι'] [Hilbert Y']
  (D : (X⟿Y) → (X'⟿Y')) [HasAdjointT D]
  {Z} [Hilbert Z] (A : X' → Y' → Z) [∀ x, HasAdjointT (A x)] [IsSmoothNT 2 A]
  : HasAdjointT (λ (g : X⟿Y) => λ x ⟿ A x (D g x)) :=
by
  try infer_instance
  let G := λ g : X'⟿Y' => λ x ⟿ A x (g x)
  let h : (λ (g : X⟿Y) => λ x ⟿ A x (D g x)) = λ g => G (D g) := by rfl
  rw [h]
  infer_instance
  done

@[simp ↓, autodiff]
theorem elemwise_adjoint_simp_alt1 {X Y ι : Type} [Enumtype ι] [FinVec X ι] [Hilbert Y]
  {X' Y' ι' : Type} [Enumtype ι'] [FinVec X' ι'] [Hilbert Y']
  (D : (X⟿Y) → (X'⟿Y')) [HasAdjointT D]
  {Z} [Hilbert Z] (A : X' → Y' → Z) [∀ x, HasAdjointT (A x)] [IsSmoothNT 2 A]
  : (λ (g : X⟿Y) => λ x ⟿ A x (D g x))†
    =
    λ g' => D† (λ x ⟿ (A x)† (g' x))
  := 
by
  let G := λ g : X'⟿Y' => λ x ⟿ A x (g x)
  let h : (λ (g : X⟿Y) => λ x ⟿ A x (D g x)) = λ g => G (D g) := by rfl
  rw [h]
  simp
  done


instance elemwise_adjoint_alt2 {Y'} [Vec Y'] {Z} [Hilbert Z]
  (A : X → Y → Y' → Z) [∀ x y', HasAdjointT (λ y => A x y y')] [IsSmoothNT 3 A]
  (g' : X → Y') [IsSmoothT g']
  : HasAdjointT (λ (g : X⟿Y) => λ x ⟿ A x (g x) (g' x)) :=
by 
  try infer_instance
  apply elemwise_adjoint_alt1 (λ x => x) (λ x y => A x y (g' x))
  done

@[simp ↓, autodiff]
theorem elemwise_adjoint_simp_alt2 {Y'} [Vec Y'] {Z} [Hilbert Z]
  (A : X → Y → Y' → Z) [∀ x y', HasAdjointT (λ y => A x y y')] [IsSmoothNT 3 A]
  (g' : X → Y' := λ _ => 0) [IsSmoothT g']
  : (λ (g : X⟿Y) => λ x ⟿ A x (g x) (g' x))†
    =
    λ h => λ x ⟿ (λ y => A x y (g' x))† (h x) :=
by
  rw[elemwise_adjoint_simp_alt1 (λ x => x) (λ x y => A x y (g' x))]
  rw[id.arg_x.adj_simp]
  done



example  : HasAdjointT fun (g : X⟿Y) => fun x ⟿ g x := by infer_instance
example  : HasAdjointT fun (g : X⟿Y) => fun x ⟿ (2:ℝ) * g x := by infer_instance
example  : HasAdjointT fun (g : ℝ⟿ℝ) => fun (x : ℝ) ⟿ x * g x := by infer_instance

example  (f : X⟿Y) : HasAdjointT fun (g : X⟿Y) => fun x ⟿ ⟪g x, f x⟫ := by infer_instance
example  (f : X⟿Y) : HasAdjointT fun (g : X⟿Y) => fun x ⟿ ⟪f x, g x⟫ := by infer_instance


example  : HasAdjointT fun (g : X⟿Y) => fun x ⟿ g x + g x := 
by 
  try infer_instance
  apply elemwise_adjoint (λ _ y => y + y)
  done

example  : HasAdjointT fun (g : ℝ⟿Y) => fun x ⟿ g x + x * g x := 
by 
  try infer_instance
  apply elemwise_adjoint (λ x y => y + x * y)
  done

set_option synthInstance.maxSize 2000 in
example  : HasAdjointT fun (g : ℝ⟿Y) => fun x ⟿ g x + ⅆ g x := 
by 
  have : HasAdjointNT 2 (λ (g dg : ℝ ⟿ X) => λ x ⟿ g x + dg x) := sorry_proof
  apply scomb_highorder_adjoint (λ g (dg : ℝ ⟿ X) => λ x ⟿ g x + dg x) (λ g => ⅆ g)
  infer_instance


-- set_option trace.Meta.synthPending true in
-- example  (f : ℝ⟿ℝ) : HasAdjointT fun (g : ℝ⟿ℝ) => fun x ⟿ ⟪f x, g x⟫ := by infer_instance


example (D : (ℝ⟿ℝ) → (ℝ⟿ℝ)) [HasAdjointT D] : HasAdjointT fun (g : ℝ⟿ℝ) => fun x ⟿ D g x := by infer_instance
example (D : (ℝ⟿ℝ) → (ℝ⟿ℝ)) [HasAdjointT D] : HasAdjointT fun (g : ℝ⟿ℝ) => fun x ⟿ x * D g x := by infer_instance


set_option synthInstance.maxSize 2000 in
example  (f : ℝ⟿ℝ) : HasAdjointT fun (g : ℝ⟿ℝ) => fun x ⟿ ⟪ⅆ f x, ⅆ g x⟫ := by infer_instance


example  (f : X⟿Y) : (fun (g : X⟿Y) => fun x ⟿ ⟪g x, f x⟫)† = λ h => λ x ⟿ h x * f x := by simp; done
example  (f : X⟿Y) : (fun (g : X⟿Y) => fun x ⟿ ⟪f x, g x⟫)† = λ h => λ x ⟿ h x * f x := by simp; done



-- @[simp ↓, autodiff]
-- theorem smooth_diff_to_normal_diff {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmoothT f]
--   : ∂ (λ x ⟿ f x) = λ x ⟿ λ dx ⊸ ∂ f x dx := by simp[Smooth.differential]; done


-- @[simp ↓, autodiff]
-- theorem smooth_sdif_to_normal_sdiff {X} [Vec X] (f : ℝ → X) [IsSmoothT f]
--   : ⅆ (λ x ⟿ f x) = λ x ⟿ ⅆ f x := by simp[Smooth.differential]; done


set_option synthInstance.maxSize 2000 in
example  (f : ℝ⟿ℝ) : (fun (g : ℝ⟿ℝ) => fun x ⟿ ⟪f x, ⅆ g x⟫)†
                       = 
                       λ h => - (λ x ⟿ ⅆ h x * f x + h x * ⅆ f x) := 
by 
  simp[differentialScalar,tangentMap,Smooth.differential,Smooth.differentialScalar]; done


#check Nat





set_option synthInstance.maxSize 2000 in
example (f : ℝ⟿ℝ) : ∇ (fun (g : ℝ⟿ℝ) => (∫ x, ⟪f x, ⅆ g x⟫))
                      = 
                      (λ g => - ⅆ f) := by simp[variationalGradient, tangentMap,Smooth.differential]; done
  -- simp[differentialScalar,tangentMap,Smooth.differential,Smooth.differentialScalar]; done


#check Nat

example (f : ℝ⟿ℝ) : IsSmoothNT 2 (fun (g : ℝ⟿ℝ) x => ⟪f x, g x⟫) := by infer_instance

set_option synthInstance.maxSize 2000 in
example (f : ℝ⟿ℝ) : IsSmoothNT 2 (fun (g : ℝ⟿ℝ) x => ⟪f x, ⅆ g x⟫) := by infer_instance


set_option trace.Meta.synthInstance true in


def a : IsSmoothT (fun (g : ℝ⟿ℝ) => ⅆ g) := by infer_instance




