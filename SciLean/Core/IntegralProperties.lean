import SciLean.Core.Integral
import SciLean.Core.CoreFunctions

namespace SciLean

variable {X Y ι : Type} [EnumType ι] [FinVec X ι] [Hilbert Y] [Hilbert Z]

def hasVariationalDual (F : (X ⟿ Y) → Set X → ℝ) 
  := ∃ (f : X ⟿ Y), ∀ Ω (φ : X ⟿ Y), F f Ω = ∫ x∈Ω, ⟪f x, φ x⟫

noncomputable
def variationalDual (F : (X ⟿ Y) → Set X → ℝ) : (X ⟿ Y) := 
  match Classical.dec (hasVariationalDual F) with
  | .isTrue h => Classical.choose h
  | .isFalse _ => 0

instance (F : (X ⟿ Y) → Set X → ℝ) : Dagger F (variationalDual F) := ⟨⟩

@[simp]
theorem variationalDual.arg_F.adjoint_simp (F : (X ⟿ Y) → (X ⟿ ℝ)) -- [inst : HasAdjoint F]
  : (fun f : X ⟿ Y => ∫ x, (F f).1 x)†
    =
    F† 1
  := sorry_proof

instance (priority := low+1) IsSmooth.rule_binop_comp {X Y₁ Y₂ Z} [Vec X] [Vec Y₁] [Vec Y₂] [Vec Z]
  (f : Y₁ → Y₂ → Z) [IsSmooth λ (yy : Y₁×Y₂) => f yy.1 yy.2]
  (g₁ : X → Y₁) [IsSmooth g₁]
  (g₂ : X → Y₂) [IsSmooth g₂]
  : IsSmooth (λ x => f (g₁ x) (g₂ x)) := sorry_proof

instance adjoint.rule_binop {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
  (f : X → Y → Z) [IsSmooth λ (xy : X×Y) => f xy.1 xy.2] [∀ x, HasAdjoint λ y => f x y]
  (g : X → Z) [IsSmooth g] 
  : IsSmooth (λ x => (f x)† (g x)) := sorry_proof



-- theorem IsSmooth.rule_scomb {X Y Z} [Vec X] [Vec Y] [Vec Z]
--   (f : X → Y → Z) [IsSmooth λ (xy : X×Y) => f xy.1 xy.2]
--   (g : X → Y) [IsSmooth g]
--   : IsSmooth (λ x => f x (g x)) := sorry_proof


example (f : X → Y → Z) [IsSmooth fun (xy : X×Y) => f xy.1 xy.2]
  (g : X → Y) [IsSmooth g]
  : IsSmooth λ x => f x (g x) := by infer_instance

@[simp]
theorem adjoint.rule_pi_smooth
  (f : X → Y → Z) [∀ x, HasAdjoint (f x)] [IsSmooth fun (xy : X×Y) => f xy.1 xy.2]
  : (fun (g : X ⟿ Y) => λ (x : X) ⟿ f x (g x))†
    =
    λ g' => λ (x : X) ⟿ (f x)† (g' x) := sorry_proof

@[simp] 
theorem smooth_one_eval {X Y} [Vec X] [Vec Y] (x : X) [One Y]
  : (1 : X ⟿ Y) x = 1 := by rfl


noncomputable 
def Smooth.divergenceDiff (v : X ⟿ X ⊸ Y) := λ x ⟿ - ∑ i, ∂ v x (𝕖' i) (𝕖 i)  

instance (v : X ⟿ X ⊸ Y) : PartialDot v (Smooth.divergenceDiff v) := ⟨⟩


-- This is a component wise formulation of divergence theorem
theorem divergence_theorem (f : X ⟿ ℝ) 
  (Ω : Set X) (S : Set X) -- ∂ Ω = S -- surface of Ω
  (𝕟 : X → X) -- this should be the normal of Ω
  : ∫ x∈Ω, ∂ f x (𝕖 i) 
    =
    ∫ x∈S, f x * ⟪𝕟 x, 𝕖 i⟫ -- not entirelly sure about the projection of the normal, it might be `⟪𝕟 x, 𝕖' i⟫`
  := sorry

@[simp]
theorem Smooth.differential.arg_f.adjoint_simp 
  : (Smooth.differential : (X⟿Y) → (X⟿X⊸Y))†
    =
    - Smooth.divergenceDiff
  := 
by

  -- this is a setup for proving adjoint 
  have Ω : Set X := sorry  -- this should be sufficiently regular, can be even a ball sufficently big to contain support of `v`
  have f : X ⟿ Y := sorry
  have v : X⟿X⊸Y := sorry -- this should be a test function vanishing outside of Ω
  have : ∫ x∈Ω, ⟪∂ f x, v x⟫ = - ∫ x∈Ω, ⟪f x, ∂· v x⟫ := by
   calc 
     ∫ x∈Ω, ⟪∂ f x, v x⟫ = ∫ x∈Ω, ∑ i, ⟪∂ f x (𝕖 i), v x (𝕖' i)⟫ := by sorry

     -- change of notation
     _ = ∫ x∈Ω, ∑ i, ⟪(∂ (x':=x;𝕖 i), f.1 x'), v x (𝕖' i)⟫ := by sorry

     -- product rule for differentiation
     _ = ∫ x∈Ω, ∑ i, (∂ (x':=x;𝕖 i), ⟪f x', v x' (𝕖' i)⟫
                      - 
                      ⟪f x, (∂ (x':=x;𝕖 i), v x' (𝕖' i))⟫) := by sorry 

     -- first therm vanishes by using greens theorem and the fact `v` vanishes on the boundary of Ω
     _ = - ∫ x∈Ω, ∑ i, ⟪f x, (∂ (x':=x;𝕖 i), v x' (𝕖' i))⟫ := by sorry

     -- change of notation and push sum inside
     _ = - ∫ x∈Ω, ⟪f x, ∑ i, (∂ v x (𝕖' i) (𝕖 i))⟫ := by sorry

     -- definition of divergence
     _ = - ∫ x∈Ω, ⟪f x, ∂· v x⟫ := by sorry

  sorry


-- ∂· ∂
-- ∇· ∇

noncomputable
def Smooth.divergenceAdjDiff {Y} {κ} [EnumType κ] [FinVec Y κ] (v : X⟿Y⊸X) :=
  let dv := λ (x : X) (u : X) (u' : Y) => ∂ (x':=x;u), (v.1 x').1 u'
  SmoothMap.mk (λ (x : X) => ∑ (i:κ) (j:ι), 𝕡 j (dv x (𝕖[X] j) (𝕖'[Y] i)) • 𝕖[Y] i) sorry_proof

instance {Y} {κ} [EnumType κ] [FinVec Y κ] (v : X ⟿ Y ⊸ X) : Divergence v (Smooth.divergenceAdjDiff v) := ⟨⟩

noncomputable
def Smooth.divergence (v : X⟿X) :=
  let dv := λ (x : X) (u : X) => ∂ (x':=x;u), v.1 x'
  SmoothMap.mk (λ (x : X) => ∑ (j:ι), 𝕡 j (dv x (𝕖[X] j))) sorry_proof

instance (v : X ⟿ X) : Divergence v (Smooth.divergence v) := ⟨⟩

variable (f : X ⟿ ℝ)


@[simp]
theorem Smooth.adjointDifferential.arg_f.adjoint_simp {Y} {κ} [EnumType κ] [FinVec Y κ]
  : (Smooth.adjointDifferential : (X⟿Y) → (X⟿Y⊸X))†
    =
    - Smooth.divergenceAdjDiff
  := 
by

  -- this is a setup for proving adjoint 
  have Ω : Set X := sorry  -- this should be sufficiently regular, can be even a ball sufficently big to contain support of `v`
  have f : X ⟿ Y := sorry
  have v : X⟿Y⊸X := sorry -- this should be a test function vanishing outside of Ω
  have : ∫ x∈Ω, ⟪∂† f x, v x⟫ = - ∫ x∈Ω, ⟪f x, ∇· v x⟫ := by
   calc 
     ∫ x∈Ω, ⟪∂† f x, v x⟫ = ∫ x∈Ω, ∑ i, ⟪∂† f x (𝕖 i), v x (𝕖' i)⟫ := by sorry

     -- adjoint of differential
     _ = ∫ x∈Ω, ∑ i, ⟪𝕖 i, ∂ f x (v x (𝕖' i))⟫ := by sorry

     -- change of notation
     _ = ∫ x∈Ω, ∑ i, ⟪𝕖 i, (∂ (x':=x;(v x (𝕖' i))), f.1 x')⟫ := by sorry

     -- pull out derivative
     _ = ∫ x∈Ω, ∑ i, ∂ (x':=x;(v x (𝕖' i))), ⟪𝕖 i, f.1 x'⟫ := by sorry

     -- rewrite (v x (𝕖' i)) into a basis
     _ = ∫ x∈Ω, ∑ i j, 𝕡 j (v x (𝕖' i)) * ∂ (x':=x;𝕖 j), ⟪𝕖 i, f.1 x'⟫ := by sorry

     -- product rule for differentiation
     _ = ∫ x∈Ω, ∑ i j, (∂ (x':=x;𝕖 j), 𝕡 j (v x' (𝕖' i)) * ⟪𝕖 i, f.1 x'⟫ 
                        -
                        (𝕡 j (∂ (x':=x;𝕖[X] j), v x' (𝕖' i))) * ⟪𝕖 i, f.1 x⟫) := by sorry

     -- the frist term dissapears thanks to the divergence theorem
     _ = - ∫ x∈Ω, ∑ i j, - (𝕡 j (∂ (x':=x;𝕖[X] j), v x' (𝕖' i))) * ⟪𝕖 i, f.1 x⟫ := by sorry

     -- definition of divergenceAdjDiff + `⟪x,y⟫ = ∑ i, ⟪𝕖' i, x⟫ * ⟪𝕖 i, y⟫`
     _ = - ∫ x∈Ω, ⟪f x, ∇· v x⟫ := by sorry

  sorry


@[simp]
theorem Smooth.gradient.arg_f.adjoint_simp 
  : (Smooth.gradient : (X⟿ℝ) → (X⟿X))†
    =
    - Smooth.divergence
  := sorry_proof


@[simp]
theorem Smooth.differentialScalar.arg_f.adjoint_simp {X} [Hilbert X]
  : (Smooth.differentialScalar : (ℝ⟿X) → (ℝ⟿X))†
    =
    - Smooth.differentialScalar
  := sorry_proof


theorem Smooth.divergence.symmetric_form (v : X ⟿ X ⊸ Y)
  : ∂· v
    =
    λ x ⟿ - ∑ i j, ⟪𝕖'[X] i, 𝕖' j⟫ • ∂ v x (𝕖 i) (𝕖 j)
  := 
by
  -- calc 
  --   𝕖' i = ∑ j, 𝕡 j (𝕖' i) • 𝕖 j   := by FinVec.is_basis (𝕖' i)
  --      _ = ∑ j, ⟪𝕖' j, 𝕖' i⟫ • 𝕖 j := by ← inner_dualBasis_proj
  -- then it is just linearity
  sorry_proof
  
--------------------------------------------------------------------------------
-- Things to get working
--------------------------------------------------------------------------------

variable (f : X ⟿ Y)

#check λ g : X ⟿ Y => λ x ⟿ g x
#check λ g : X ⟿ Y => λ x ⟿ ⟪f x, g x⟫
#check λ g : X ⟿ Y => λ x ⟿ ⟪g x, f x⟫

#check λ g : X ⟿ Y => ∫ x, ⟪g x, f x⟫
#check (λ g : X ⟿ Y => ∫ x, ⟪g x, f x⟫)†
#check (λ g : X ⟿ ℝ => ∫ x, g.1 x)†

example (f : X⟿Y) : (λ g : X⟿Y => ∫ x, ⟪f x, g x⟫)† = f := 
by
  conv => 
    lhs
    rw[variationalDual.arg_F.adjoint_simp (fun g => fun x ⟿ ⟪f x, g x⟫)]
    rw[adjoint.rule_pi_smooth]
    simp only [Inner.inner.arg_a3.adjoint_simp]
    simp

example (f : X⟿Y) : (λ g : X⟿Y => ∫ x, ⟪g x, f x⟫)† = f := 
by
  conv => 
    lhs
    rw[variationalDual.arg_F.adjoint_simp (fun g => fun x ⟿ ⟪g x, f x⟫)]
    rw[adjoint.rule_pi_smooth (λ x y => ⟪y, f x⟫)]
    simp only [Inner.inner.arg_a2.adjoint_simp]
    simp

instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) : HasAdjoint f := sorry_proof

example (f : X⟿Y) : (λ g : X⟿Y => ∫ x, ⟪∂ g x, ∂ f x⟫)† = - ∂· (∂ f) :=
by
  conv => 
    lhs
    rw[variationalDual.arg_F.adjoint_simp (fun g => fun x ⟿ ⟪∂ g x, ∂ f x⟫)]
    rw[adjoint.rule_comp (λ v => λ x ⟿ ⟪v x, ∂ f x⟫) Smooth.differential]
    simp only [adjoint.rule_pi_smooth (λ x y => ⟪y, ∂ f x⟫)]
    simp only [Inner.inner.arg_a2.adjoint_simp]
    simp

example (f : X⟿ℝ) : (λ g : X⟿ℝ => ∫ x, ⟪∇ g x, ∇ f x⟫)† = - ∇· (∇ f) := 
by
  conv => 
    lhs
    rw[variationalDual.arg_F.adjoint_simp (fun (g : X⟿ℝ) => fun x ⟿ ⟪∇ g x, ∇ f x⟫)]
    rw[adjoint.rule_comp (λ v => λ x ⟿ ⟪v x, ∇ f x⟫) Smooth.gradient]
    simp only [adjoint.rule_pi_smooth (λ x y => ⟪y, ∇ f x⟫)]
    simp only [Inner.inner.arg_a2.adjoint_simp]
    simp


noncomputable
def gradientVariational (F : (X⟿Y) → Set X → ℝ) (f : X⟿Y) := (∂ F f)† 

instance (F : (X⟿Y) → Set X → ℝ) : Nabla F (gradientVariational F) := ⟨⟩

@[simp]
theorem gradientVariational_comp (F : (X⟿Y) → (X⟿ℝ))
  : (∇ λ f : X ⟿ Y => ∫ x, (F f).1 x)
    =
    λ f => ∂† F f 1
  := sorry_proof

#check SmoothMap.mk

example (f : X⟿ℝ) : (∇ f' : X⟿ℝ, ∫ x, ‖∇ f x‖²) f = - 2 • ∇· (∇ f) := 
by
  conv => 
    lhs
    rw[gradientVariational_comp (λ f' : X⟿ℝ => λ x ⟿ ‖∇ f x‖²)]
    dsimp



variable (g : X⟿ℝ)
#check (∇ (g' : X⟿ℝ), ∫ x, ‖∇ g' x‖²) g
  


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


@[simp ↓, diff]
theorem elemwise_adjoint_simp {Z} [Hilbert Z] (A : X → Y → Z) [∀ x, HasAdjointT (A x)] [IsSmoothNT 2 A]
  : (λ (g : X⟿Y) => λ x ⟿ A x (g x))†
    =
    λ g => λ x ⟿ (A x)† (g x) := by sorry_proof


instance elemwise_adjoint_alt1 {X Y ι : Type} [EnumType ι] [FinVec X ι] [Hilbert Y]
  {X' Y' ι' : Type} [EnumType ι'] [FinVec X' ι'] [Hilbert Y']
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

@[simp ↓, diff]
theorem elemwise_adjoint_simp_alt1 {X Y ι : Type} [EnumType ι] [FinVec X ι] [Hilbert Y]
  {X' Y' ι' : Type} [EnumType ι'] [FinVec X' ι'] [Hilbert Y']
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

@[simp ↓, diff]
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

instance : HasAdjoint (Smooth.differentialScalar : (ℝ⟿X) → (ℝ⟿X)) := sorry_proof

example  : HasAdjointT fun (g : ℝ⟿Y) => ⅆ g := by infer_instance
example  : HasAdjointT fun (g : ℝ⟿Y) => fun x ⟿ ⅆ g x := by infer_instance


set_option synthInstance.maxSize 20000 in
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
example  (f : ℝ⟿ℝ) : HasAdjointT fun (g : ℝ⟿ℝ) => fun x ⟿ ⟪ⅆ f x, ⅆ g x⟫ := by (try infer_instance); sorry_proof


example  (f : X⟿Y) : (fun (g : X⟿Y) => fun x ⟿ ⟪g x, f x⟫)† = λ h => λ x ⟿ h x * f x := by simp; done
example  (f : X⟿Y) : (fun (g : X⟿Y) => fun x ⟿ ⟪f x, g x⟫)† = λ h => λ x ⟿ h x * f x := by simp; done

example  (f : X⟿Y) : HasAdjointT fun (g : X⟿Y) => fun x ⟿ ⟪f x, g x⟫ := by infer_instance
example  (f : X⟿Y) : HasAdjointT fun (g : X⟿Y) => fun x ⟿ ⟪g x, f x⟫ := by infer_instance
example  (f : X⟿Y) (A : (X⟿Y) → (X⟿Y)) [HasAdjointT A] : HasAdjointT fun (g : X⟿Y) => fun x ⟿ ⟪A g x, f x⟫ := by (try infer_instance); admit
example  (f : X⟿Y) (A : (X⟿Y) → (X⟿Y)) [HasAdjointT A] : HasAdjointT fun (g : X⟿Y) => fun x ⟿ ⟪f x, A g x⟫ := by infer_instance


-- @[simp ↓, diff]
-- theorem smooth_diff_to_normal_diff {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmoothT f]
--   : ∂ (λ x ⟿ f x) = λ x ⟿ λ dx ⊸ ∂ f x dx := by simp[Smooth.differential]; done


-- @[simp ↓, diff]
-- theorem smooth_sdif_to_normal_sdiff {X} [Vec X] (f : ℝ → X) [IsSmoothT f]
--   : ⅆ (λ x ⟿ f x) = λ x ⟿ ⅆ f x := by simp[Smooth.differential]; done




#check Nat





-- set_option synthInstance.maxSize 2000 in
-- example (f : ℝ⟿ℝ) : ∇ (fun (g : ℝ⟿ℝ) => (∫ x, ⟪f x, ⅆ g x⟫))
--                       = 
--                       (λ g => - ⅆ f) := by simp[variationalGradient, tangentMap,Smooth.differential]; done
  -- simp[differentialScalar,tangentMap,Smooth.differential,Smooth.differentialScalar]; done


#check Nat

example (f : ℝ⟿ℝ) : IsSmoothNT 2 (fun (g : ℝ⟿ℝ) x => ⟪f x, g x⟫) := by infer_instance

-- example (f : ℝ⟿ℝ) : IsSmoothNT 2 (fun (g : ℝ⟿ℝ) x => ⟪f x, ⅆ g x⟫) := by infer_instance



-- def a : IsSmoothT (fun (g : ℝ⟿ℝ) => ⅆ g) := by infer_instance





