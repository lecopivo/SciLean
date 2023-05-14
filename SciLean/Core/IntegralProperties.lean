import SciLean.Core.Integral
import SciLean.Core.CoreFunctions
import SciLean.Core.VariationalCalculus
import SciLean.Core.Tactic.FunctionTransformation.Core

namespace SciLean

variable {X Y ι : Type} [EnumType ι] [FinVec X ι] [Hilbert Y] [Hilbert Z]

-- def hasVariationalDual (F : (X ⟿ Y) → Set X → ℝ) 
--   := ∃ (f : X ⟿ Y), ∀ Ω (φ : X ⟿ Y), F f Ω = ∫ x∈Ω, ⟪f x, φ x⟫

-- noncomputable
-- def variationalDual (F : (X ⟿ Y) → Set X → ℝ) : (X ⟿ Y) := 
--   match Classical.dec (hasVariationalDual F) with
--   | .isTrue h => Classical.choose h
--   | .isFalse _ => 0

-- instance (F : (X ⟿ Y) → Set X → ℝ) : Dagger F (variationalDual F) := ⟨⟩

-- @[simp]
-- theorem variationalDual.arg_F.adjoint_simp (F : (X ⟿ Y) → (X ⟿ ℝ)) -- [inst : HasAdjoint F]
--   : (fun f : X ⟿ Y => ∫ x, (F f).1 x)†
--     =
--     F† 1
--   := sorry_proof


-- instance adjoint.rule_binop {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
--   (f : X → Y → Z) [IsSmooth λ (xy : X×Y) => f xy.1 xy.2] [∀ x, HasAdjoint λ y => f x y]
--   (g : X → Z) [IsSmooth g] 
--   : IsSmooth (λ x => (f x)† (g x)) := sorry_proof

  
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

example (f : X⟿Y)
  : HasAdjoint fun (g : X⟿Y) => λ (x : X) ⟿ ⟪f x, g x⟫ := by infer_instance

example (f : X⟿Y) : (λ g : X⟿Y => ∫ x, ⟪f x, g x⟫)† = f := 
by
  conv => 
    lhs
    rw[variationalDual.arg_F.adjoint_simp (fun (g : X⟿Y) => fun x => ⟪f x, g x⟫)]
    rw[adjoint.rule_pi_smooth]
    fun_trans only
    simp

example (f : X⟿Y) : (λ g : X⟿Y => ∫ x, ⟪g x, f x⟫)† = f := 
by
  ignore_fun_prop
  conv => 
    lhs
    rw[variationalDual.arg_F.adjoint_simp (fun g => fun x => ⟪g x, f x⟫)]
    rw[adjoint.rule_pi_smooth (λ x y => ⟪y, f x⟫)]
    fun_trans only
    simp

instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) : HasAdjoint f := sorry_proof


example (f : X⟿Y) : (λ g : X⟿Y => ∫ x, ⟪∂ g x, ∂ f x⟫)† = - ∂· (∂ f) :=
by
  conv => 
    lhs
    rw[variationalDual.arg_F.adjoint_simp (fun g => fun x => ⟪∂ g x, ∂ f x⟫)]
    rw[adjoint.rule_comp (λ v => λ x ⟿ ⟪v x, ∂ f x⟫) Smooth.differential]
    simp only [adjoint.rule_pi_smooth (λ x y => ⟪y, ∂ f x⟫)]
    conv => 
      enter [2]
      fun_trans only
    simp

example (f : X⟿ℝ) : (λ g : X⟿ℝ => ∫ x, ⟪∇ g x, ∇ f x⟫)† = - ∇· (∇ f) := 
by
  conv => 
    lhs
    rw[variationalDual.arg_F.adjoint_simp (fun (g : X⟿ℝ) => fun x => ⟪∇ g x, ∇ f x⟫)]
    rw[adjoint.rule_comp (λ v => λ x ⟿ ⟪v x, ∇ f x⟫) Smooth.gradient]
    simp only [adjoint.rule_pi_smooth (λ x y => ⟪y, ∇ f x⟫)]
    fun_trans only
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

instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) : HasAdjDiff f := sorry_proof
instance {X Y} [Vec X] [Vec Y] (f : X → Y) : IsSmooth f := sorry_proof

theorem SmoothMap.mk.arg_f.pointwise 
  (f : X → Y → Z) [IsSmooth λ (xy : X×Y) => f xy.1 xy.2]
  : (∂† λ (g : X⟿Y) => λ x ⟿ f x (g x))
    =
    λ g dg' => λ x ⟿ ∂† (f x) (g x) (dg' x)
  := sorry

theorem SmoothMap.mk.arg_f.comp {U V} [SemiHilbert U] [SemiHilbert V]
  (g : U → V) [HasAdjDiff g]
  (f : V → X → Y) [IsSmooth λ vx : V×X => f vx.1 vx.2] -- [HasAdjDiff λ v => λ x ⟿ f v x]
  : have : ∀ v, IsSmooth (f v) := sorry_proof
    (∂† λ (u : U) => λ x ⟿ f (g u) x)
    =
    λ u du' => 
      let v := g u
      let df' := ∂† λ v => λ x ⟿ f v x
      let dg' := ∂† g
      dg' u (df' v du')
  := sorry


noncomputable
def hihi (v : X ⟿ X) :=  ∇· v

@[simp]
theorem Smooth.gradient.arg_f.differential_simp
  : ∂ (λ f : X⟿ℝ => ∇ f)
    =
    λ _ df => (gradient df)
  := sorry_proof

@[simp]
theorem Smooth.gradient.arg_f.adjointDifferential_simp
  : ∂† (λ f : X⟿ℝ => ∇ f)
    =
    λ f df' => - Smooth.divergence df' -- for some reason `∇· df'` does not work :(
  := by
  unfold SciLean.adjointDifferential
  simp
  done


@[simp]
theorem Smooth.differential.arg_f.differential_simp {X} [SemiHilbert X]
  : ∂ (λ f : ℝ⟿X => ⅆ f)
    =
    λ _ df => (differentialScalar df) -- for some reason `ⅆ df` does not work :(
  := sorry_proof


#check Smooth.differentialScalar.arg_f.adjoint_simp


@[simp]
theorem Smooth.differential.arg_f.adjointDifferential_simp {X} [Hilbert X]
  : ∂† (λ f : ℝ⟿X => ⅆ f)
    =
    λ _ df => - (differentialScalar df) -- for some reason `ⅆ df` does not work :(
  := by
  unfold SciLean.adjointDifferential
  simp
  done

  
example (f : X⟿ℝ) : (∇ f' : X⟿ℝ, ∫ x, ‖∇ f' x‖²) f = - (2:ℝ) • ∇· (∇ f) := 
by
  conv => 
    lhs
    rw[gradientVariational_comp (λ f' : X⟿ℝ => λ x ⟿ ‖∇ f' x‖²)]
    dsimp
    rw[adjointDifferential.rule_comp (λ (f : X⟿X) => λ x ⟿ ‖f x‖²) Smooth.gradient]
    simp
    rw[SmoothMap.mk.arg_f.pointwise λ x y => ‖y‖²]
    fun_trans only
    simp
  admit -- almost there


theorem adjointDifferential.rule_scomb {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
  (f : X → Y → Z) [HasAdjDiff λ xy : X×Y => f xy.1 xy.2]
  (g : X → Y) [HasAdjDiff g]
  : ∂† (λ x : X => f x (g x))
    =
    λ x dz => 
      let y := g x
      let dx₁ := ∂† (x':=x;dz), f x' y 
      let dy  := ∂† (y':=y;dz), f x y'
      let dx₂ := ∂† g x dy
      dx₁ + dx₂ := sorry

@[simp]
theorem hoho {X} [Vec X] (f : ℝ→X) (h : IsSmooth f) (t : ℝ) : ⅆ (SmoothMap.mk f h) t = ⅆ f t := by rfl

@[simp]
theorem adjDiff_as_gradient {X} [SemiHilbert X] (f : X → ℝ) (x : X) : ∂† f x 1 = ∇ f x := by rfl

example (L : X → X → ℝ) 
  : (∇ x : ℝ⟿X, ∫ t, L (x t) (ⅆ x t)) 
    = λ x => 
      λ t ⟿ ∇ (x':=x t), L x' (ⅆ x t)    -- (∂/∂x L) 
              - ⅆ (t':=t), ∇ (v':=ⅆ x t'), L (x t') v' :=   -- d/dt (∂/∂ẋ L) 
by
  funext x; ext t
  conv => 
    lhs
    rw[gradientVariational_comp (λ x : ℝ⟿X => λ t ⟿ L (x t) (ⅆ x t))]
    dsimp
    
    rw[adjointDifferential.rule_scomb (λ (x : ℝ⟿X) (v : ℝ⟿X) => λ t ⟿ L (x t) (v t)) Smooth.differentialScalar]

    simp (config := {zeta := false})
    conv => 
      simp (config := {zeta := false}) only [SmoothMap.mk.arg_f.pointwise λ t x' => L x' (ⅆ x t)]
      simp (config := {zeta := false}) only [SmoothMap.mk.arg_f.pointwise λ t y => L (x t) y]
    simp [Inner.normSqr.arg_x.adjointDifferential_simp]
  simp
  abel
  done


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





