import SciLean.Core.Integral
import SciLean.Core.CoreFunctions
import SciLean.Core.VariationalCalculus
import SciLean.Core.Tactic.FunctionTransformation.Core

namespace SciLean

variable {X Y ι : Type} [EnumType ι] [FinVec X ι] [Hilbert Y] [Hilbert Z]
  
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
    λ f df' => - divergenceSmooth df' -- for some reason `∇· df'` does not work :(
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


