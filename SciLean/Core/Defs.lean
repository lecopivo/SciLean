import SciLean.Data.Prod
import SciLean.Core.LinMap
import SciLean.Core.SmoothMap
import SciLean.Core.InvMap

namespace SciLean

open SciLean.Mathlib.Convenient

--- Definitions that need to be given upfroant

section OnPlainVectorSpaces

variable {α β γ : Type _}
variable {K : Type _}
variable {X Y Z : Type _} [Vec K X] [Vec K Y] [Vec K Z] 
variable {Y₁ Y₂ : Type _} [Vec K Y₁] [Vec K Y₂]


-- ∂ 

@[fun_trans_def]
noncomputable 
opaque differential (f : X → Y) (x dx : X) : Y := 
  match Classical.propDecidable (is_smooth f) with
  | isTrue  h => Mathlib.Convenient.derivative f h x dx
  /- For nondifferentiable function the value is not specified.
     Maybe we could assign zero, similarly to division by zero.
     With zero, `differential` might be semilinear in `f`.
     This should be investigated! -/
  | _ => 0

@[fun_trans_def]
noncomputable
def Smooth.differential (f : X ⟿ Y) : (X ⟿ X ⊸ Y) := 
  SmoothMap.mk (λ x => 
    LinMap.mk (λ dx => SciLean.differential f.1 x dx) 
    sorry_proof)
  sorry_proof

@[default_instance]
instance (f : X → Y) : Partial f (differential f) := ⟨⟩
instance (f : X ⟿ Y) : Partial f (Smooth.differential f) := ⟨⟩


-- ⅆ

noncomputable
def differentialScalar (f : ℝ → X) (t : ℝ) : X := 
  differential f t 1

noncomputable
def Smooth.differentialScalar (f : ℝ ⟿ X) : ℝ ⟿ X := 
  SmoothMap.mk (λ t => ((differential f t) 1)) sorry_proof

@[default_instance] 
instance differentialScalar.instDifferentialNotation (f : ℝ → X) 
  : Differential f (differentialScalar f) := ⟨⟩
instance Smooth.differentialScalar.instDifferentialNotation (f : ℝ ⟿ X) 
  : Differential f (Smooth.differentialScalar f) := ⟨⟩


-- 𝒯

@[fun_trans_def]
noncomputable
def tangentMap (f : X → Y) (x dx : X) : Y×Y := (f x, ∂ f x dx)

@[fun_trans_def]
noncomputable
def Smooth.tangentMap (f : X ⟿ Y) : X ⟿ X ⟿ Y×Y := 
  SmoothMap.mk (λ x => 
    SmoothMap.mk (λ dx => (f x, ∂ f x dx))
    (sorry_proof))
  sorry_proof

@[default_instance]
instance (f : X → Y) : TangentMap f (tangentMap f) := ⟨⟩
instance (f : X ⟿ Y) : TangentMap f (Smooth.tangentMap f) := ⟨⟩


end OnPlainVectorSpaces

section OnSemiHilbertSpaces

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] 
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]


-- †

@[fun_trans_def]
noncomputable
def adjoint (f : X → Y) (y : Y) : X :=
  match Classical.propDecidable (has_adjoint f) with
  | isTrue h =>
    let f' := Classical.choose h.has_adjoint
    f' y
  | isFalse _ => 0
  
@[default_instance]
instance (f : X → Y) [SemiHilbert X] [SemiHilbert Y] : Dagger f (adjoint f) := ⟨⟩


-- ∂†

@[fun_trans_def]
noncomputable 
def adjointDifferential (f : X → Y) (x : X) (dy' : Y) : X := (∂ f x)† dy'

@[default_instance]
instance (f : X → Y) : PartialDagger f (adjointDifferential f) := ⟨⟩

@[fun_trans_def]
noncomputable
def Smooth.adjointDifferential (f : X ⟿ Y) : (X ⟿ Y ⊸ X) := 
  SmoothMap.mk (λ x => 
    LinMap.mk (λ dy => SciLean.adjointDifferential f.1 x dy)
    sorry_proof)
  sorry_proof

instance (f : X ⟿ Y) : PartialDagger f (Smooth.adjointDifferential f) := ⟨⟩


-- ℛ

@[fun_trans_def]
noncomputable
def reverseDifferential (f : X → Y) (x : X) : Y×(Y→X) := (f x, λ dy => ∂† f x dy)

instance (priority:=low) (f : X → Y) : ReverseDifferential f (reverseDifferential f) := ⟨⟩


-- ∇

noncomputable
def gradient (f : X → ℝ) (x : X) : X := ∂† f x 1

noncomputable
def Smooth.gradient (f : X ⟿ ℝ) : X⟿X := SmoothMap.mk (λ x => adjoint (λ dx => ∂ f x dx) 1) sorry_proof


@[default_instance]
instance gradient.instNablaNotation (f : X → ℝ) : Nabla f (gradient f) := ⟨⟩
instance Smooth.gradient.instNablaNotation (f : X ⟿ ℝ) : Nabla f (Smooth.gradient f) := ⟨⟩


-- ⁻¹
@[fun_trans_def]
noncomputable 
def invFun {α β} [Nonempty α] (f : α → β) : β → α := Function.invFun f

instance invFun.instInverseNotation {α β} [Nonempty α] (f : α → β) : InverseNotation f (invFun f) := ⟨⟩

-- argmin
noncomputable
opaque argminFun [Nonempty X] (f : X → ℝ) : X 

-- TODO: move to notations
macro " argmin " x:Lean.Parser.Term.funBinder " , " b:term:66 : term => `(argminFun λ $x => $b)

@[app_unexpander argminFun] def unexpandArgmin : Lean.PrettyPrinter.Unexpander
  | `($(_) λ $x => $b) => 
    `(argmin $x, $b)
  | _  => throw ()

@[app_unexpander invFun] def unexpandInvFun : Lean.PrettyPrinter.Unexpander
  | `($(_) $f) => 
    `($f⁻¹)
  | `($(_) $f $x) => 
    `($f⁻¹ $x)
  | _  => throw ()


end OnSemiHilbertSpaces


@[fun_prop_def]
structure HasAdjoint {X Y : Type _} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) : Prop where
  hasAdjoint : has_adjoint f
  isLin : IsLin f
  isSmooth : IsSmooth f

--------------------------------------------------------------------------------

@[fun_prop_def]
structure HasAdjDiff {X Y : Type _} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) : Prop where
  isSmooth : IsSmooth f
  differential_hasAdjoint : ∀ x, HasAdjoint (∂ f x)
