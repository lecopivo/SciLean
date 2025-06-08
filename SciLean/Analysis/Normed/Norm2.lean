import Mathlib.Analysis.InnerProductSpace.Basic

import SciLean.Analysis.Scalar.Basic

namespace SciLean

open RCLike ComplexConjugate

/-- Square of L₂ norm over the field `K` -/
class Norm2 (K X : Type _) where
  norm2 : X → K

-- TODO: remove this instance and add coherency class saying that `‖x‖₂ = ⟪x,x⟫`
instance [Inner K X] : Norm2 K X where
  norm2 x := Inner.inner K x x

macro "‖" x:term "‖₂²[" K:term "]" : term => `(@Norm2.norm2 $K _ _ $x)
macro "‖" x:term "‖₂²" : term => `(@Norm2.norm2 defaultScalar% _ _ $x)

@[app_unexpander Norm2.norm2] def unexpandNorm2 : Lean.PrettyPrinter.Unexpander
  | `($(_) $x) => `(‖ $x ‖₂²)
  | _ => throw ()


theorem norm2_def [Inner K X] (x : X) : ‖x‖₂²[K] = Inner.inner K x x := by rfl

def norm₂ (K : Type _) {R X : Type _} [Scalar R K] [Norm2 K X] (x : X) : K := Scalar.sqrt (Norm2.norm2 x)

macro "‖" x:term "‖₂[" K:term "]" : term => `(norm₂ $K $x)
macro "‖" x:term "‖₂" : term => `(norm₂ defaultScalar% $x)

@[app_unexpander norm₂] def unexpandNorm₂ : Lean.PrettyPrinter.Unexpander
  | `($(_) $_ $x) => `(‖ $x ‖₂)
  | _ => throw ()

@[simp, simp_core]
theorem norm₂_squared_nat {R K X : Type _} [Scalar R K] [Norm2 K X] (x : X)
  : ‖x‖₂[K] ^ 2 = ‖x‖₂²[K] := by sorry_proof

@[simp, simp_core]
theorem norm₂_squared {R K X : Type _} [Scalar R K] [Norm2 K X] (x : X)
  : ‖x‖₂[K] ^ (2:K) = ‖x‖₂²[K] := by sorry_proof

@[simp, simp_core]
theorem scalar_norm {R} [RealScalar R] (r : R) : ‖r‖₂[R] = Scalar.abs r := by sorry_proof

section Inner

macro "⟪" x:term ", " y:term "⟫[" K:term "]" : term => `(@Inner.inner $K _ _ $x $y)
macro "⟪" x:term ", " y:term "⟫" : term => `(@Inner.inner defaultScalar% _ _ $x $y)

@[app_unexpander Inner.inner] def unexpandInner : Lean.PrettyPrinter.Unexpander
  | `($(_) $_ $x $y) => `(⟪$x, $y⟫)
  | _ => throw ()


instance (K X Y) [Add K] [Inner K X] [Inner K Y] : Inner K (X × Y) where
  inner := λ (x,y) (x',y') => ⟪x,x'⟫[K] + ⟪y,y'⟫[K]

theorem _root_.Prod.inner_def (K X Y) [Add K] [Inner K X] [Inner K Y] (x y : X×Y) :
    ⟪x,y⟫[K] = ⟪x.1,y.1⟫[K] + ⟪x.2,y.2⟫[K] := by rfl

@[simp, simp_core]
theorem norm₂_prod {R K X Y} [Scalar R K] [AddCommMonoid K] [Inner K X] [Inner K Y] (x : X) (y : Y) :
  ‖(x,y)‖₂[K] = Scalar.sqrt (‖x‖₂²[K] + ‖y‖₂²[K]) := by sorry_proof

@[simp, simp_core]
theorem norm₂_scalar {R} [RealScalar R] (x : R) :
  ‖x‖₂[R] = Scalar.abs x := by sorry_proof

@[simp, simp_core]
theorem norm2_scalar {R} [RealScalar R] (x : R) :
  ‖x‖₂²[R] = x^2 := by sorry_proof

-- instance (priority:=low) (K ι) (X : ι → Type _)
--   [AddCommMonoid K] [∀ i, Inner K (X i)] [IndexType ι]
--   : Inner K ((i : ι) → X i) where
--   inner := λ f g => ∑ i, ⟪f i, g i⟫[K]

end Inner
