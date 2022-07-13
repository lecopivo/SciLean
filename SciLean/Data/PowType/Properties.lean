import SciLean.Data.PowType.Algebra
import SciLean.Core.Functions

namespace SciLean.PowType

function_properties powType.getOp {X} [PowType X] {n : Nat} (x : X^n) (i : Idx n) : X
argument x [Vec X]
  isLin    := sorry,
  isSmooth := sorry,
  diff_simp := dx[i] by sorry
argument x [SemiHilbert X]
  hasAdjoint := sorry,
  adj_simp := (0 : X^n).set i x' by sorry,
  hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
  adjDiff_simp := (0 : X^n).set i dx' by simp[adjDiff]; unfold hold; simp done

instance powType.getOp.arg_xi.hasAdjDiff {X} [SemiHilbert X] [PowType X] {n : Nat} 
  : HasAdjDiff (λ (x : X^n) i => x[i]) := sorry
@[simp] theorem powType.getOp.arg_xi.adjDiff {X} [SemiHilbert X] [PowType X] {n : Nat} 
  : ∂† (λ (x : X^n) i => x[i]) = λ x dx' => PowType.intro dx' := sorry

function_properties powType.set {X} [PowType X] {n : Nat} (x : X^n) (i : Idx n) (xi : X) : X^n
argument x [Vec X]
  isSmooth  := sorry,
  diff_simp := dx.set i 0 by sorry
argument x [SemiHilbert X]
  hasAdjoint [Fact (xi=0)] := sorry,
  adj_simp   [Fact (xi=0)] := x'.set i 0 by sorry,
  hasAdjDiff   := by constructor; infer_instance; simp; infer_instance done,
  adjDiff_simp := dx'.set i 0 by simp[adjDiff]; unfold hold; simp done

argument xi [Vec X]
  isSmooth  := sorry,
  diff_simp := (0 : X^n).set i dxi by sorry
argument xi [SemiHilbert X]
  hasAdjoint [Fact (x=0)] := sorry,
  adj_simp   [Fact (x=0)] := xi'[i] by sorry,
  hasAdjDiff   := by constructor; infer_instance; simp; infer_instance done,
  adjDiff_simp := dxi'[i] by simp[adjDiff] done

function_properties PowType.intro {X} [PowType X] {n : Nat} (f : Idx n → X) : X^n
argument f [Vec X]
  isLin := sorry,
  isSmooth := sorry,
  diff_simp := intro df by sorry
argument f [SemiHilbert X]
  hasAdjoint := sorry,
  adj_simp :=  λ i => f'[i] by sorry,
  hasAdjDiff := sorry,
  adjDiff_simp := λ i => df'[i] by sorry

-- set_option pp.all true in
example {X} [PowType X] [Vec X] {n} {i : Idx n}: IsSmooth λ (x : X^n) => x[i] := by infer_instance
-- instance : IsSmooth   (λ (c : X^n) (i : Fin n)  => c[i]) := sorry
-- instance : IsLin      (λ (c : X^n) (i : Fin n)  => c[i]) := sorry
-- -- instance (i : Fin n) : IsSmooth   (λ c : X^n => c[i]) := by infer_instance
-- -- instance (i : Fin n) : IsLin      (λ c : X^n => c[i]) := by infer_instance

-- @[simp]
-- theorem diff_of_powtype_getOp
--   : ∂ (λ (x : X^n) (i : Fin n) => x[i]) = λ x dx i => dx[i] := sorry

-- variable [Hilbert X]
-- instance : HasAdjoint (λ (c : X^n) (i : Fin n) => c[i]) := sorry
-- -- instance (i : Fin n) : HasAdjoint (λ c : X^n => c[i]) := by infer_instance

-- @[simp]                         
-- theorem adjoint_of_powtype_get
--   : (λ (c : X^n) i => c[i])† = PowType.intro := sorry
