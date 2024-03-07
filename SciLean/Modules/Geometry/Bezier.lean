import SciLean.Core
import SciLean.Data.GenericArray
import SciLean.Data.FunRec
import SciLean.Tactic.ConvIf
import SciLean.Meta.DerivingOp
import SciLean.Meta.DerivingAlgebra
import SciLean.Solver.Solver

namespace SciLean

namespace Bezier

variable {X : Type}
variable {Points : Nat → Type} [GenericLinearArray Points X]

open GenericArray



/-- `k`-th derivative of a bezier curve with `n+k` points is just a bezier curve with `n` points

This function computes those `n` points.-/
def derivativePoints [Vec X] {n} (k : Nat) (points : Points (k+n)) : Points n :=
  let fₙ : (n' : Nat) → Points (n'+1) → Points n' :=
    λ n' pts => upper2DiagonalUpdate (λ _ => n') (λ _ => -n') pts |> dropElem 1
  funRevRec k n fₙ points
argument points
  isLin, isSmooth, diff_simp

function_properties derivativePoints [SemiHilbert X] {n} (k : Nat) (points : Points (k+n)) : Points n
argument points
  hasAdjoint, adj,
  hasAdjDiff := by constructor; infer_instance; simp; infer_instance,
  adjDiff_simp by simp[adjointDifferential]

/-- Evaluate k-th derivative of a Bezier curve given by `n` points `points` -/
def evalDer [Vec X] {n} (k : Nat) (points : Points n) (t : ℝ) : X :=
  let n' := n - k - 1
  if h : n = k + (n' + 1) then
    let points' : Points (n' + 1) := derivativePoints k (h ▸ points)
    let fₙ : (n' : Nat) → Points (n'+1) → Points n' :=
      λ _ pts => linearInterpolate t pts
    (funRevRec n' 1 fₙ points')[0]
  else
    0
argument points
  isLin := sorry_proof,
  isSmooth, diff_simp
argument t
  isSmooth := sorry_proof,
  diff := dt * evalDer (k+1) points t by sorry_proof

abbrev eval [Vec X] {n} (points : Points n) (t : ℝ) : X := evalDer 0 points t

def split [Vec X] {n} (points : Points n) (t : ℝ) : Points n × Points n :=
  let fₙ :  (n' : Nat) → Points (n - n') × Points n' × Points n'
                       → Points (n - (n' + 1)) × Points (n' + 1) × Points (n' + 1) :=
      λ n' (pts, startPts, endPts) =>
        -- This is effectivelly asking if `0 < n - n'` but in a form that is usefully for typecasting
        if h : n - n' = (n - (n' + 1) + 1) then
          -- In this case pts should have at least one element
          let first := pts[⟨0, sorry_proof⟩]
          let last  := pts[⟨n - n' - 1, sorry_proof⟩]
          (linearInterpolate t (h ▸ pts), pushElem 1 first startPts, pushElem 1 last endPts)
        else
          -- it should be the case that `n - n' = 0`
          -- thus `h'` should be saying 0 = 0
          have h' : (n - n') = (n - (n' + 1)) := sorry_proof
          -- `pts` is an empty array, so just push 0 vectors to startPts and endPts
          ((h' ▸ pts), pushElem 1 0 startPts, pushElem 1 0 endPts)

  let (_, startPts, endPts) := (funRec n 0 fₙ (points, reserveElem n 0, reserveElem n 0))
  (startPts, reverse endPts)


/-- Bezier curve evaluation satisfy a recursive formula -/
def eval_rec [Vec X] (points : Points (n + 2)) (t : ℝ)
  :
    let P₀ : Points (n+1) := λ [i] => points[⟨i.1, sorry_proof⟩]
    let P₁ : Points (n+1) := λ [i] => points[⟨i.1+1, sorry_proof⟩]
    eval points t = (1-t) * eval P₀ t + t * eval P₁ t
  := sorry_proof


section BezierCurvesOfReals

-- TODO: Replace with ℝ^{n} I do not think there is a good argument for using a generic array
variable {RealPoints : Nat → Type} [GenericLinearArray RealPoints ℝ]

/-- Finds all roots of a polynomial `p` in the interval `[a, b]`.-/
noncomputable
def Polynomial.roots (p : ℝ → ℝ) (a b : ℝ) /- [IsPol f] -/ : Array ℝ := sorry

/-- Finds all roots in [0,1] interval of a Bezier curve -/
noncomputable
def roots {n} (points : RealPoints n) : Array ℝ := Polynomial.roots (eval points) 0 1

/-- Approximation of `roots` -/
noncomputable
approx roots_approx := λ {n} (weights : RealPoints n) => roots weights
by
  simp

/-- Finds all points in [0,1] of a Bezier curve that have zero derivative -/
noncomputable
def extremalPoints {n} (weights : RealPoints n) : Array ℝ := sorry

/-- Approximation of `roots` -/
noncomputable
approx extremalPoints_approx := λ {n} (weights : RealPoints n) => extremalPoints weights
by
  simp

end BezierCurvesOfReals


end Bezier

structure BezierCurve {T : Nat → Type} (X : Type) [Vec X] [LinearPowType T X] (deg : Nat) where
  points : X^{deg + 1}
deriving Vec

namespace BezierCurve

variable {T : Nat → Type} {X : Type} [Vec X] [LinearPowType T X] {deg}

abbrev intro (f : Fin (deg + 1) → X) : BezierCurve X deg := ⟨λ [i] => f i⟩
instance : CoeFun (BezierCurve X deg) (λ _ => ℝ → X) := ⟨λ γ => Bezier.eval γ.points⟩

instance (γ : BezierCurve X deg) : IsSmooth (λ t => γ t) := by infer_instance

end BezierCurve
