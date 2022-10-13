import SciLean.Core
import SciLean.Data.GenericArray
import SciLean.Data.FunRec
import SciLean.Tactic.ConvIf
import SciLean.Meta.DerivingOp
import SciLean.Meta.DerivingAlgebra

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

/-- Bezier curve evaluation satisfy a recursive formula -/
def eval_rec [Vec X] (points : Points (n + 2)) (t : ℝ)
  : 
    let P₀ : Points (n+1) := λ [i] => points[⟨i.1, sorry_proof⟩]
    let P₁ : Points (n+1) := λ [i] => points[⟨i.1+1, sorry_proof⟩]
    eval points t = (1-t) * eval P₀ t + t * eval P₁ t 
  := sorry_proof

end Bezier

structure BezierCurve {T : Nat → Type} (X : Type) [Vec X] [LinearPowType T X] (deg : Nat) where
  points : X^{deg + 1}
deriving Vec


structure Vec3 where
  (x y z : ℝ)
deriving Vec, Mul, Div

instance : ToString Vec3 := ⟨λ v => s!"({v.x}, {v.y}, {v.z})"⟩

#eval (10 : ℝ) * Vec3.mk 1 2 3 / Vec3.mk 100 200 300

#check instAddSemigroupBezierCurve

namespace BezierCurve 

variable {T : Nat → Type} {X : Type} [Vec X] [LinearPowType T X] {deg}

abbrev intro (f : Fin (deg + 1) → X) : BezierCurve X deg := ⟨λ [i] => f i⟩
instance : CoeFun (BezierCurve X deg) (λ _ => ℝ → X) := ⟨λ γ => Bezier.eval γ.points⟩

instance (γ : BezierCurve X deg) : IsSmooth (λ t => γ t) := by infer_instance

end BezierCurve
