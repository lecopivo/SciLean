import SciLean.Mathlib.Data.Enumtype
import SciLean.Algebra.Real

namespace SciLean

inductive Prism where
  | point : Prism
  | cone (P : Prism) : Prism
  | prod (P Q : Prism) : Prism

namespace Prism

  def faceCount (P : Prism) (n : Nat) : Nat :=
    match P with
      | point => if n == 0 then 1 else 0
      | cone P => 
        match n with
          | 0   => 1 + P.faceCount 0
          | n+1 => P.faceCount n + P.faceCount (n+1)
      | prod P Q => ∑ i : Fin (n+1), (P.faceCount i.1) * (Q.faceCount (n-i.1))

  def dim : (P : Prism) → Nat
    | point => 0
    | cone P' => 1 + P'.dim
    | prod P' Q' => P'.dim + Q'.dim

  inductive Face : Prism → Nat → Type where
    | point : Face point 0
    | tip (P : Prism) : Face (cone P) 0
    | cone {n} {P : Prism} (f : Face P n) : Face (cone P) (n+1)
    | base {n} {P : Prism} (f : Face P n) : Face (cone P) n
    | prod {n m} {P Q : Prism} (f : Face P n) (g : Face Q m) 
      : Face (prod P Q) (n + m) 

  def Face.toPrism {P n} (f : Face P n) : Prism :=
    match f with
      | point => Prism.point
      | tip P  => Prism.point
      | cone f => Prism.cone f.toPrism
      | base f => f.toPrism
      | prod f g => Prism.prod f.toPrism g.toPrism

  def Face.ofFace' {P Q : Prism} {n m : Nat} : (f : Face P n) → (g : Face Q m) → (h : f.toPrism = Q) → Face P m
    |   point,   point, _ => point
    |  tip P',   point, _ => tip P'
    | cone f',   tip _, _ => tip _
    | cone f', cone g', h => cone (ofFace' f' g' (by simp[toPrism] at h; apply h))
    | cone f', base g', h => base (ofFace' f' g' (by simp[toPrism] at h; apply h))
    | base f',      g', h => base (ofFace' f' g' (by simp[toPrism] at h; apply h))
    | prod f' f'', prod g' g'', h => prod (ofFace' f' g' (by simp[toPrism] at h; apply h.1)) 
                                          (ofFace' f'' g'' (by simp[toPrism] at h; apply h.2))

  def Face.ofFace {P n m} {f : Face P n} (g : Face (f.toPrism) m) : Face P m
    := ofFace' f g (by rfl)

  def Face.first (P : Prism) (n : Nat) : Option (Face P n) := sorry
  def Face.next {P n} (f : Face P n) : Option (Face P n) := sorry
  def Face.toFin {P n} (f : Face P n) : Fin (P.faceCount n) := sorry
  def Face.fromFin (P : Prism) (n : Nat) (i : Fin (P.faceCount n)) : Face P n := sorry

  def segment  := cone point
  def triangle := cone segment
  def square   := prod segment segment
  def tet      := cone triangle
  def cube     := prod segment square
  def pyramid  := cone square
  def prism    := prod segment triangle

  -- Natural embedding space
  def E : (P : Prism) → Type
    | point => Unit
    | cone P' => ℝ × P'.E
    | prod P' Q' => P'.E × Q'.E

  def pointCount (P : Prism) : Nat := P.faceCount 0

  def pos' {P : Prism} : Face P 0 → P.E := sorry
  -- def pos {P : Prism} : Fin (P.pointCount) → ℝ^P.dim := sorry

  -- def toRn : {P : Prism} → P.E → ℝ^P.dim := sorry
  -- def fromRn : {P : Prism} → ℝ^P.dim → P.E := sorry

  def barycentricCoord' {P : Prism} : Face P 0 → P.E → ℝ := sorry
  -- def barycentricCoord {P : Prism} : Fin (P.pointCount) → ℝ^P.dim → ℝ := sorry
