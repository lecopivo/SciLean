import SciLean.Data.Mesh.Prism

namespace SciLean

namespace Prism


-- /-- Finds a closest point on a triangle.

-- The result is a pair:
--   1. element is point,segment or triangle
--   2. element is position of the closets point in the local coordinates
-- -/
def closestOnTriangle (x : ℝ^{2}) (fromRef toRef : ℝ^{2} → ℝ^{2}) : (f : Face triangle) × ℝ^{f.dim} :=
  let y := toRef x
  let y₀ := y[0]
  let y₁ := y[1]
  let e₀ : ℝ^{2} := ⟨1,0⟩
  let e₁ : ℝ^{2} := ⟨0,1⟩
  let p₀ : ℝ^{2} := 0
  let p₁ : ℝ^{2} := fromRef e₀
  let p₂ : ℝ^{2} := fromRef e₁

  if y₁ ≤ 0 then
    let d₁₀ := p₁ - p₀
    let d₁₀ := (1/∥d₁₀∥)*d₁₀
    let t := ⟪x - p₀, d₁₀⟫

    if t ≤ 0 then
      -- point 0
      Sigma.mk triangle.point0.toFace 0
    else if 1 ≤ t then
      -- point 1
      Sigma.mk triangle.point1.toFace 0
    else
      -- edge 0
      let t : ℝ^{1} := λ [i] => t
      Sigma.mk triangle.edge0.toFace t
  else if y₀ ≤ 0 then

    let d₂₀ := p₂ - p₀
    let d₂₀ := (1/∥d₂₀∥)*d₂₀
    let t := ⟪x - p₀, d₂₀⟫

    if t ≤ 0 then
      -- point 0
      Sigma.mk triangle.point0.toFace 0
    else if 1 ≤ t then
      -- point 2
      Sigma.mk triangle.point2.toFace 0
    else
      -- edge 1
      let t : ℝ^{1} := λ [i] => t
      Sigma.mk triangle.edge1.toFace t
  else if 0 ≤ y₁ + y₀ - 1 then
    let d₂₁ := p₂ - p₁
    let d₂₁ := (1/∥d₂₁∥)*d₂₁
    let t := ⟪x - p₁, d₂₁⟫

    if t ≤ 0 then
      -- point 1
      Sigma.mk triangle.point1.toFace 0
    else if 1 ≤ t then
      -- point 2
      Sigma.mk triangle.point2.toFace 0
    else
      -- edge 2
      let t : ℝ^{1} := λ [i] => t
      Sigma.mk triangle.edge2.toFace t
  else
    Sigma.mk triangle.topFace y


/-- Finds the closest point to `x` on the prism `P` that is linearly deformed by `fromRef`

The output is pair (f, y) where `f` is the face of `P` on which the closest point lies and `y` is the location of the closets poin in local coordinates
-/
def closestPoint (P : Prism) (x : P.Space) (fromRef toRef : P.Space → P.Space) : (f : Face P) × ℝ^{f.dim} :=
  match P with
  | ⟨.point, _⟩ =>
    Sigma.mk ⟨.point, sorry_proof, sorry_proof⟩ 0

  | ⟨.cone .point, _⟩ =>
    let y : ℝ^{1} := toRef x
    if y[0] ≤ 0 then
      Sigma.mk segment.point0.toFace.anyDim 0
    else if 1 ≤ y[0] then
      Sigma.mk segment.point1.toFace.anyDim 0
    else
      Sigma.mk segment.topFace.anyDim y

  | ⟨.cone (.cone .point), _⟩ => closestOnTriangle x fromRef toRef

  | _ => panic! s!"Closest point is not implemented for prism {P}!"

-- def closestOnSegment (x : ℝ) (fromRef toRef : ℝ^
