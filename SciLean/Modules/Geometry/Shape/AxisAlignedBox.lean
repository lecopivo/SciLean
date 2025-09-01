import SciLean.Core
import SciLean.Modules.Geometry.Shape
import SciLean.Modules.Geometry.Shape.Sphere

open FiniteDimensional

namespace SciLean

namespace Shape

variable
  {R : Type _} [RealScalar R] [PlainDataType R]
  {ι : Type _} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {X : Type _} [FinVec ι R X] [PlainDataType X]
  {Y : Type _} [SemiHilbert R Y]
  {S : Type _} [Shape S X]

set_default_scalar R

instance : GetElem X ι R (fun _ _ => True) where
  getElem x i _ := ℼ i x

instance : GetElem X ℕ R (fun _ i => i < IndexType.card ι) where
  getElem x i h := ℼ (IndexType.fromFin ⟨i,h⟩) x


variable (X)
structure AxisAlignedBox where
  min : X
  max : X
  deriving Inhabited, Repr
variable {X}


instance : Shape (AxisAlignedBox X) X where
  toSet b x := ∀ (i : ι), 0 ≤ (x[i] - b.min[i]) ∧ 0 ≤ (b.max[i] - x[i])


instance (b : AxisAlignedBox X) (x : X) : Decidable (x ∈ toSet b) := by
  simp[toSet, Membership.mem, Set.Mem]; infer_instance


instance : Locate (AxisAlignedBox X) where
  locate b x := Id.run do
    let mut loc : Location := .inside
    for i in IndexType.univ ι do
      let xi := x[i]
      if xi < b.min[i] || b.max[i] < xi then
        return .outside
      if xi = b.min[i] || xi = b.max[i] then
        loc := .boundary
    return loc

  is_locate := sorry_proof



class BoundingBox
    {R : Type _} [RealScalar R]
    {ι : Type _} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
    {X : Type _} [FinVec ι R X]
    (S : Type _) [Shape S X] where
  boundingBox (s : S) : AxisAlignedBox X
  is_bounding_box : ∀ s : S,
    let b := boundingBox s
    -- is bounding
    toSet s ⊆ toSet b
    ∧
    -- is minimal
    ∀ (b' : AxisAlignedBox X), toSet s ⊆ toSet b' → toSet b ⊆ toSet b'


-- export BoundingBox (boundingBox)
abbrev boundingBox [BoundingBox S] (s : S) := BoundingBox.boundingBox R ι s

instance : BoundingBox (AxisAlignedBox X) where
  boundingBox b := b
  is_bounding_box := sorry_proof


instance [OrthonormalBasis ι R X] : BoundingBox (Sphere R X) where
  boundingBox s := {
    min := s.center - s.radius • ∑ i, ⅇ i,
    max := s.center + s.radius • ∑ i, ⅇ i }
  is_bounding_box := sorry_proof


instance [OrthonormalBasis ι R X]: BoundingBox (Ball R X) where
  boundingBox s := {
    min := s.center - s.radius • ∑ i, ⅇ i,
    max := s.center + s.radius • ∑ i, ⅇ i }
  is_bounding_box := sorry_proof


instance [OrthonormalBasis ι R X] : BoundingSphere (AxisAlignedBox X) where
  boundingSphere b :=
    { center := (0.5:R) • (b.min + b.max), radius := ‖b.max - b.min‖₂/2 }
  is_bounding_sphere := sorry_proof
