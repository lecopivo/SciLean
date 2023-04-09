import SciLean.Core.Defs
import SciLean.Core.Diff

namespace SciLean


class LieGroup.SO (G V : Type) [SemiHilbert V] [Group G] extends DistribMulAction G V -- extends Diff G


/--
Shape parametrized by `P` living in `X`
-/
structure Shape {P X} (toSet : P → Set X) where
  params : P  
  -- add some niceness properties 
  --  - probably that it is a closed set
  --  - compactness is probably too restrictive

namespace Shape

  variable {P X : Type} [Hilbert X] {p : P → Set X}


  ------------------------------------------------------------------------------
  -- Locate
  ------------------------------------------------------------------------------
  inductive Location | inside | boundary | outside 

  noncomputable 
  def locateSpec (s : Shape p) (x : X) : Location := sorry
    -- if x ∈ interior s then
    --   inside
    -- else if x ∈ univ ∖ closure s
    --   outside
    -- else
    --   boundary

  class IsLocate (f : Shape p → X → Location) where
    is_locate : locateSpec = f

  class HasLocate (p : P → Set X) where
    locate : Shape p → X → Location
    is_locate : IsLocate locate

  def locate [HasLocate p] (s : Shape p) (x : X) := HasLocate.locate s x

  instance [HasLocate p] : IsLocate (locate (p:=p)) := HasLocate.is_locate 
  @[simp] theorem locate_spec [IsLocate f]
    : locateSpec = f := IsLocate.is_locate

  ------------------------------------------------------------------------------
  -- Level Set 
  ------------------------------------------------------------------------------
  class IsLevelSet (f : Shape p → X → ℝ) where
    is_level_set : ∀ (s : Shape p), 
      if f s x < 0 then
        s.locateSpec x = inside
      else if f s x = 0 then
        s.locateSpec x = boundary
      else 
        s.locateSpec x = outside

  class HasLevelSet (p : P → Set X) where
    levelSet : Shape p → X → ℝ
    is_level_set : IsLevelSet levelSet

  def levelSet [HasLevelSet p] (s : Shape p) (x : X) := HasLevelSet.levelSet s x

  instance [HasLevelSet p] : IsLevelSet (levelSet (p:=p)) := HasLevelSet.is_level_set


  ------------------------------------------------------------------------------
  -- Signed Distance Function
  ------------------------------------------------------------------------------
  -- TODO: This should map to `ℝ∪{∞}∪{-∞}` to allow for empty space and total space
  noncomputable 
  def sdfSpec (s : Shape p) (x : X) : ℝ := sorry
    -- match s.locateSpec with
    -- | inside => - dist(x, boundary s)
    -- | outside =>  dist(x, boundary s)
    -- | boundary => 0

  class IsOutsideDist (f : Shape p → X → ℝ) where
    is_outside_dist : ∀ s x,
      0 ≤ f s x → s.sdfSpec x = f s x

  class IsInsideDist (f : Shape p → X → ℝ) where
    is_inside_dist : ∀ s x,
      f s x ≤ 0 → s.sdfSpec x = f s x

  class IsSdf (f : Shape p → X → ℝ) extends IsOutsideDist f, IsInsideDist f

  class HasSdf (p : P → Set X) where
    sdf (s : Shape p) (x : X) : ℝ
    is_sdf : IsSdf sdf

  def sdf [HasSdf p] (s : Shape p) (x : X) := HasSdf.sdf s x

  
  instance [HasSdf p] : IsSdf (sdf (p:=p)) := HasSdf.is_sdf
  instance (f : Shape p → X → ℝ) [IsSdf f] : IsLevelSet f := sorry

  @[simp] theorem sdf_spec (f : Shape p → X → ℝ) [IsSdf f]
    : sdfSpec = f := sorry_proof


  ------------------------------------------------------------------------------
  -- Distance between two shapes
  ------------------------------------------------------------------------------
  noncomputable
  def distSpec (A : Shape p) (B : Shape q) : ℝ := sorry
    -- if disjoint A B then
    --   sup (x ∈ A), inf (y ∈ B), dist x y
    -- else
    --   - min (sup (x ∈ A∩B) (inf (y ∈ ∂B), dist x y))
    --         (sup (x ∈ A∩B) (inf (y ∈ ∂A), dist x y))

  class HasDist (p : P → Set X) (q : Q → Set X) where
    dist (A : Shape p) (B : Shape q) : ℝ 
    is_dist : ∀ A B, distSpec A B = dist A B

  def dist [HasDist p q] (A : Shape p) (B : Shape q) : ℝ := HasDist.dist A B
  @[simp] theorem dist_spec [HasDist p q] (A : Shape p) (B : Shape q)
    : distSpec A B = dist A B := by apply HasDist.is_dist
  

  ------------------------------------------------------------------------------
  -- Shape Transform
  ------------------------------------------------------------------------------
  class HasTransform (p : P → Set X) (f : X → X) where
    trans : P → P
    is_trans : sorry -- the new shape is f(A)

  def trans (f : X → X) [HasTransform p f] (s : Shape p) : Shape p := ⟨HasTransform.trans p f s.params⟩

  -- Common transformations
  abbrev HasReflect (p : P → Set X) := HasTransform p Neg.neg
  abbrev HasTranslate (p : P → Set X) := ∀ t, HasTransform p λ x => x + t
  abbrev HasRotate (p : P → Set X) (R : Type) [Group R] [LieGroup.SO R X] 
    := ∀ r : R, HasTransform p λ x => r • x
  abbrev HasMirror (p : P → Set X) := ∀ n : X, HasTransform p λ x => x - ((2 : ℝ) * ⟪x,n⟫) • n

  abbrev reflect [HasReflect p] (s : Shape p) := s.trans Neg.neg
  abbrev translete [HasTranslate p] (s : Shape p) (t : X) := s.trans λ x => x + t
  abbrev rotate {R : Type} [Group R] [LieGroup.SO R X] [HasRotate p R] 
    (s : Shape p) (r : R) := s.trans λ x => r • x 
  abbrev mirror [HasMirror p] (s : Shape p) (n : X) := s.trans λ x => x - ((2 : ℝ) * ⟪x,n⟫) • n

  class HasRigidTransform (p : P → Set X) (R : Type) [Group R] [LieGroup.SO R X] where
    hasTranslate : HasTranslate p
    hasRotate : HasRotate p R

  instance {R : Type} [Group R] [LieGroup.SO R X] [inst : HasRigidTransform p R] 
    : HasTranslate p := inst.hasTranslate
  instance {R : Type} [Group R] [LieGroup.SO R X] [inst : HasRigidTransform p R] 
    : HasRotate p R := inst.hasRotate


  ------------------------------------------------------------------------------
  -- Minkowski Sum
  ------------------------------------------------------------------------------
  class HasMinkowskiSum (p : P → Set X) (q : Q → Set X) (r : outParam $ R → Set X) where
    sum : P → Q → R
    is_sum : sorry

end Shape
