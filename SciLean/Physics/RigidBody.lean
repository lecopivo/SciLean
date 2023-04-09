import SciLean.Core.Defs
import SciLean.Core.Diff

import SciLean.Meta.DerivingAlgebra
import SciLean.Core.DifferentialDep

namespace SciLean


class LieGroup.SO (G V : Type) [SemiHilbert V] [Group G] extends DistribMulAction G V -- extends Diff G


/--
Shape parametrized by `P` living in `X`
-/
structure Shape {P X} (toSet : P → Set X) where
  params : P  
  -- add some niceness properties - probably a compactness

namespace Shape

  variable {P X : Type} [Hilbert X] {p : P → Set X}

  -- Locate
  inductive Location | outside | inside | boundary

  noncomputable 
  def locateSpec (s : Shape p) (x : X) : Location := sorry
    -- if x ∈ interior s then
    --   inside
    -- else if x ∈ univ ∖ closure s
    --   outside
    -- else
    --   boundary

  class HasLocate (p : P → Set X) where
    locate : Shape p → X → Location
    is_locate : ∀ (s : Shape p), s.locateSpec = locate s

  def locate [HasLocate p] (s : Shape p) (x : X) := HasLocate.locate s x
  @[simp] theorem locate_spec [HasLocate p] (s : Shape p) 
    : s.locateSpec = s.locate := by apply HasLocate.is_locate


  -- Signed Distance Function
  noncomputable 
  def sdfSpec (s : Shape p) (x : X) : ℝ := sorry
    -- match s.locateSpec with
    -- | inside => - dist(x, boundary s)
    -- | outside =>  dist(x, boundary s)
    -- | boundary => 0

  class HasSdf (p : P → Set X) where
    sdf (s : Shape p) (x : X) : ℝ
    is_sdf : ∀ s, s.sdfSpec = sdf s

  def sdf [HasSdf p] (s : Shape p) (x : X) := HasSdf.sdf s x
  @[simp] theorem sdf_spec [HasSdf p] (s : Shape p) 
    : s.sdfSpec = s.sdf := by apply HasSdf.is_sdf


  -- Distance between two shapes

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
  

  -- Transoform of space can be done on parameters
  class HasTransform (p : P → Set X) (f : X → X) where
    trans : P → P
    is_trans : sorry

  def trans [HasTransform p f] (s : Shape p) : Shape p := ⟨HasTransform.trans p f s.params⟩


  -- -- Rigid transforms
  -- class HasRigidTransform (p : P → Set X) (R) [Group R] [LieGroup.SO R X] where
  --   rigidTransform : ∀ (t : X) (r : R), HasTransform p λ x => r•x + t


  -- Minkowski sum
  class HasMinkowskiSum (p : P → Set X) (q : Q → Set X) (r : outParam $ P → Set X) where
    sum : P → Q → P
    is_sum : sorry



  structure Ball.Params (X) [Hilbert X]  where
    center : X
    radius : ℝ

  def Ball.toSet (params : Ball.Params X) : Set X := λ x => (∥x-params.center∥ ≤ params.radius)

  structure Ball (X) [Hilbert X] extends Shape (Ball.toSet (X:=X))

  structure Sphere.Params (X) [Hilbert X]  where
    center : X
    radius : ℝ

  def Sphere.toSet (params : Sphere.Params X) : Set X := λ x => (∥x-params.center∥ = params.radius)

  abbrev Sphere (X) [Hilbert X] := Shape (Sphere.toSet (X:=X))

end Shape

-- structure TransformedShape.Params (P X R)  where
--   params : P
--   position : X
--   orientation : R

-- def TransformedShape.transform (p : P → Set X) : Params P X R → Set X := sorry

-- structure TransformedShape (p : P → Set X)  TransformedShape.transform p

-- def mkTransformedShape (s : Shape p) (x : X) (r : R) : Shape (TransformedShape.transform p) :=
--   ⟨s.params, x, r⟩

-- namespace TransformedShape 

--   variable {P X R : Type _} [SemiHilbert X] [Group R] [Diff R] [LieGroup.SO R X]

--   def toRef   (s : TransformedShape P X R) (x : X) : X := s.orientation⁻¹ • (x - s.position)
--   def toWorld (s : TransformedShape P X R) (x : X) : X := s.orientation • x + s.position

--   def sdf (s : Shape P X R) [Shape.HasSdf s] := 

-- end TransformedShape


namespace RigidBody

/--
Specification of a rigid body. This defines a class of rigid bodies parametrized
by a parameter `p : P`. For example balls would have `P = {density radius : ℝ}`
and we can compute the masses and the tensor of innertia.

It is assumed that the center of mass is in the origin.
-/
structure Spec (X R P : Type) [Diff R] where
  mass : P → ℝ
  inertiaTensor : P → {r : R} → 𝒯[r] R → 𝒯[r] R → ℝ

structure Position {X R P : Type} [Diff R] (spec : Spec X R P) where
  position : X
  orientation : R
  params : P

structure Velocity {X R P : Type} [Vec X] [Diff R] [Diff P] {spec : Spec X R P} (x : Position spec) where
  velocity : X
  angularVelocity : 𝒯[x.orientation] R
  dparams : 𝒯[x.params] P
deriving Vec

instance [Vec X] [Diff R] [Diff P] (spec : Spec X R P) : Diff (Position spec) where 
  TangentSpace x := Velocity x

abbrev State {X R P : Type} [Vec X] [Diff R] [Diff P] (spec : Spec X R P) := 𝒯 (Position spec)

variable {X R P ι : Type} {_ : Enumtype ι} [FinVec X ι] [Diff R] [Group R] [LieGroup.SO R X] [Diff P] {spec : Spec X R P}

namespace Position 

  def toRef   (b : Position spec) (x : X) : X := b.orientation⁻¹ • (x - b.position)
  def toWorld (b : Position spec) (x : X) : X := b.orientation • x + b.position

  def mass (b : Position spec) : ℝ := spec.mass b.params
  def inertiaTensor (b : Position spec) {r : R} (ω ω' : 𝒯[r] R) : ℝ := spec.inertiaTensor b.params ω ω'
  
end Position

def kineticEnergy (x : Position spec) (v : Velocity x) : ℝ := 1/2 * (x.inertiaTensor v.angularVelocity v.angularVelocity + x.mass * ∥v.velocity∥²)


end RigidBody

