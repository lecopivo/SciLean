import SciLean.Core.Defs
import SciLean.Core.Diff

import SciLean.Meta.DerivingAlgebra
import SciLean.Core.DifferentialDep

namespace SciLean


class LieGroup.SO (G V : Type) [SemiHilbert V] [Group G] extends DistribMulAction G V -- extends Diff G

namespace RigidBody

/--
Specification of a rigid body. This defines a class of rigid bodies parametrized
by a parameter `p : P`. For example balls would have `P = {density radius : ℝ}`
and we can compute the masses and the tensor of innertia.

It is assumed that the center of mass is in the origin.
-/
structure Params (X R : Type) [Diff R] where
  mass : ℝ
  inertiaTensor : {r : R} → 𝒯[r] R → 𝒯[r] R → ℝ

structure Position (X R : Type) [Vec X] [Diff R] where
  position : X
  orientation : R

structure Velocity {X R} [Vec X] [Diff R] (x : Position X R) where
  velocity : X
  angularVelocity : 𝒯[x.orientation] R
deriving Vec

instance [Vec X] [Diff R] : Diff (Position X R) where 
  TangentSpace x := Velocity x

abbrev State (X R : Type) [Vec X] [Diff R] := 𝒯 (Position X R)

variable {X R P ι : Type} {_ : Enumtype ι} [FinVec X ι] [Diff R] [Group R] [LieGroup.SO R X]

namespace Position 

  def toRef   (b : Position X R) (x : X) : X := b.orientation⁻¹ • (x - b.position)
  def toWorld (b : Position X R) (x : X) : X := b.orientation • x + b.position
  
end Position

def kineticEnergy (p : Params X R) (x : Position X R) (v : Velocity x) : ℝ := 
  1/2 * (p.inertiaTensor v.angularVelocity v.angularVelocity + p.mass * ∥v.velocity∥²)


end RigidBody

