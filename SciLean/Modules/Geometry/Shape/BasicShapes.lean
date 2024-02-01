import SciLean.Core.Defs
import SciLean.Core.Meta.RewriteBy
import SciLean.Core.AdjDiff
import SciLean.Core.Tactic.FunctionTransformation.Core
import SciLean.Core.UnsafeAD
import SciLean.Core.CoreFunctions
import SciLean.Data.DataArray

import SciLean.Physics.Shape

namespace SciLean

namespace Shape

-- A great inspiration for this file is this amazing argicle on basic shapes and
-- their distance function: https://iquilezles.org/articles/distfunctions/

------------------------------------------------------------------------------
-- Axis Aligned Box
------------------------------------------------------------------------------

structure AxisAlignedBoxAtOrigin.Params (X) {ι : Type} {_:Enumtype ι} [FinVec X ι] where
  radius : ℝ^ι
  radius_valid : ∀ i, 0 ≤ radius[i] -- we do not want empty box

def AxisAlignedBoxAtOrigin.toSet {X ι : Type} [Enumtype ι] [FinVec X ι] (p : Params X) (x : X) : Prop :=
  ∀ i : ι, (Real.abs (𝕡 i x)) ≤ p.radius[i]

abbrev AxisAlignedBoxAtOrigin (X : Type) {ι} {_ : Enumtype ι} [FinVec X ι] := Shape (AxisAlignedBoxAtOrigin.toSet (X:=X) (ι:=ι))

abbrev AxisAlignedBox (X : Type) {ι} {_:Enumtype ι} [FinVec X ι] := Shape (translatedSet (AxisAlignedBoxAtOrigin.toSet (X:=X) (ι:=ι)))

abbrev Box (X R : Type) {ι} {_:Enumtype ι} [FinVec X ι] [Group R] [LieGroup.SO R X]
  := Shape (rigidTransformSet R (AxisAlignedBoxAtOrigin.toSet (X:=X) (ι:=ι)))

def mkAxisAlignedBox {X : Type} {ι} {_:Enumtype ι} [FinVec X ι] (min max : X)
  : AxisAlignedBox X :=
  let p : AxisAlignedBoxAtOrigin.Params X :=
    {
      radius := ⊞ i, (0.5 : ℝ) * (𝕡 i max - 𝕡 i min).abs
      radius_valid := sorry
    }
  ⟨p, (0.5 : ℝ) • (min + max)⟩

namespace AxisAlignedBoxAtOrigin

  variable {X ι} [Enumtype ι] [FinVec X ι]

  instance : HasLocate (toSet (X:=X) (ι:=ι)) where
    locate := λ s x => Id.run do
      let mut l : Location := .inside
      for (i,_) in Enumtype.fullRange ι do
        let xi := (𝕡 i x).abs
        if s.params.radius[i] < xi then
          return .outside
        if xi = s.params.radius[i] then
          l := .boundary
      return l
    is_locate := sorry

  instance [OrthonormalBasis X ι ℝ] : HasSdf (toSet (X:=X) (ι:=ι)) where
    sdf := λ s x => Id.run do
      let mut cornerDist : ℝ := 0
      let mut sideDist   : ℝ := 0
      for (i,id) in Enumtype.fullRange ι do
        let xi := 𝕡 i x
        let ri := s.params.radius[i]
        let q := xi.abs - ri

        -- initialize sideDist
        if id.1 = 0 then
          sideDist := q

        if q > 0 then
          cornerDist += q*q

        if sideDist < q then
          sideDist := q

      return cornerDist.sqrt + sideDist.min 0
    is_sdf := sorry

  instance : HasReflect (toSet (X:=X) (ι:=ι)) where
    trans := λ p => p
    is_trans := sorry

  instance : HasScale (toSet (X:=X) (ι:=ι)) := λ s =>
  {
    trans := λ ⟨p, h⟩ =>
      {
        radius := ⊞ i, s.abs * p[i]
        radius_valid := sorry
      }
    is_trans := sorry
  }

end AxisAlignedBoxAtOrigin


------------------------------------------------------------------------------
-- Ball
------------------------------------------------------------------------------

structure BallAtOrigin.Params (X : Type) [Hilbert X] where
  radius : ℝ
  radius_valid : 0 ≤ radius

namespace BallAtOrigin.Params

  variable {X : Type} [Hilbert X] (p : Params X)

  def sdf (x : X) := ‖x‖ - p.radius

  def sdfGrad (x : X) := (∇ (sdf p) x)
    rewrite_by
      unfold sdf; unfold gradient
      unsafe_ad
      fun_trans

  def sdfHess (x : X) (u v : X) := (∂ (∂ (sdf p)) x u v)
    rewrite_by
      unfold sdf; unfold gradient
      unsafe_ad
      fun_trans
      simp[fun_trans]
      fun_trans

  def levelSet (x : X) := ‖x‖² - p.radius^2

  def levelSetGrad (x : X) := (∇ (levelSet p) x)
    rewrite_by
      unfold levelSet; unfold gradient
      fun_trans

  def levelSetHess (x u v: X) := (∂ (∂ (levelSet p)) x u v)
    rewrite_by
      unfold levelSet; unfold gradient
      fun_trans; simp; fun_trans

end BallAtOrigin.Params

def BallAtOrigin.toSet {X} [Hilbert X] (p : Params X) (x : X) : Prop :=
  ‖x‖ ≤ p.radius

abbrev BallAtOrigin (X : Type) {ι : Type} {_ : Enumtype ι} [FinVec X ι] := Shape (BallAtOrigin.toSet (X:=X))

def mkBallAtOrigin (X) {ι} {_:Enumtype ι} [FinVec X ι] (radius : ℝ)
  : BallAtOrigin X := ⟨radius.abs, sorry⟩

abbrev Ball (X) {ι} {_:Enumtype ι} [FinVec X ι] := Shape (translatedSet (BallAtOrigin.toSet (X:=X)))

def mkBall {X} {ι} {_:Enumtype ι} [FinVec X ι] (center : X) (radius : ℝ)
  : Ball X := (mkBallAtOrigin X radius).mkTranslated center

namespace BallAtOrigin

  variable {X} [Hilbert X]

  instance : HasLevelSet (toSet (X:=X)) where
    levelSet := λ s x => ‖x‖² - s.params.radius^2
    is_level_set := sorry

  instance : HasLocate (toSet (X:=X)) := locateFromLevelSet

  instance : HasSdf (toSet (X:=X)) where
    sdf := λ s x => ‖x‖ - s.params.radius
    is_sdf := sorry

  instance : HasReflect (toSet (X:=X)) where
    trans := λ p => p
    is_trans := sorry

  instance (R : Type) [Group R] [LieGroup.SO R X] : HasRotate R (toSet (X:=X)) := λ r =>
  {
    trans := λ p => p
    is_trans := sorry
   }

  instance : HasScale (toSet (X:=X)) := λ s =>
  {
    trans := λ ⟨r, h⟩ =>
      {
        radius := s.abs * r
        radius_valid := sorry
      }
    is_trans := sorry
  }

end BallAtOrigin


------------------------------------------------------------------------------
-- Capsule
------------------------------------------------------------------------------

structure Capsule.Params (X : Type) [Hilbert X] where
  point1 : X
  point2 : X
  radius : {r : ℝ // 0 ≤ r}

def Capsule.sdf {X} [Hilbert X] (a b : X) (r : ℝ) (x : X) : ℝ :=
  let xa := x - a
  let ba := (b - a)
  let ba := (1/‖ba‖) • ba
  let h := ⟪xa, ba⟫.clamp 0 1
  ‖xa - h•ba‖ - r

def Capsule.toSet {X} [Hilbert X] (p : Params X) (x : X) : Prop :=
  Capsule.sdf p.point1 p.point2 p.radius x ≤ 0

abbrev Capsule (X ι : Type) [Enumtype ι] [FinVec X ι] := Shape (Capsule.toSet (X:=X))

namespace Capsule

  variable {X} [Hilbert X]

  instance : HasLevelSet (toSet (X:=X)) where
    levelSet := λ s x =>
      let xa := x - s.params.point1
      let ba := (s.params.point2 - s.params.point1)
      let ba := (1/‖ba‖) • ba
      let h := ⟪xa, ba⟫.clamp 0 1
      ‖xa - h•ba‖² - s.params.radius.1^2
    is_level_set := sorry

  instance : HasLocate (toSet (X:=X)) := locateFromLevelSet

  instance : HasSdf (toSet (X:=X)) where
    sdf := λ s x =>
      let xa := x - s.params.point1
      let ba := (s.params.point2 - s.params.point1)
      let ba := (1/‖ba‖) • ba
      let h := ⟪xa, ba⟫.clamp 0 1
      ‖xa - h•ba‖ - s.params.radius
    is_sdf := sorry

  instance : HasReflect (toSet (X:=X)) where
    trans := λ p =>
      {
        point1 := - p.point1
        point2 := - p.point2
        radius := p.radius
      }
    is_trans := sorry

  instance : HasTranslate (toSet (X:=X)) := λ t =>
  {
    trans := λ p =>
      {
        point1 := p.point1 + t
        point2 := p.point2 + t
        radius := p.radius
      }
    is_trans := sorry
   }

  instance (R : Type) [Group R] [LieGroup.SO R X] : HasRotate R (toSet (X:=X)) := λ r =>
  {
    trans := λ p =>
      {
        point1 := r • p.point1
        point2 := r • p.point2
        radius := p.radius
      }
    is_trans := sorry
   }


end Capsule


------------------------------------------------------------------------------
-- Round Cone
------------------------------------------------------------------------------



structure RoundCone.Params (X : Type) [Hilbert X] where
  a : X
  b : X
  r1 : ℝ
  r2 : ℝ
  valid : 0 ≤ r1 ∧ 0 ≤ r2

namespace RoundCone.Params

  variable {X} [Hilbert X] (p : RoundCone.Params X)

  -- This code comes from https://iquilezles.org/articles/distfunctions/

  -- Maybe turn these into computed fields
  def ba := p.b - p.a
  def l2 := ‖p.ba‖²
  def rr := p.r1 - p.r2
  def a2 := p.l2 - p.rr^2
  def il2 := 1.0 / p.l2

  def sdf (x : X) :=
    let pa := x - p.a
    let y  := ⟪pa,p.ba⟫
    let z  := y - p.l2
    let x2 := ‖p.l2•pa - y•p.ba‖²
    let y2 := y*y*p.l2
    let z2 := z*z*p.l2

    let k := p.rr.sign*p.rr*p.rr*x2
    if (z.sign*p.a2*z2 > k) then
      (x2 + z2).sqrt * p.il2 - p.r2
    else if (y.sign*p.a2*y2 < k) then
      (x2 + y2).sqrt * p.il2 - p.r1
    else
    ((x2*p.a2*p.il2).sqrt+y*p.rr)*p.il2 - p.r1

  set_option synthInstance.maxSize 2000

  -- noncomputable
  -- def sdfGrad (x : X) := (∇ p.sdf x)
  --   rewrite_by
  --     unfold sdf; unfold gradient
  --     unsafe_ad
  --     ignore_fun_prop
  --     fun_trans



end RoundCone.Params


def RoundCone.toSet {X} [Hilbert X] (p : Params X) (x : X) : Prop :=
  p.sdf x ≤ 0

abbrev RoundCone (X : Type) [Hilbert X] := Shape (RoundCone.toSet (X:=X))


namespace RoundCone

  variable {X} [Hilbert X]

  instance : HasSdf (toSet (X:=X)) where
    sdf := λ s x => s.params.sdf x
    is_sdf := sorry

  instance : HasLocate (toSet (X:=X)) := locateFromSdf

  instance : HasReflect (toSet (X:=X)) where
    trans := λ p =>
      {
        a := - p.a
        b := - p.b
        r1 := p.r1
        r2 := p.r2
        valid := p.valid
      }
    is_trans := sorry

  instance : HasTranslate (toSet (X:=X)) := λ t =>
  {
    trans := λ p =>
      {
        a := p.a + t
        b := p.b + t
        r1 := p.r1
        r2 := p.r2
        valid := p.valid
      }
    is_trans := sorry
   }

  instance (R : Type) [Group R] [LieGroup.SO R X] : HasRotate R (toSet (X:=X)) := λ r =>
  {
    trans := λ p =>
      {
        a := r • p.a
        b := r • p.b
        r1 := p.r1
        r2 := p.r2
        valid := p.valid
      }
    is_trans := sorry
   }

  instance : HasScale (toSet (X:=X)) := λ s =>
  {
    trans := λ p =>
      {
        a := s•p.a
        b := s•p.b
        r1 := s.abs*p.r1
        r2 := s.abs*p.r2
        valid := sorry
      }
    is_trans := sorry
   }

end RoundCone


variable {X Y} [SemiHilbert X] [SemiHilbert Y]
#check (∂† λ xy : X × Y => xy.fst) rewrite_by fun_trans [fun_trans]; simp [fun_trans]

open Lean Qq Meta

#eval show MetaM Unit from do

  let fst : Q(ℝ×ℝ → ℝ) := q(λ xy : ℝ × ℝ => xy.fst)

  IO.println (← reduce fst)
