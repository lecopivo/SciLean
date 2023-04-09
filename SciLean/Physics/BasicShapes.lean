
import SciLean.Physics.Shape

namespace SciLean

namespace Shape

-- A great inspiration for this file is this amazing argicle on basic shapes and 
-- their distance function: https://iquilezles.org/articles/distfunctions/


------------------------------------------------------------------------------
-- Axis Aligned Box
------------------------------------------------------------------------------

structure AxisAlignedBox.Params (X ι : Type) [Enumtype ι] [FinVec X ι] where
  min : ι → ℝ  -- TODO: Change to ℝ^ι once it is not broken
  max : ι → ℝ  
  is_valid : ∀ i, min i ≤ max i -- we do not want empty box

def AxisAlignedBox.toSet {X ι} [Enumtype ι] [FinVec X ι] (p : Params X ι) (x : X) : Prop := 
  ∀ i : ι, (p.min i ≤ 𝕡 i x) ∧ (𝕡 i x ≤ p.max i)

abbrev AxisAlignedBox (X ι : Type) [Enumtype ι] [FinVec X ι] := Shape (AxisAlignedBox.toSet (X:=X) (ι:=ι))

namespace AxisAlignedBox

  variable {X ι} [Enumtype ι] [FinVec X ι]

  instance : HasLocate (toSet (X:=X) (ι:=ι)) where
    locate := λ s x => Id.run do
      let mut l : Location := .inside
      for (i,_) in Enumtype.fullRange ι do
        let xi := 𝕡 i x
        if xi < s.params.min i || s.params.max i < xi then
          return .outside
        if xi = s.params.min i || s.params.max i = xi then
          l := .boundary
      return l
    is_locate := sorry


  instance [OrhonormalBasis X ι] : HasSdf (toSet (X:=X) (ι:=ι)) where
    sdf := λ s x => Id.run do
      let mut cornerDist : ℝ := 0
      let mut sideDist   : ℝ := 0
      for (i,id) in Enumtype.fullRange ι do
        let xi := 𝕡 i x
        let ci := (s.params.max i + s.params.min i)/2 -- center 
        let ri := (s.params.max i - s.params.min i)/2 -- radius
        let q := (xi - ci).abs - ri

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
    trans := λ p => 
      {
        min := λ i => - p.max i
        max := λ i => - p.min i
        is_valid := sorry
      }
    is_trans := sorry

  instance : HasTranslate (toSet (X:=X) (ι:=ι)) := λ t => 
  {
    trans := λ p => 
      {
        min := λ i => p.min i + 𝕡 i t
        max := λ i => p.max i + 𝕡 i t
        is_valid := sorry
      }
    is_trans := sorry
   }

end AxisAlignedBox


------------------------------------------------------------------------------
-- Ball
------------------------------------------------------------------------------

structure Ball.Params (X : Type) [Hilbert X] where
  center : X
  radius : {r : ℝ // 0 ≤ r}

def Ball.toSet {X} [Hilbert X] (p : Params X) (x : X) : Prop := 
  ∥x - p.center∥ ≤ p.radius.1

abbrev Ball (X ι : Type) [Enumtype ι] [FinVec X ι] := Shape (Ball.toSet (X:=X))


namespace Ball

  variable {X} [Hilbert X]

  instance : HasLocate (toSet (X:=X)) where
    locate := λ s x =>
      let d := ∥x - s.params.center∥² - s.params.radius.1^2
      if 0 < d then
        .outside
      else if d = 0 then
        .boundary
      else
        .inside
    is_locate := sorry

  instance : HasSdf (toSet (X:=X)) where
    sdf := λ s x => ∥x - s.params.center∥ - s.params.radius.1
    is_sdf := sorry
  
  instance : HasReflect (toSet (X:=X)) where
    trans := λ p => 
      {
        center := - p.center
        radius := p.radius
      }
    is_trans := sorry

  instance : HasTranslate (toSet (X:=X)) := λ t => 
  {
    trans := λ p => 
      {
        center := p.center + t
        radius := p.radius
      }
    is_trans := sorry
   }


end Ball



