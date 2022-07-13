import SciLean.Data.FunType
import SciLean.Data.NRealArray

namespace SciLean

-- PowType is just like FunType where the type `T` is not important
-- The main example `ℝ^n`, it bahaves like `Fin n → ℝ` but we do not 
-- care too much about what exactly `T` is. 
-- PowType provides notation `ℝ^Fin n`, we also have short hand `ℝ^{n}`.
open FunType in
class PowType (T : outParam Type) (I X : Type) extends FunType T I X, HasSet T, HasIntro T

def PowTypeCarrier (X I : Type) {T} [PowType T I X] := T

notation X "^" I => PowTypeCarrier X I

-- Allow notation like ℝ^{n,m,k}
syntax term "^{" term,* "}" : term
macro_rules 
| `($X:term ^{ $n }) => do
  `($X ^ (Fin $n))
| `($X:term ^{ $ns,* }) => do
  if 0 < ns.getElems.size then
    let last := ns.getElems[ns.getElems.size-1]!
    let ns' := ns.getElems[:ns.getElems.size-1]
    let I ← ns'.foldrM (λ x y => `(Fin $x × $y)) (← `(Fin $last))
    `($X ^ $I)
  else 
    `(Unit)

namespace PowTypeCarrier

  variable {X I} {T : outParam Type} [Enumtype I] [PowType T I X] [Inhabited X]

  instance : FunType (X^I) I X := PowType.toFunType
  instance : FunType.HasSet (X^I) := PowType.toHasSet
  instance : FunType.HasIntro (X^I) := PowType.toHasIntro

  abbrev get (x : X^I) (i : I) : X := getElem x i True.intro
  abbrev set (x : X^I) (i : I) (xi : X) : X^I := setElem x i xi
  abbrev intro (f : I → X) : X^I := FunType.intro f
  abbrev modify [Inhabited X] (x : X^I) (i : I) (f : X → X) : X^I := FunType.modify x i f
  abbrev mapIdx (f : I → X → X) (x : X^I) : X^I := FunType.mapIdx f x
  abbrev map (f : X → X) (x : X^I) : X^I := FunType.map f x

end PowTypeCarrier

instance [Enumtype I] : PowType (NRealArray (numOf I)) I ℝ := ⟨⟩

namespace PowTypeCarrier

  def reshape {I J} [Enumtype I] [Enumtype J] (x : ℝ^I) (h : numOf I = numOf J) : ℝ^J :=
    ⟨x.1, h ▸ x.2⟩

end PowTypeCarrier

instance {T I X} [PowType T I X] [Enumtype I] [ToString I] [ToString X] : ToString (X^I) :=
  ⟨λ x => Id.run do
    let mut s := ""
    for (i,li) in Enumtype.fullRange I do
      if li = 0 then
        s := s.append s!"{i}: {x[i]}"
      else 
        s := s.append s!", {i}: {x[i]}"
    "{" ++ s ++ "}"⟩

-- variable (x : ℝ^{3,22,10})
-- #check λ (i,j,k) => x[(i,j,k)]

-- namespace PowType

--   @[simp]
--   theorem sum_intro {ι} [Enumtype ι]
--     [PowType α] [Add α] [Zero α] [Zero (Idx n → α)] [Add (Idx n → α)]
--     (f : ι → Idx n → α) 
--     : (∑ i, PowType.intro (f i)) = (PowType.intro (∑ i, f i))
--     := 
--   by
--     admit

--   @[simp]
--   theorem add_intro 
--     (f g : Idx n → α) [PowType α] [Add α]
--     : 
--       (PowType.intro f)  + (PowType.intro g)
--       = 
--       (PowType.intro λ i => f i + g i)
--     := 
--   by
--     admit

--   @[simp]
--   theorem sub_intro 
--     (f g : Idx n → α) [PowType α] [Sub α]
--     : 
--       (PowType.intro f)  - (PowType.intro g)
--       = 
--       (PowType.intro λ i => f i - g i)
--     := 
--   by
--     admit


--   @[simp]
--   theorem hmul_intro 
--     (f : Idx n → α) [PowType α] [HMul β α α] (b : β)
--     :
--       b * (PowType.intro f) = PowType.intro λ i => b * f i
--     := 
--   by 
--     admit
