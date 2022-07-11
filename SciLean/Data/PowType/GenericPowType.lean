import SciLean.Data.FunType
import SciLean.Data.NRealArray

namespace SciLean

-- We keep the argument order the same as for FunType
open FunType in
class PowType (T : outParam Type) (I X : Type) extends FunType T I X, HasSet T, HasIntro T

def PowTypeCarrier (X I : Type) {T} [PowType T I X] := T

notation X "^" I => PowTypeCarrier X I

syntax term "^{" term,* "}" : term

macro_rules 
| `($X:term ^{ $n }) => do
  `($X ^ (Fin $n))
| `($X:term ^{ $n,$ns,* }) => do
  let I ← ns.getElems.foldlM (λ x y => `($x × Fin $y)) (← `(Fin $n))
  `($X ^ $I)

namespace PowTypeCarrier

  variable {X I} {T : outParam Type} [Enumtype I] [PowType T I X] [Inhabited X]

  instance : FunType (X^I) I X := PowType.toFunType
  instance : FunType.HasSet (X^I) := PowType.toHasSet
  instance : FunType.HasIntro (X^I) := PowType.toHasIntro

  abbrev getOp (self : X^I) (idx : I) : X := FunType.toFun self idx
  abbrev set (x : X^I) (i : I) (xi : X) : X^I := FunType.HasSet.set x i xi
  abbrev intro (f : I → X) : X^I := FunType.HasIntro.intro f
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


variable (x : ℝ^{n,m})


-- def conv2d (x : Fin n → Fin m → ℝ) (y : Fin 3 → Fin 3 → Fin k → ℝ) : ℝ^{n-2, m-2, k} := 
--   .intro λ ((i, j), k) => Id.run do
--     let mut val : ℝ := 0
--     for di in [0:3] do
--       for dj in [0:3] do
--         val := val + x[(i + di -1, j + dj -1)] -- * y[(di+1, dj+1, k)]
--     val
    
