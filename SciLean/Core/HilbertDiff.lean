import SciLean.Core.Diff
import SciLean.Core.Hilbert

namespace SciLean

/-- Diffeological space with SemiHilbert structure on the tangent space

  TODO: Add some smoothness condition such that we can differentiate inner product
    However, this requires parallel transport!
  -/
@[reducible]
class SemiHilbertDiff (X : Type) extends Diff X where
  [instSemiHilbertTS : ∀ x, SemiHilbert (TangentSpace x)]

attribute [reducible] SemiHilbertDiff.instSemiHilbertTS SemiHilbertDiff.toDiff

@[reducible]
instance (priority:=low) (X : Type) [SemiHilbert X] : SemiHilbertDiff X := ⟨⟩

@[reducible] 
instance (X) [SemiHilbertDiff X] (x : X) : SemiHilbert (𝒯[x] X) := 
  SemiHilbertDiff.instSemiHilbertTS x

@[reducible]
instance SemiHilbertDiff_of_Prod
  (X) [SemiHilbertDiff X] (Y) [SemiHilbertDiff Y]
  : SemiHilbertDiff (X×Y) := ⟨⟩

@[reducible]
instance SemiHilbertDiff_of_funType
  {ι : Type} [Enumtype ι]
  (X) [SemiHilbertDiff X]
  : SemiHilbertDiff (ι → X) := ⟨⟩

@[reducible]
instance SemiHilbertDiff_of_Sum (X) [SemiHilbertDiff X] (Y) [SemiHilbertDiff Y]
  : SemiHilbertDiff (X⊕Y) := ⟨⟩


--------------------------------------------------------------------------------


@[reducible]
class HilbertDiff (X : Type) extends SemiHilbertDiff X where
  [instHilbertTS : ∀ x, Hilbert (TangentSpace x)]

attribute [reducible] HilbertDiff.instHilbertTS HilbertDiff.toSemiHilbertDiff

@[reducible]
instance (priority:=low) (X : Type) [Hilbert X] : HilbertDiff X := ⟨⟩

@[reducible] 
instance (X) [HilbertDiff X] (x : X) : Hilbert (𝒯[x] X) := 
  HilbertDiff.instHilbertTS x

@[reducible]
instance instHilbertDiffProd
  (X) [HilbertDiff X] (Y) [HilbertDiff Y]
  : HilbertDiff (X×Y) := ⟨⟩

@[reducible]
instance instHilbertDiffForAll
  {ι : Type} [Enumtype ι]
  (X) [HilbertDiff X]
  : HilbertDiff (ι → X) := ⟨⟩

@[reducible]
instance isntHilbertDiffSum (X) [HilbertDiff X] (Y) [HilbertDiff Y]
  : HilbertDiff (X⊕Y) := ⟨⟩
