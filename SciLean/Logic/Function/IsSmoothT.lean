import SciLean.Logic.Function.TransitiveClosure
import SciLean.Algebra.IsLinearMap

namespace SciLean

/-- A function is smooth if it's differentiable to all orders -/
class IsSmooth (K : Type) [RCLike K] {X Y : Type} [NormedAddCommGroup X] [NormedSpace K X]
    [NormedAddCommGroup Y] [NormedSpace K Y] (f : X → Y) : Prop :=
  (smooth : Differentiable K f)

/-- Transitive closure of IsSmooth -/
abbrev IsSmoothT (K : Type) [RCLike K] {X Y : Type} [NormedAddCommGroup X] [NormedSpace K X]
    [NormedAddCommGroup Y] [NormedSpace K Y] (f : X → Y) : Prop :=
  FunPropT (IsSmooth K) f

/-- Linear maps are smooth -/
instance (priority := 80) isSmooth_of_isLinearMap {K : Type} [RCLike K] {X Y : Type} 
    [NormedAddCommGroup X] [NormedSpace K X]
    [NormedAddCommGroup Y] [NormedSpace K Y] 
    {f : X → Y} (h : IsLinearMap K f) : 
    IsSmooth K f :=
  { smooth := sorry_proof }

/-- Composition of smooth functions is smooth -/
theorem isSmooth_comp {K : Type} [RCLike K] {X Y Z : Type} 
    [NormedAddCommGroup X] [NormedSpace K X]
    [NormedAddCommGroup Y] [NormedSpace K Y]
    [NormedAddCommGroup Z] [NormedSpace K Z]
    {f : Y → Z} {g : X → Y} 
    (hf : IsSmooth K f) (hg : IsSmooth K g) : 
    IsSmooth K (f ∘ g) :=
  { smooth := sorry_proof }

end SciLean
