import SciLean.Data.ArrayType.Properties

namespace SciLean

variable {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam}
variable [GenericArrayType Cont Idx Elem] [Enumtype Idx] [Nonempty Idx]

@[simp]
theorem sum_setElem_zero [Vec Elem] (f : Idx → Elem) :
  ∑ (i : Idx), setElem (0 : Cont) i (f i) = introElem f := sorry_proof

@[simp]
theorem sum_setElem_zero' [Vec Elem] (f : Idx → Elem) (g : Idx → Idx) [IsInv g] :
  ∑ (i : Idx), setElem (0 : Cont) (g i) (f i) = introElem (λ i => f (g⁻¹ i)) := sorry_proof
