import SciLean.Core


namespace SciLean

function_properties SciLean.Idx.shiftPos {n} [Nonempty (Idx n)] (x : Idx n) (y : USize)
argument x
  IsInv := sorry_proof,
  abbrev ⁻¹ := λ x' => x'.shiftNeg y by sorry_proof

function_properties SciLean.Idx.shiftNeg {n} [Nonempty (Idx n)] (x : Idx n) (y : USize)
argument x
  IsInv := sorry_proof,
  abbrev ⁻¹ := λ x' => x'.shiftPos y by sorry_proof

