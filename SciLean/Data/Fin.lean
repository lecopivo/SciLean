import SciLean.Core.CoreFunctions

namespace SciLean

def _root_.Fin.shift (x : Fin n) (y : Int) : Fin n := ⟨((x.1 + y) % n).toNat, sorry⟩


function_properties Fin.shift {n} [Nonempty (Fin n)] (x : Fin n) (y : Int)
argument x
  IsInv := sorry_proof,
  abbrev ⁻¹ := λ x' => x'.shift (-y) by sorry_proof

