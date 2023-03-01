import SciLean.Data.GenericArray.Notation
import SciLean.Data.GenericArray.Properties

namespace SciLean
namespace GenericArray
section GenericLinearArray

variable {Cont : Nat → Type} {Elem : Type |> outParam}
variable [GenericLinearArray Cont Elem]

