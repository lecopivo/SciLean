import SciLean.Core.Functions
import SciLean.Mechanics
import SciLean.Operators.ODE
-- import SciLean.Solver 
-- import SciLean.Tactic.LiftLimit
-- import SciLean.Tactic.FinishImpl
-- import SciLean.Data.PowType
-- import SciLean.Core.Extra

open Function

open SciLean


variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
variable {U V W : Type} [Hilbert U] [Hilbert V] [Hilbert W]

