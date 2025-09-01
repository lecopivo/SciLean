import SciLean.Data.DataArray
import SciLean.Analysis.Calculus.Notation.Deriv
import SciLean.Analysis.Calculus.Notation.FwdDeriv


namespace SciLean.Optimjl


variable {R : Type} [RealScalar R]


inductive LineSearchError where
  /-- Line search failed bacause reached maximum iteration -/
  | maxIterationn
  /-- Called method is not supported -/
  | notSupported


abbrev LineSearchM (Method State : Type) :=
  ReaderT Method $ StateT State (EIO LineSearchError)


variable (R)
class LineSearch (Method : Type) (State : outParam Type) where
  /-- Line search finds `x` such that `φ x ≤ φ 0 + c₁ * x * dφ 0`. -/
  c₁ (method : Method) : R

  /-- Print summary of the methods.

  With `verbose := false` this should be just a name.
  With `verbose := true` this should print the name and all the settings.  -/
  summary (method : Method) (verbose := false) : String


class LineSearch0 (Method : Type) (State : outParam Type) extends LineSearch R Method State where
  /-- Find `x` such that `φ x ≤ φ 0 + c₁ * x * dφ 0`. Return `x` and `φ x`.

  Method using only function values and derivative information at the beggining. -/
  call (Φ : R → R) (φ₀ dφ₀ : R) (x₀ : R) :
    LineSearchM Method State (R×R) := throw .notSupported


class LineSearch1 (Method : Type) (State : outParam Type) extends LineSearch R Method State where
  /-- Find `x` such that `φ x ≤ φ 0 + c₁ * x * dφ 0`. Return `x` and `φ x`.

  First order method using derivative information. -/
  call (Φdφ : R → R → R×R) (x₀ : R) (φdφ₀ : Option (R×R)) :
    LineSearchM Method State (R×R) := throw .notSupported


structure LineSearch0Obj (R : Type) [RealScalar R] where
  Method : Type
  m : Method
  inst : LineSearch0 R Method Unit := by infer_instance

variable {R}

def LineSearch0Obj.call (ls : LineSearch0Obj R) (φ : R → R) (φ₀ dφ₀ : R) (x₀ : R) :=
  ls.inst.call φ φ₀ dφ₀ x₀ ls.m
