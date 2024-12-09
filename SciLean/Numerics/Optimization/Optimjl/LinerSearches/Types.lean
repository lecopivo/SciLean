import SciLean.Data.DataArray
import SciLean.Numerics.Optimization.Optimjl.Utilities.Types
import SciLean.Analysis.Calculus.Notation.Deriv
import SciLean.Analysis.Calculus.Notation.FwdDeriv


namespace SciLean.Optimjl


variable {R : Type} [RealScalar R]


inductive LineSearchError where
  /-- Line search failed bacause reached maximum iteration -/
  | maxIterationn
  /-- Called method is not supported -/
  | notSupported


abbrev LineSearchM (Config State : Type) :=
  ReaderT Config $ StateT State (EIO LineSearchError)


variable (R)
class LineSearch (Config State : Type) where
  /-- Line search finds `x` such that `φ x ≤ φ 0 + c₁ * x * dφ 0`. -/
  c₁ (cfg : Config) : R

  /-- Print summary of the methods.

  With `verbose := false` this should be just a name.
  With `verbose := true` this should print the name and all the settings.  -/
  summary (cfg : Config) (verbose := false) : String


class LineSearch0 (Config State : Type) extends LineSearch R Config State where
  /-- Find `x` such that `φ x ≤ φ 0 + c₁ * x * dφ 0`. Return `x` and `φ x`.

  Method using only function values and derivative information at the beggining. -/
  call (Φ : R → R) (φ₀ dφ₀ : R) (x₀ : R) :
    LineSearchM Config State (Option (R×R)) := throw .notSupported


class LineSearch1 (Config State : Type) extends LineSearch R Config State where
  /-- Find `x` such that `φ x ≤ φ 0 + c₁ * x * dφ 0`. Return `x` and `φ x`.

  First order method using derivative information. -/
  call (Φdφ : R → R → R×R) (x₀ : R) (φdφ₀ : Option (R×R)) :
    LineSearchM Config State (Option (R×R)) := throw .notSupported
