import SciLean.Core.FloatAsReal
import SciLean.Core.FunctionTransformations
import SciLean.Core.Notation.CDeriv
import SciLean.Core.Notation.FwdDeriv
import SciLean.Core.Rand.Rand
import SciLean.Core.Rand.Distributions.Uniform
import SciLean.Data.ArrayType
import SciLean.Data.DataArray
import SciLean.Tactic.Autodiff
import SciLean.Mathlib.Analysis.AdjointSpace.Geometry

import Mathlib.MeasureTheory.Measure.Hausdorff

open MeasureTheory

namespace SciLean.Rand

-- open Rand Scalar RealScalar in
-- instance (x : Vec3) (r : Float) : UniformRand (sphere₂ x r) where
--   uniform := {
--     -- there is some clash of UniformSpace instances on `Float` that causes `BorelSpace Vec3` to be infered
--     -- and this prevent the use of Hausdoff measure here
--     spec := erase (fun φ => 0 /- ∫ x' in sphere₂ x r, φ x' ∂μH[2]-/)
--     rand := Rand.rand <| do
--       let z := 2*(← uniformI Float) - 1
--       let θ := 2*pi*(← uniformI Float)
--       let r := sqrt (1 - z*z)
--       return ⟨r*cos θ, r*sin θ, z⟩
--     }
--   is_uniform := sorry_proof
