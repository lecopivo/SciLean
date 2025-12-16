import SciLean
import tensor_basic

/-!
Smoke tests for SciLean.

These are intentionally compilation-only (no `#eval`) so they work on macOS
even when module precompilation is disabled (to avoid building `Mathlib:shared`).
-/

open SciLean

-- A couple of basic "does it elaborate?" checks.
#check SciLean.Numerics.ODE.rungeKutta4
#check SciLean.Numerics.ODE.heunMethod
#check SciLean.Numerics.ODE.explicitMidpoint

-- Tensor types
#check Device
#check CpuTensor
#check GpuTensor
