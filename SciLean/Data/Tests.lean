import SciLean.Basic
import SciLean.Tactic
-- import Lean

-- open Lean
-- open Lean.Meta

set_option synthInstance.maxHeartbeats 5000
-- set_option synthInstance.maxSize 1000

-- set_option trace.Meta.Tactic.simp true
-- set_option trace.Meta.synthInstance true 

namespace SciLean.NDVector.Tests

section NDVector

  variable {α β γ : Type}
  variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

  variable {dims} (x dx : NDVector dims) (i : Fin dims.product)
  example : ∂ (λ x => x[i]) x dx = dx[i] := by simp done
  example : ∂ (λ x => x[i]*x[i]) x dx = dx[i]*x[i] + x[i]*dx[i] := by simp done
  example : ∂ (λ x i => x[i]*x[i]) x dx i = dx[i]*x[i] + x[i]*dx[i] := by simp done

  example : Vec (NDVector dims) := by infer_instance
  example : Hilbert (NDVector dims) := by infer_instance

  example : (λ x : NDVector dims => sum fun i => getOp x i)† 1 = (lmk fun i => 1) := by autoadjoint done
  example (a : Fin _) [NonZero dims.product] : (fun (x : NDVector dims) i => x[i - a])† = (fun x => lmk fun i => x (i + a)) := by autoadjoint done
  example (x : NDVector dims) (i) : (fun (y : NDVector dims) => y[i] * x[i])† 1 = (lmk (λ j => (kron i j) * x[i])) := by autoadjoint simp done

  example (x) : gradient (λ (x : ℝ) => x) x = 1 := by autograd done
  example : ∇ (λ (x : NDVector dims) => x[i]) x = (lmk fun j => kron i j) := by autograd done
  example {dims} (i) (x : NDVector dims) : ∇ (λ (x : NDVector dims) => x[i]) x = lmk (kron i) := by autograd done
  example {dims} (i) (x : NDVector dims) : ∇ (λ (x : NDVector dims) => x[i]*x[i]) x = ((2 : ℝ) * lmk fun j => kron i j * x[i]) := by autograd done

end NDVector


