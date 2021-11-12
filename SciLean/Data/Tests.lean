import SciLean.Basic
-- import Lean

-- open Lean
-- open Lean.Meta

-- set_option synthInstance.maxHeartbeats 5000
-- set_option synthInstance.maxSize 1000

-- set_option trace.Meta.Tactic.simp true
-- set_option trace.Meta.synthInstance true 

namespace SciLean.NDVector.Tests

section NDVector

  variable {α β γ : Type}
  variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

  variable {dims} (x dx : NDVector dims) (i : Fin dims.product)
  example : δ (λ x => x[i]) x dx = dx[i] := by simp done
  example : δ (λ x => x[i]*x[i]) x dx = dx[i]*x[i] + x[i]*dx[i] := by simp done
  example : δ (λ x i => x[i]*x[i]) x dx i = dx[i]*x[i] + x[i]*dx[i] := by simp done

  example : Vec (NDVector dims) := by infer_instance
  example : Hilbert (NDVector dims) := by infer_instance

  example : adjoint (δ (λ (x : NDVector dims) => x[i]) x) 1 = 0 := 
  by 
    conv => 
      pattern (δ _)
      enter [x,dx]
      simp

    admit

  -- noncomputable 
  -- def foo {U} [Hilbert U] (u : U) : U := u

  -- @[simp]
  -- theorem hohoh {X} [Vec X] (x : X) : (2 : ℝ) * x = x := sorry

  -- #check gradient

  -- example (x : ℝ) :  (δ (λ (x : ℝ) => x) (x + x))† 1  = x :=
  -- by
  --   conv in (δ _) => enter [x,dx]
  --   simp
    
  --   admit

  example (x) : gradient (λ (x : ℝ) => x) x = 1 :=
  by 
    conv =>
      pattern (gradient _)
      simp[gradient]
      conv =>
        enter [x,1,dx]
        simp
    simp done

  example : ∇ (λ (x : NDVector dims) => x[i]) x = 0 := 
  by
    conv =>
      pattern (∇ _)
      simp[gradient]
      conv =>
        pattern (δ _)
        enter [x,dx]
        simp
    simp[getOp]
    admit

  example {dims} (i) (x : NDVector dims) : ∇ (λ (x : NDVector dims) => x[i]) x = lmk (kron i) := 
  by
    conv =>
      pattern (∇ _)
      simp[gradient]
      conv =>
        enter[x,1,dx]
        simp
    simp done

  example (x : NDVector dims) (i) : (fun (y : NDVector dims) => y[i] * x[i])† 1 = (lmk (λ j => (kron i j) * x[i])) :=
  by
    simp
    done

  example {dims} (i) (x : NDVector dims) : ∇ (λ (x : NDVector dims) => x[i]*x[i]) x = lmk (kron i) := 
  by
    conv =>
      pattern (∇ _)
      simp[gradient]
      conv =>
        enter[x,1,dx]
        simp
    simp[Function.comp] 
    admit

end NDVector


