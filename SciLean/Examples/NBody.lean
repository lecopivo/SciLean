import SciLean.Basic
import SciLean.Mechanics

namespace SciLean

set_option synthInstance.maxHeartbeats 5000
set_option synthInstance.maxSize 1000

def G : ℝ := 1.0

def NDVector.getVec3 {n} (v : NDVector [3,n]) (i : Fin n) : ℝ×ℝ×ℝ := (v[⟨3*i+0, sorry⟩], v[⟨3*i+1, sorry⟩], v[⟨3*i+2, sorry⟩])


def T {n : Nat} (m : NDVector [n]) (p : NDVector [3, n]) : ℝ := 
    ∑ i, (1/(2*m[i])) * ∥p.getVec3 ⟨i,sorry⟩∥^(2:ℝ)

def V {n : Nat} (m : NDVector [n]) (x : NDVector [3, n]) : ℝ :=
(1/2) * ∑ i j, G*(m[i])*(m[j]) * 1/∥(x.getVec3 ⟨i,sorry⟩ - x.getVec3 ⟨j,sorry⟩)∥

def H {n} (m : NDVector [n]) (x p : NDVector [3, n]) := T m p - V m x


-- def Tgrad {n} (m : NDVector [n]) : Impl (∇ (T m)) := 
-- by
--   conv =>
--     enter [1]
--     simp [T]
    
    

def solver {n} (m : NDVector [n]) (steps : Nat) : Impl (ode_solve (HamiltonianSystem (H m))) := 
by  
  conv => 
    enter [1,1]
    simp[HamiltonianSystem, H, T, V]

    conv =>
      pattern (∇ _)
      simp[gradient]
      conv => 
        pattern (δ _)
        enter [x,dx]
        


  admit
  
  
  

  
