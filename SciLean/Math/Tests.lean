import SciLean.Basic

set_option synthInstance.maxHeartbeats 50000
set_option synthInstance.maxSize 10000

section Sum

-- set_option trace.Meta.Tactic.simp true
-- set_option trace.Meta.synthInstance true 

variable (n : Nat) {dims} (u : NDVector dims) 

def heheh : IsLin (NDVector.getOp : NDVector [n] → Fin [n].product → ℝ ) := by infer_instance

def sum_test1 {dims} (u du : NDVector dims) 
    : δ (λ v : NDVector dims => (∑ i, 5*v[i] + 3)) u du  = (∑ i, 5*du[i]) := 
by
  autodiff
  conv =>
    pattern (differential _)
    repeat' (ext x)
    simp

  done



def sum_test2 {dims} (u : NDVector dims) 
    : ∇ (λ v : NDVector dims => (∑ i, v[i])) u = NDVector.lmk (λ _ => 1) :=
by
  simp
  simp[gradient]
  conv =>
    pattern (differential _)
    enter [x,dx]
    rmlamlet

  conv =>
    pattern (dual _)
    simp
    rmlamlet
    simp
  
  done


-- set_option trace.Meta.Tactic.simp true

def sum_test3
    : ∇ (λ v : NDVector dims => (∑ i, (v[i])*(v[i]))) u = (2:ℝ)*u :=
by
  simp[gradient]
  conv =>
    pattern (differential _)
    enter [x,dx]
    rmlamlet
    simp[subs]
    rmlamlet
    simp
    pattern (differential _)
    enter [x,dx,i,j]
    simp
  
  skip
  
  conv =>
    pattern (dual _)
    rmlamlet
    simp
  admit

#check adjoint (comp (swap comp (NDVector.getOp u)) • comp HMul.hMul • NDVector.getOp)

#check adjoint (comp (swap comp (NDVector.getOp u)) • comp HMul.hMul • NDVector.getOp)
    
end Sum


