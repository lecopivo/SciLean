import SciLean.Basic

set_option synthInstance.maxHeartbeats 50000
set_option synthInstance.maxSize 10000

section Sum

-- set_option trace.Meta.Tactic.simp true
-- set_option trace.Meta.synthInstance true 

abbrev NDVector.getOp {dims} (self : NDVector dims) (idx : Fin dims.product) : ℝ := self.lget idx

variable (n : Nat)

def heheh : IsLin (NDVector.lget : NDVector [n] → Fin [n].product → ℝ ) := by infer_instance

def sum_test1 {dims} (u du : NDVector dims) : δ (λ v : NDVector dims => (∑ i, 5*v[i] + 3)) u du  = (∑ i, 5*du[i]) := 
by
  autodiff
  conv =>
    pattern (differential _)
    repeat' (ext x)
    simp

  done



def sum_test2 {dims} (u : NDVector dims) : ∇ (λ v : NDVector dims => (∑ i, v[i])) u = NDVector.lmk (λ _ => 1) :=
by
  simp
  simp[gradient]
  conv =>
    pattern (differential _)
    enter [x,dx]
    rmlamlet
    simp

  conv =>
    pattern (dual _)
    simp
    rmlamlet
    simp
  
  done

set_option trace.Meta.Tactic.simp true

def sum_test3 {dims} (u : NDVector dims) : ∇ (λ v : NDVector dims => (∑ i, (v.lget i)*(v.lget i))) u = (2:ℝ)*u :=
by
  simp[gradient]
  conv =>
    pattern (differential _)
    enter [x,dx]
    rmlamlet
    simp
  
  conv =>
    pattern (dual _)
    rmlamlet
    simp

  simp
  skip
  admit
    
def test : IsDiff (NDVector.lget (dims := [3,4])) := by infer_instance done

def test2 : IsDiff (comp HMul.hMul • NDVector.lget (dims := [3,4])) := by infer_instance done

def test3 {dims} (x : NDVector dims) (i) : IsDiff ((comp HMul.hMul) (NDVector.lget x) i) := by infer_instance

def test4 {dims} (x : NDVector dims) (i) : IsDiff (comp (comp HMul.hMul) NDVector.lget x i) := by infer_instance

def test5 (x : NDVector [3,4]) : IsDiff (subs ((comp HMul.hMul • NDVector.lget) x)) := by apply instIsDiffSubs_1

def test6 (x : NDVector [3,4]) : IsDiff (comp subs (comp HMul.hMul • NDVector.lget) x) := by infer_instance


set_option trace.Meta.synthInstance true 

def test7 : IsDiff (subs (subs • comp HMul.hMul • NDVector.lget (dims := [3,4])) NDVector.lget) := by apply instIsDiffSubs_2
end Sum
