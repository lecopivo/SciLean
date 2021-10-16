import SciLean.Basic

-- set_option synthInstance.maxHeartbeats 50000
-- set_option synthInstance.maxSize 10000

-- set_option trace.Meta.Tactic.simp true
-- set_option trace.Meta.synthInstance true 

namespace Data.Tests

section NDVector

  variable {dims} (x : NDVector dims) {dims'} (y : NDVector dims') (i : Fin dims.product)

  def test1 : IsDiff (NDVector.lget (dims := [3,4])) := by infer_instance done
  def test2 : IsDiff (comp HMul.hMul • NDVector.lget (dims := [3,4])) := by infer_instance done
  def test3 : IsDiff ((comp HMul.hMul) (NDVector.lget x) i) := by infer_instance done
  def test4 : IsDiff (comp (comp HMul.hMul) NDVector.lget x i) := by infer_instance done
  def test5 : IsDiff (subs ((comp HMul.hMul • NDVector.lget) x)) := by simp[subs]; rmlamlet; infer_instance; done
  def test6 : IsDiff (comp subs (comp HMul.hMul • NDVector.lget) x) := by simp[subs]; rmlamlet; infer_instance; done
  def test7 : IsDiff (swap comp NDVector.lget • (comp diag • swap (comp • swap comp)) • comp HMul.hMul • NDVector.lget (dims := dims)) := by infer_instance; done
  def test8 : IsDiff ((swap comp NDVector.lget • (comp diag • swap (comp • swap comp)) • comp HMul.hMul • NDVector.lget (dims := dims)) x) := by simp; infer_instance; done
  def test9 : IsDiff (diag • swap (comp • swap comp) (HMul.hMul • NDVector.lget x)) := by infer_instance
  def test10 : IsDiff ((diag • swap (comp • swap comp) (HMul.hMul • NDVector.lget x))) := by infer_instance
  def test11 : IsDiff ((swap (comp • swap comp) (HMul.hMul • NDVector.lget x)) : (Fin (List.product dims) → ℝ) → _ → _) := by infer_instance done

  #check adjoint (comp (swap comp (NDVector.getOp x)) • comp HMul.hMul • NDVector.getOp)

  def test12 : (comp (swap comp (NDVector.lget x)) • comp HMul.hMul • NDVector.lget) y = λ i j => x[j]*y[i] := by
    funext i j
    simp
    admit

  -- def test13 : adjoint (comp (swap comp (NDVector.getOp x)) • comp HMul.hMul • NDVector.getOp) = 0 := sorry

end NDVector



