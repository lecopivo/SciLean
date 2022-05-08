import Mathlib.Algebra.Group.Basic

section UnitOperations

  instance : Add PUnit := ⟨λ x y => PUnit.unit⟩
  instance : Sub PUnit := ⟨λ x y => PUnit.unit⟩
  instance : Mul PUnit := ⟨λ x y => PUnit.unit⟩
  instance : Neg PUnit := ⟨λ x => PUnit.unit⟩
  
  instance : Zero PUnit := ⟨PUnit.unit⟩

  -- Multiplication on `α` is not necessary but we do not want for example `ℕ*()` to compile
  instance [Mul α] : HMul α PUnit PUnit := ⟨λ a x => PUnit.unit⟩
 
end UnitOperations
