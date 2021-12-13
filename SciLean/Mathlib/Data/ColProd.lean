def ColProd (α β) := α × β 
-- we use `×ₗ` because some moron did not include subscript c (as 'C'olumn) into unicode 
infixr:35 " ×ₗ "  => ColProd  

instance [ToString α] [ToString β] : ToString (α ×ₗ β) := by simp[ColProd] infer_instance

-- Column-wise ordering 
instance [LT α] [LT β] : LT (α ×ₗ β) where
  lt s t := s.2 < t.2 ∨ (s.2 = t.2 ∧ s.1 < t.1)
