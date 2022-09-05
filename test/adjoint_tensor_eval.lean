import SciLean
import SciLean.Tactic.Basic

open SciLean

variable {I₁ I₂ I₃ I₄ : Type} 
variable [Enumtype I₁] [Enumtype I₂] [Enumtype I₃] [Enumtype I₄]
variable [Nonempty I₁] [Nonempty I₂] [Nonempty I₃] [Nonempty I₄]


--  ___           _     _
-- | _ \__ _ _ _ | |__ / |
-- |   / _` | ' \| / / | |
-- |_|_\__,_|_||_|_\_\ |_|

example (i : I₁)
  : (λ (f : I₁ → ℝ) => f i)† 
    = 
    λ f' i' => kron i i' * f' := 
by 
  conv => lhs; simp
  done


--  ___           _     ___
-- | _ \__ _ _ _ | |__ |_  )
-- |   / _` | ' \| / /  / /
-- |_|_\__,_|_||_|_\_\ /___|

-- Full evaluate
example (i j)
  : (λ (f : I₁ → I₂ → ℝ) => f i j)† 
    = 
    λ (f' : ℝ) i' j' => kron i i' * kron j j' * f' := 
by 
  conv => 
    lhs
    repeat' ext
    simp
  done

-- Get i-th row
example (i)
  : (λ (f : I₁ → I₂ → ℝ) j => f i j)† 
    = 
    λ (f' : I₂ → ℝ) i' j' => kron i i' * f' j' := 
by 
  conv => lhs; simp
  done

-- Get j-th column
example (j)
  : (λ (f : I₁ → I₂ → ℝ) i => f i j)† 
    = 
    λ (f' : I₁ → ℝ) i' j' => kron j j' * f' i' := 
by 
  conv => 
    lhs
    repeat' ext
    simp
  done

-- Transpose
example 
  : (λ (f : I₁ → I₂ → ℝ) j i => f i j)† 
    = 
    λ (f' : I₂ → I₁ → ℝ) i' j' => f' j' i' := 
by
  conv => 
    lhs
    repeat' ext
    simp
  done


-- Take diagonal 
example 
  : (λ (f : I₁ → I₁ → ℝ) i => f i i)† 
    = 
    λ (f' : I₁ → ℝ) i' j' => kron i' j' * f' i' := 
by
  conv => 
    lhs
    repeat' ext
    simp
  done

--  ___           _     ____
-- | _ \__ _ _ _ | |__ |__ /
-- |   / _` | ' \| / /  |_ \
-- |_|_\__,_|_||_|_\_\ |___/

-- Full evaluate
example (i j k)
  : (λ (f : I₁ → I₂ → I₃ → ℝ) => f i j k)† 
    = 
    λ f' i' j' k' => kron i i' * kron j j' * kron k k' * f' := 
by 
  conv => 
    lhs
    repeat' ext
    simp
  done

-- Fix i
example (i)
  : (λ (f : I₁ → I₂ → I₃ → ℝ) j k => f i j k)†
    = 
    λ f' i' j' k' => kron i i' * f' j' k' := 
by 
  conv => 
    lhs
    repeat' ext
    simp
  done

-- Fix j
example (j)
  : (λ (f : I₁ → I₂ → I₃ → ℝ) i k => f i j k)†
    = 
    λ f' i' j' k' => kron j j' * f' i' k' := 
by 
  conv => 
    lhs
    repeat' ext
    simp
    rw [sum_swap]
    simp only [kron_smul_assoc, sum_of_kron_2]
    simp
    simp only [CommRing.mul_comm (kron j _) _]
    simp only [kron_smul_assoc, sum_of_kron_2]
    simp
  done

-- Fix k
example (k)
  : (λ (f : I₁ → I₂ → I₃ → ℝ) i j => f i j k)†
    = 
    λ f' i' j' k' => kron k k' * f' i' j' := 
by 
  conv => 
    lhs
    repeat' ext
    simp
    rw [sum_swap]
    simp only [kron_smul_assoc, sum_of_kron_2]
    simp
    simp only [kron_smul_assoc, sum_of_kron_2]
    simp
  done

-- Fix j k
example (j k)
  : (λ (f : I₁ → I₂ → I₃ → ℝ) i => f i j k)†
    = 
    λ f' i' j' k' => kron j j' * kron k k' * f' i' := 
by
  conv =>
    lhs
    repeat' ext
    simp
    simp only [kron_smul_assoc, sum_of_kron_2]
    simp
  done

-- Fix i k
example (i k)
  : (λ (f : I₁ → I₂ → I₃ → ℝ) j => f i j k)†
    = 
    λ f' i' j' k' => kron i i' * kron k k' * f' j' := 
by
  conv =>
    lhs
    repeat' ext
    simp
    simp only [CommRing.mul_comm (kron i _) _]
    simp only [kron_smul_assoc, sum_of_kron_2]
    simp
  done

-- Fix i j
example (i j)
  : (λ (f : I₁ → I₂ → I₃ → ℝ) k => f i j k)†
    = 
    λ f' i' j' k' => kron i i' * kron j j' * f' k' := 
by
  conv =>
    lhs
    repeat' ext
    simp
    simp only [CommRing.mul_comm (kron i _ * kron j _) _]
    simp only [kron_smul_assoc, sum_of_kron_2]
    simp
  done

-- Fix i and transpose
set_option trace.Meta.Tactic.simp.discharge true in
example (i)
  : (λ (f : I₁ → I₂ → I₃ → ℝ) k j => f i j k)†
    = 
    λ f' i' j' k' => kron i i' * f' k' j' := 
by 
  conv => 
    lhs
    repeat' ext
    simp
  done




#exit
