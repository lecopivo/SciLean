import SciLean

open SciLean

def conv1d {n} (k) (w : Fin k → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  λ i => ∑ j, w j * x (i.shift j)


set_option trace.Meta.Tactic.fun_trans.rewrite true
set_option trace.Meta.Tactic.fun_trans.step true
set_option trace.Meta.Tactic.fun_trans.normalize_let true
set_option trace.Meta.Tactic.fun_trans.lambda_special_cases true
function_properties conv1d {n} [Nonempty (Fin n)] (k) (w : Fin k → ℝ) (x : Fin n → ℝ)
argument x
  def ∂† by
    unfold conv1d; simp
    fun_trans; fun_trans


def conv2d {n m} (k l) (w : ℝ^{k,l}) (x : ℝ^{n,m}) : ℝ^{n,m} :=
  ⊞ i, ∑ j, w[j] * x[i.1.shift j.1, i.2.shift j.2]


-- function_properties conv2d {n m} [Nonempty (Fin m)] [Nonempty (Fin n)] [Nonempty (Fin n × Fin m)] 
-- [∀ a b, IsInv fun i : Fin n × Fin m => (i.1.shift a, i.2.shift b)]
-- (k l) (w : ℝ^{k,l}) (x : ℝ^{n,m})
-- argument x
--   def ∂† by
--     unfold conv2d; simp
--     fun_trans; fun_trans; fun_trans
