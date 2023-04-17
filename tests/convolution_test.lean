import SciLean

open SciLean

example : IsInv (λ xy : Nat × Nat => xy) := by infer_instance

example : IsInv (λ xy : Nat × Nat => (xy.1,xy.2)) := by infer_instance

instance [Nonempty α] [Nonempty β] (f : α → α') (g : β → β') [IsInv f] [IsInv g]
  : IsInv λ xy : α×β => (f xy.1, g xy.2) := sorry_proof

instance hoho [Nonempty α] [Nonempty β] (f : α → α') (g : β → β') [IsInv f] [IsInv g]
  : IsInv λ xy : α×β => (g xy.snd, f xy.fst) := sorry_proof

example : IsInv (λ xy : Int × Int => (1 + xy.snd, 2 + xy.fst)) := by infer_instance

theorem prodMap.invFun [Nonempty α] [Nonempty β] (f : α → α') (g : β → β') [IsInv f] [IsInv g]
  : (λ xy : α×β => (f xy.fst, g xy.snd))⁻¹
    =
    (λ xy : α'×β' => (f⁻¹ xy.fst, g⁻¹ xy.snd))
  := sorry

theorem prodMap.invFun' [Nonempty α] [Nonempty β] (f : α → α') (g : β → β') [IsInv f] [IsInv g]
  : (λ xy : α×β => (f xy.fst, g xy.snd))⁻¹
    =
    (λ xy : α'×β' => (f⁻¹ xy.fst, g⁻¹ xy.snd))
  := sorry

#check Prod.mk.arg_fstsnd.IsInv'

set_option trace.Meta.Tactic.fun_trans.step true in
set_option trace.Meta.Tactic.fun_trans.rewrite true in
#check (λ xy : Int × Int => (1 + xy.1, 3 + xy.2))⁻¹ rewrite_by simp only [prodMap.invFun]; fun_trans

#check (λ xy : Int × Int => (1 + xy.2, 3 + xy.1))⁻¹ rewrite_by simp only [prodMap.invFun];


#exit 
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
