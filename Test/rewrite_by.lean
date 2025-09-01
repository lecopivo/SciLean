import SciLean

set_option pp.proofs false

/-- info: ⋯ : True -/
#guard_msgs in
#check (by simp : 1 * 5 = 5) rewrite_type_by simp
