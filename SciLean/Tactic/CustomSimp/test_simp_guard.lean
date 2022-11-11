import SciLean.Tactic.CustomSimp.AllPrePost

open SciLean

variable {α β γ δ : Type}

def D (f : α → β) : α → α → β := sorry

theorem D_comp
  (f : β → γ) (g : α → β)
  : D (λ x => f (g x)) = λ x dx => D f (g x) (D g x dx) := sorry


@[simp_guard g (λ x => x)]
theorem D_comp_parm
  (f : β → δ → γ) (g : α → β) (d : δ)
  : D (λ x => f (g x) d) = λ x dx => D (λ y => f y d) (g x) (D g x dx) :=
by
  apply D_comp (λ y => f y d) g -- we have to specify `f` explicitly


set_option trace.Meta.Tactic.simp.discharge true in
example
  (f : β → δ → γ) (g : α → β) (d : δ)
  : D (λ x => f (g x) d) = λ x dx => D (λ y => f y d) (g x) (D g x dx) :=
by
  -- simp [D_comp_parm] -- normal `simp` fails with timeout
  scilean_simp [D_comp_parm]
  done
