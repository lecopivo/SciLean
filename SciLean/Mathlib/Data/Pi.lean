import Mathlib.Algebra.Group.Basic

section FunctionOperations

  variable {α : Type u} {β : (a : α) → Type v} {γ : Type w}
  
  instance [∀ a, Add (β a)] : Add ((a : α) → β a) := ⟨λ f g => λ a => f a + g a⟩
  instance [∀ a, Sub (β a)] : Sub ((a : α) → β a) := ⟨λ f g => λ a => f a - g a⟩
  instance [∀ a, Mul (β a)] : Mul ((a : α) → β a) := ⟨λ f g => λ a => f a * g a⟩
  instance [∀ a, Div (β a)] : Div ((a : α) → β a) := ⟨λ f g => λ a => f a / g a⟩

  instance [∀ a, HMul γ (β a) (β a)] : HMul γ ((a : α) → β a) ((a : α) → β a) := ⟨λ c f => λ a => c * (f a)⟩

  instance [∀ a, Neg (β a)] : Neg ((a : α) → β a) := ⟨λ f => λ a => - f a⟩

  instance [∀ a, Zero (β a)] : Zero ((a : α) → β a) := ⟨λ _ => 0⟩
  instance [∀ a, One (β a)] : One ((a : α) → β a) := ⟨λ _ => 1⟩

  variable (f g : (a : α) → β a) (a : α)

  @[simp] theorem fun_add_eval [∀ a, Add (β a)] 
    : (f + g) a = f a + g a := by simp[HAdd.hAdd,Add.add] done
  @[simp] theorem fun_sub_eval [∀ a, Sub (β a)] 
    : (f - g) a = f a - g a := by simp[HSub.hSub,Sub.sub] done
  @[simp] theorem fun_mul_eval [∀ a, Mul (β a)] 
    : (f * g) a = f a * g a := by simp[HMul.hMul,Mul.mul] done
  @[simp] theorem fun_div_eval [∀ a, Div (β a)] 
    : (f / g) a = f a / g a := by simp[HDiv.hDiv,Div.div] done

  @[simp] theorem fun_hmul_eval [∀ a, HMul γ (β a) (β a)] (c : γ)
    : (c * f) a = c * (f a) := by simp[HMul.hMul] done

end FunctionOperations
