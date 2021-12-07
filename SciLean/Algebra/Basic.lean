import Mathlib.Data.Iterable
-- import SciLean.Std.Enumtype

instance : Neg (Fin n) :=
  ⟨λ x =>
     match n, x with
       | 0, x => x
       | (n+1), x => 0 - x⟩

example (x : Fin n) : x = -x := sorry

instance [Zero α] : Inhabited α := ⟨0⟩
instance [One α] : Inhabited α := ⟨1⟩

instance : Zero Nat := ⟨0⟩
instance : Zero Float := ⟨0.0⟩
instance : One Nat := ⟨1⟩
instance : One Float := ⟨1.0⟩

section UnitOperations

  instance : Add PUnit := ⟨λ x y => PUnit.unit⟩
  instance : Sub PUnit := ⟨λ x y => PUnit.unit⟩
  instance : Mul PUnit := ⟨λ x y => PUnit.unit⟩
  instance : Neg PUnit := ⟨λ x => PUnit.unit⟩
  
  instance : Zero PUnit := ⟨PUnit.unit⟩
 
end UnitOperations

section ProductOperations

  variable {α : Type u} {β : Type v} {γ : Type w}

  instance [Add α] [Add β] : Add (α × β) := ⟨λ p q => (p.1 + q.1, p.2 + q.2)⟩
  instance [Sub α] [Sub β] : Sub (α × β) := ⟨λ p q => (p.1 - q.1, p.2 - q.2)⟩
  instance [Mul α] [Mul β] : Mul (α × β) := ⟨λ p q => (p.1 * q.1, p.2 * q.2)⟩
  instance [Div α] [Div β] : Div (α × β) := ⟨λ p q => (p.1 / q.1, p.2 / q.2)⟩

  -- instance {α β γ} [HAdd α γ α] [HAdd β γ β] : HAdd (α×β) γ (α×β) := ⟨λ p c => (p.1+c, p.2+c)⟩
  -- instance {α β γ} [HAdd γ α α] [HAdd γ β β] : HAdd γ (α×β) (α×β) := ⟨λ c p => (c+p.1, c+p.2)⟩
  -- instance {α β γ} [HSub α γ α] [HSub β γ β] : HSub (α×β) γ (α×β) := ⟨λ p c => (p.1-c, p.2-c)⟩
  -- instance {α β γ} [HMul α γ α] [HMul β γ β] : HMul (α×β) γ (α×β) := ⟨λ p c => (p.1*c, p.2*c)⟩
  instance {α β γ} [HMul γ α α] [HMul γ β β] : HMul γ (α×β) (α×β) := ⟨λ c p => (c*p.1, c*p.2)⟩
  -- instance {α β γ} [HDiv α γ α] [HDiv β γ β] : HDiv (α×β) γ (α×β) := ⟨λ p c => (p.1/c, p.2/c)⟩

  instance [Neg α] [Neg β] : Neg (α × β) := ⟨λ p => (-p.1, -p.2)⟩

  instance [Zero α] [Zero β] : Zero (α × β) := ⟨(0, 0)⟩
  instance [One α] [One β] : One (α × β) := ⟨(1, 1)⟩

end ProductOperations


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
