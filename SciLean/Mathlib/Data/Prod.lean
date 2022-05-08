import Mathlib.Algebra.Group.Basic

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
