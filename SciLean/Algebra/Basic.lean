
class Zero (α : Type u) where
  zero : α
class One (α : Type u) where
  one : α

instance instOfNatZero [Zero α] : OfNat α (nat_lit 0) where
  ofNat := Zero.zero

instance instOfNatOne [One α] : OfNat α (nat_lit 1) where
  ofNat := One.one

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

  variable {α : Type u} {β : Type v} {γ : Type w}

  instance [Add β] : Add (α → β) := ⟨λ f g => λ a => f a + g a⟩
  instance [Sub β] : Sub (α → β) := ⟨λ f g => λ a => f a - g a⟩
  instance [Mul β] : Mul (α → β) := ⟨λ f g => λ a => f a * g a⟩
  instance [Div β] : Div (α → β) := ⟨λ f g => λ a => f a / g a⟩

  instance [HMul γ β β] : HMul γ (α → β) (α → β) := ⟨λ s f => λ a => s * (f a)⟩

  instance [Neg β] : Neg (α → β) := ⟨λ f => λ a => - f a⟩

  instance [Zero β] : Zero (α → β) := ⟨λ _ => 0⟩
  instance [One β] : One (α → β) := ⟨λ _ => 1⟩

end FunctionOperations
