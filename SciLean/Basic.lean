universe u v w u' v' w'

notation "ℕ" => Nat
notation "ℤ" => Int

def curry {α : Type u} {β : Type v} {γ : Type w} (f : α × β → γ) : α → β → γ := λ x y => f (x, y)
def uncurry {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) : α × β → γ := λ p => f p.1 p.2
def diag {α : Type u} : α → α × α := (λ x => (x, x))


def const {X : Type u} (Y : Type u) (x : X) (y : Y) := x
def comp {X Y Z : Type u} (f : Y→Z) (g : X→Y) (x : X) := f (g x)
def swap {X Y Z : Type u} (f : X→Y→Z) (y : Y) (x : X) := f x y
def subs {X Y Z : Type u} (f : X→Y→Z) (g : X→Y) (x : X) := (f x) (g x)

@[simp] def id.reduce {X} (x : X) : id x = x := by simp
@[simp] def const.reduce {X Y} (x : X) (y : Y) : const Y x y = x := by simp[const]
@[simp] def swap.reduce {X Y Z} (f : X → Y → Z) (x : X) (y : Y) : swap f y x = f x y := by simp[swap]
@[simp] def comp.reduce {X Y Z} (f : Y → Z) (g : X → Y) (x : X) : comp f g x = f (g x) := by simp [comp]
@[simp] def subs.reduce {X Y Z} (f : X → Y → Z) (g : X → Y) (x : X) : subs f g x = (f x) (g x) := by simp[subs]

def Prod.fmap {α : Type u} {α' : Type u'} {β : Type v} {β' : Type v'} (f : α → β) (f' : α' → β') : α × α' → β × β' := (λ p => (f p.1, f' p.2))

class Inv (α : Type u) where
  inv : α → α

postfix:100 "⁻¹" => Inv.inv

class Norm (α : Type) where
  norm : α → Float

instance : Norm Float := ⟨λ x => Float.sqrt (x*x)⟩
instance {α β} [Norm α] [Norm β] : Norm (α×β) := ⟨λ p => Float.sqrt ((Norm.norm p.1)^2.0 + (Norm.norm p.2)^2.0)⟩

def norm {α} [Norm α] (a : α) : Float := Norm.norm a

macro "∥" t:term "∥" : term => `(norm $t)

class Zero (α : Type u) where
  zero : α
class One (α : Type u) where
  one : α

instance instOfNatZero [Zero α] : OfNat α (nat_lit 0) where
  ofNat := Zero.zero

instance instOfNatOne [One α] : OfNat α (nat_lit 1) where
  ofNat := One.one

def zero {α : Type u} [Zero α] : α := Zero.zero
def one {α : Type u} [One α] : α := One.one

instance [Zero α] : Inhabited α := ⟨zero⟩
instance [One α] : Inhabited α := ⟨one⟩

instance : Zero Nat := ⟨0⟩
instance : Zero Float := ⟨0.0⟩
instance : One Nat := ⟨1⟩
instance : One Float := ⟨1.0⟩

class IsNonZero {α : Type u} [Zero α] (x : α) : Prop where
  isNonZero : x ≠ zero

class IsPositive {α : Type u} [Zero α] [LT α] (x : α) : Prop where
  isPositive : x > zero

class IsNegative {α : Type u} [Zero α] [LT α] (x : α) : Prop where
  isNegative : x < zero

class IsNonNegative {α : Type u} [Zero α] [LE α] (x : α) : Prop where
  isNonNegative : x ≥ zero

class IsNonPositive {α : Type u} [Zero α] [LE α] (x : α) : Prop where
  isNonPositive : x ≤ zero


section ProductOperations

  variable {α : Type u} {β : Type v} {γ : Type w}

  instance [Add α] [Add β] : Add (α × β) := ⟨λ p q => (p.1 + q.1, p.2 + q.2)⟩
  instance [Sub α] [Sub β] : Sub (α × β) := ⟨λ p q => (p.1 - q.1, p.2 - q.2)⟩
  instance [Mul α] [Mul β] : Mul (α × β) := ⟨λ p q => (p.1 * q.1, p.2 * q.2)⟩
  instance [Div α] [Div β] : Div (α × β) := ⟨λ p q => (p.1 / q.1, p.2 / q.2)⟩

  instance {α β γ} [HAdd α γ α] [HAdd β γ β] : HAdd (α×β) γ (α×β) := ⟨λ p c => (p.1+c, p.2+c)⟩
  instance {α β γ} [HAdd γ α α] [HAdd γ β β] : HAdd γ (α×β) (α×β) := ⟨λ c p => (c+p.1, c+p.2)⟩
  instance {α β γ} [HSub α γ α] [HSub β γ β] : HSub (α×β) γ (α×β) := ⟨λ p c => (p.1-c, p.2-c)⟩
  instance {α β γ} [HMul α γ α] [HMul β γ β] : HMul (α×β) γ (α×β) := ⟨λ p c => (p.1*c, p.2*c)⟩
  instance {α β γ} [HMul γ α α] [HMul γ β β] : HMul γ (α×β) (α×β) := ⟨λ c p => (c*p.1, c*p.2)⟩
  instance {α β γ} [HDiv α γ α] [HDiv β γ β] : HDiv (α×β) γ (α×β) := ⟨λ p c => (p.1/c, p.2/c)⟩

  instance [Neg α] [Neg β] : Neg (α × β) := ⟨λ p => (-p.1, -p.2)⟩
  instance [Inv α] [Inv β] : Inv (α × β) := ⟨λ p => (p.1⁻¹, p.2⁻¹)⟩

  instance [Zero α] [Zero β] : Zero (α × β) := ⟨(zero, zero)⟩
  instance [One α] [One β] : One (α × β) := ⟨(one, one)⟩

end ProductOperations


section FunctionOperations

  variable {α : Type u} {β : Type v} {γ : Type w}

  instance [Add β] : Add (α → β) := ⟨λ f g => λ a => f a + g a⟩
  instance [Sub β] : Sub (α → β) := ⟨λ f g => λ a => f a - g a⟩
  instance [Mul β] : Mul (α → β) := ⟨λ f g => λ a => f a * g a⟩
  instance [Div β] : Div (α → β) := ⟨λ f g => λ a => f a / g a⟩

  instance [HMul γ β β] : HMul γ (α → β) (α → β) := ⟨λ s f => λ a => s * (f a)⟩

  instance [Neg β] : Neg (α → β) := ⟨λ f => λ a => - f a⟩
  instance [Inv β] : Inv (α → β) := ⟨λ f => λ a => (f a)⁻¹⟩

  instance [Zero β] : Zero (α → β) := ⟨λ _ => zero⟩
  instance [One β] : One (α → β) := ⟨λ _ => one⟩

end FunctionOperations

def sum {n α} [Zero α] [Add α] (f : Fin n → α) : α := do
  let mut r := zero 
  for i in [0:n] do
    r := r + f ⟨i, sorry⟩
  r
  -- match n with
  --   | 0 => zero
  --   | 1 => f ⟨0, sorry⟩
  --   | n+1 => (sum (λ i : Fin n => f ⟨i, sorry⟩)) + f ⟨n, sorry⟩

macro "∑" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders `sum xs b

def big_product {n α} [One α] [Mul α] (f : Fin n → α) : α :=
  match n with
    | 0 => one
    | 1 => f ⟨0, sorry⟩
    | n+1 => (big_product (λ i : Fin n => f ⟨i, sorry⟩)) * f ⟨n, sorry⟩

macro "∏" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders `big_product xs b




