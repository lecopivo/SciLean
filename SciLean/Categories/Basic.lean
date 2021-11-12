namespace SciLean

variable {X : Type u} {Y : Type v} {Z : Type w}

def id (x : X) := x
def const (Y : Type v) (x : X) (y : Y) := x
def comp (f : Y→Z) (g : X→Y) (x : X) := f (g x)
def swap (f : X→Y→Z) (y : Y) (x : X) := f x y
def diag (f : X→X→Y) (x : X) := (f x x)

abbrev subs (f : X→Y→Z) (g : X→Y) : X → Z := diag (comp (swap comp g) f)

@[simp] def id_reduce (x : X) : id x = x := by simp[id]
@[simp] def const_reduce (Y : Type v) (x : X) (y : Y) : const Y x y = x  := by simp[const]
@[simp] def comp_reduce (f : Y→Z) (g : X→Y) (x : X) : (comp f g x) = f (g x) := by simp[comp]
@[simp] def swap_reduce (f : X→Y→Z) (y : Y) (x : X) : (swap f y x) = f x y := by simp[swap]
@[simp] def diag_reduce (f : X→X→Y) (x : X) : (diag f x) = f x x := by simp[diag]

@[simp] def subs_reduce (f : X→Y→Z) (g : X→Y) (x : X) : (subs f g x) = (f x) (g x) := by simp[subs] done

abbrev curry : (X × Y → Z) → (X → Y → Z) := (swap (comp comp comp) Prod.mk)
abbrev uncurry : (X → Y → Z) → (X × Y → Z) := (swap (comp subs (swap comp Prod.fst)) Prod.snd)

class FetchProof {α} (P : α → Prop) (a : α) where
  (fetch_proof : P a)

instance (P : X → Prop) (x : X) [FetchProof P x] : P (id x) := by simp; apply FetchProof.fetch_proof
instance (P : X → Prop) (x : X) (y : Y) [FetchProof P x] : P (const Y x y) := by simp; apply FetchProof.fetch_proof
instance (P : Z → Prop) (f : X → Y → Z) (x : X) (y : Y) [FetchProof P (f x y)] : P (swap f y x) := by simp; apply FetchProof.fetch_proof
instance (P : Z → Prop) (f : Y → Z) (g : X → Y) (x : X) [FetchProof P (f (g x))] : P (comp f g x) := by simp; apply FetchProof.fetch_proof
   -- instance (P : Z → Prop) (f : X → Y → Z) (g : X → Y) (x : X) [FetchProof P ((f x) (g x))] : P (subs f g x) := by simp; apply FetchProof.fetch_proof
instance (P : Y → Prop) (f : X → X → Y) (x : X) [FetchProof P (f x x)] : P (diag f x) := by simp; apply FetchProof.fetch_proof


   -- Extra arguments reduction -- is this enough?
variable {α : Type _}
instance (P : Z → Prop) (f : X → Y → α → Z) (x : X) (y : Y) (a : α) [FetchProof P (f x y a)] : P (swap f y x a) := by simp; apply FetchProof.fetch_proof
instance (P : Z → Prop) (f : Y → α → Z) (g : X → Y) (x : X) (a : α) [FetchProof P (f (g x) a)] : P (comp f g x a) := by simp; apply FetchProof.fetch_proof
   -- instance (P : Z → Prop) (f : X → Y → α → Z) (g : X → Y) (x : X) (a : α) [FetchProof P ((f x) (g x) a)] : P (subs f g x a) := by simp; apply FetchProof.fetch_proof
instance (P : Y → Prop) (f : X → X → α → Y) (x : X) (a : α) [FetchProof P (f x x a)] : P (diag f x a) := by simp; apply FetchProof.fetch_proof
