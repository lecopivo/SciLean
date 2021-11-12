import SciLean.Categories.Set.Basic

namespace SciLean.Set

variable {X : Type u} {Y : Type v} {Z : Type w}

def id (x : X) := x
def const (Y : Type v) (x : X) (y : Y) := x
def comp (f : Y→Z) (g : X→Y) (x : X) := f (g x)
def swap (f : X→Y→Z) (y : Y) (x : X) := f x y
def diag (f : X→X→Y) (x : X) := (f x x)

abbrev subs (f : X→Y→Z) (g : X→Y) : X → Z := diag (comp (swap comp g) f)

@[simp] def const_reduce (Y : Type v) (x : X) (y : Y) : const Y x y = x  := by simp[const]
@[simp] def comp_reduce (f : Y→Z) (g : X→Y) (x : X) : (comp f g x) = f (g x) := by simp[comp]
@[simp] def swap_reduce (f : X→Y→Z) (y : Y) (x : X) : (swap f y x) = f x y := by simp[swap]
@[simp] def diag_reduce (f : X→X→Y) (x : X) : (diag f x) = f x x := by simp[diag]

@[simp] def subs_reduce (f : X→Y→Z) (g : X→Y) (x : X) : (subs f g x) = (f x) (g x) := by simp[subs] done

abbrev curry : (X × Y → Z) → (X → Y → Z) := (swap (comp comp comp) Prod.mk)
abbrev uncurry : (X → Y → Z) → (X × Y → Z) := (swap (comp subs (swap comp Prod.fst)) Prod.snd)
