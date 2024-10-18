import Aesop
import SciLean.Util.SorryProof
import SciLean.Data.ArrayType

namespace SciLean

structure ArrayN (α : Type u) (n : Nat) where
  data : Array α
  h_size : n = data.size

def ArrayN.ofFn (f : Fin n → α) : ArrayN α n :=
{
  data := .ofFn f
  h_size := by simp
}

def ArrayN.mapIdx {α β : Type*} (a : ArrayN α n) (f : Fin n → α → β) : ArrayN β n :=
{
  data := a.data.mapIdx (λ i v => f ⟨i, by have := a.2; omega⟩ v)
  h_size := by simp[a.2]
}

def ArrayN.map {α β : Type*} (a : ArrayN α n) (f : α → β) : ArrayN β n := a.mapIdx (fun _ => f)


instance : ArrayType (ArrayN α n) (Fin n) α where
  ofFn := ArrayN.ofFn
  get := fun a i => a.data.get ⟨i, by have := a.2; have := i.2; simp_all⟩
  set := fun a i v => {
    data := a.data.set ⟨i.1, by have := a.2; omega⟩ v
    h_size := by have := a.2; simp_all
  }
  modify := fun a i f => {
    data := a.data.modify i f
    h_size := by have := a.2; simp_all
  }
  get_ofFn := by intro i; simp[ArrayN.ofFn]
  ofFn_get := by intro f; simp[ArrayN.ofFn]
  get_set_eq := by
    intro a i v; simp
  get_set_neq := by
    intro a i j v h; simp [h]
    sorry_proof
  modify_set := by
    intro a i v; simp
    sorry_proof
instance : GetElem (ArrayN α n) (Fin n) α (λ _ _ => True) where
  getElem arr i _ := arr.data.get ⟨i.1, by have := arr.2; omega⟩


@[simp]
theorem ArrayN.ofFn_get (f : Fin n → α) (i : Fin n) :
    (ofFn f)[i] = f i := by
  sorry_proof

@[simp]
def ArrayN.mk_get (data : Array α) (h_size : n = data.size) (i : Fin n) :
  (ArrayN.mk data h_size)[i] = data[i] := by rfl

@[simp]
def ArrayN.get_normalize (a : ArrayN α n) (i : Fin n) :
  have := a.2
  a.data[i.1] = a[i] := by simp[ArrayType.get]


instance [Inhabited α] : Inhabited (ArrayN α n) :=
  ⟨{
    data := .mkArray n default
    h_size := by simp
  }⟩
