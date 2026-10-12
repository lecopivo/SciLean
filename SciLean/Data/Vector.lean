module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs

public import SciLean.Data.ArrayOperations.Basic
public import SciLean.Util.SorryProof

@[expose] public section


namespace SciLean

-- Array Operations

-- this is potentially evil instance as `Vector α n` already has `GetElem` but with different dom
instance : GetElem' (Vector α n) (Fin n) α where
  getElem xs i h := xs[i]

instance : InjectiveGetElem (Vector α n) (Fin n) where
  getElem_injective := by
    intro x y h
    ext i hi
    exact congrFun h ⟨i,hi⟩

instance : DefaultIndex (Vector α n) (Fin n) where

instance : SetElem' (Vector α n) (Fin n) α where
  setElem x i v _ := x.set i v
  setElem_valid := by simp

instance : LawfulSetElem (Vector α n) (Fin n) where
  getElem_setElem_eq := by
    intro xs i v _
    simp only [getElem, setElem, Vector.get, Fin.val_cast]
    exact Vector.getElem_set_self _
  getElem_setElem_neq := by
    intro xs i j v _ _ hij
    simp only [getElem, setElem, Vector.get, Fin.val_cast]
    exact Vector.getElem_set_ne i.isLt j.isLt (Fin.val_ne_of_ne hij)

instance : OfFn (Vector α n) (Fin n) α where
  ofFn := Vector.ofFn

instance : LawfulOfFn (Vector α n) (Fin n) where
  getElem_ofFn := by
    simp[getElem,ofFn,Vector.ofFn]
    unfold Vector.get
    simp

@[simp, simp_core]
theorem Vector.getElem_map{α β n} (f : α → β) (x : Vector α n) (i : Fin n) :
    (x.map f)[i] = f (x[i]) := by
  simp[getElem,Vector.map]; unfold Vector.get; simp


-- Algebraic Operations
instance [Add X] : Add (Vector X n) := ⟨fun x y => x.mapFinIdx fun i xi _ => xi + y[i]⟩
instance [Sub X] : Sub (Vector X n) := ⟨fun x y => x.mapFinIdx fun i xi _ => xi - y[i]⟩
instance [Neg X] : Neg (Vector X n) := ⟨fun x => x.map fun xi => -xi⟩
instance [SMul R X] : SMul R (Vector X n) := ⟨fun r x => x.map fun xi => r • xi⟩
instance [Zero X] : Zero (Vector X n) := ⟨⟨Array.replicate n (0:X), by simp⟩⟩

@[simp, simp_core]
theorem Vector.getElem_add [Add X] (x y : Vector X n) (i : ℕ) (h : i < n) : (x + y)[i] = x[i] + y[i] := by
  simp [HAdd.hAdd, Add.add, Vector.getElem_mapFinIdx]

@[simp, simp_core]
theorem Vector.getElem_sub [Sub X] (x y : Vector X n) (i : ℕ) (h : i < n) : (x - y)[i] = x[i] - y[i] := by
  simp [HSub.hSub, Sub.sub, Vector.getElem_mapFinIdx]

@[simp, simp_core]
theorem Vector.getElem_neg [Neg X] (x : Vector X n) (i : ℕ) (h : i < n) : (-x)[i] = -x[i] := by
  simp[getElem,Neg.neg,Vector.map]; unfold Vector.get; simp

@[simp, simp_core]
theorem Vector.getElem_smul [SMul R X] (r : R) (x : Vector X n) (i : ℕ) (h : i < n) : (r • x)[i] = r • x[i] := by
  simp[getElem,HSMul.hSMul,SMul.smul,Vector.map]; unfold Vector.get; simp

@[simp, simp_core]
theorem Vector.getElem_zero [Zero X] (i : ℕ) (h : i < n) : (0 : Vector X n)[i] = 0 := by
  simp[getElem,Zero.zero,OfNat.ofNat]; unfold Vector.get; simp

-- set_option pp.fieldNotation false
-- set_option pp.notation false
-- Algebraic instances
instance [AddCommGroup X] : AddCommGroup (Vector X n) where
  add_assoc := by intros; ext i; simp[add_assoc]
  zero_add := by intros; ext i; simp[zero_add]
  add_zero := by intros; ext i; simp[add_zero]
  nsmul := fun n x => x.map fun xi => n • xi
  nsmul_zero := by intros; ext i; simp
  nsmul_succ := by intros; ext i; simp [succ_nsmul]
  zsmul := fun n x => x.map fun xi => n • xi
  zsmul_zero' := by intros; ext i; simp
  zsmul_succ' := by intros; ext i; simp [add_zsmul]
  zsmul_neg' := by intros; ext i; simp [add_zsmul, natCast_zsmul, succ_nsmul, add_comm]
  neg_add_cancel := by intros; ext i; simp[neg_add_cancel]
  add_comm := by intros; ext i; simp[add_comm]
  sub_eq_add_neg := by intros; ext i; simp[sub_eq_add_neg]

instance [Semiring R] [AddCommGroup X] [Module R X] : Module R (Vector X n) where
  one_smul := by intros; ext i; simp[one_smul]
  mul_smul := by intros; ext i; simp[mul_smul]
  smul_zero := by intros; ext i; simp[smul_zero]
  smul_add := by intros; ext i; simp[smul_add]
  add_smul := by intros; ext i; simp[add_smul]
  zero_smul := by intros; ext i; simp[zero_smul]
