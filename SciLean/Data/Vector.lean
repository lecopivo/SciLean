import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Defs

import SciLean.Data.ArrayOperations.Basic
import SciLean.Util.SorryProof

namespace SciLean

-- Array Operations

-- this is potentially evil instance as `Vector α n` already has `GetElem` but with different dom
instance : GetElem' (Vector α n) (Fin n) α where
  getElem xs i h := xs[i]

instance : InjectiveGetElem (Vector α n) (Fin n) where
  getElem_injective := sorry_proof

instance : DefaultIndex (Vector α n) (Fin n) where

instance : SetElem' (Vector α n) (Fin n) α where
  setElem x i v _ := x.set i v
  setElem_valid := by simp

instance : LawfulSetElem (Vector α n) (Fin n) where
  getElem_setElem_eq := sorry_proof
  getElem_setElem_neq := sorry_proof

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
  simp[getElem,HAdd.hAdd,Add.add]; unfold Vector.get; simp

@[simp, simp_core]
theorem Vector.getElem_sub [Sub X] (x y : Vector X n) (i : ℕ) (h : i < n) : (x - y)[i] = x[i] - y[i] := by
  simp[getElem,HSub.hSub,Sub.sub]; unfold Vector.get; simp

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
  nsmul_zero := by sorry_proof
  nsmul_succ := by sorry_proof
  zsmul := fun n x => x.map fun xi => n • xi
  zsmul_zero' := sorry_proof
  zsmul_succ' := sorry_proof
  zsmul_neg' := by sorry_proof
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
