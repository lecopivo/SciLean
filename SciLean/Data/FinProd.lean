-- import SciLean.Mathlib.Data.PUnit
-- import SciLean.Mathlib.Data.Prod
-- import SciLean.Mathlib.Data.Enumtype
import SciLean.Data.EnumType
 
namespace SciLean

/-- Give `Fin n₁ × ... × Fin nₘ` for a list `[n₁,..., nₘ]`  -/
def FinProd : List Nat → Type
  | [] => Unit
  | [n] => Fin n
  | n :: (m :: ns) => Fin n × FinProd (m :: ns)

instance instEnumtypeFinProd (l : List Nat) : Enumtype (FinProd l) := 
  match l with
  | []  => by simp[FinProd]; infer_instance
  | [n] => by simp[FinProd]; infer_instance
  | n :: m :: ns => 
    have e := instEnumtypeFinProd (m :: ns)
    by simp[FinProd]; infer_instance

instance instEnumTypeFinProd (l : List Nat) : EnumType (FinProd l) := 
  match l with
  | []  => by simp[FinProd]; infer_instance
  | [n] => by simp[FinProd]; infer_instance
  | n :: m :: ns => 
    have e := instEnumTypeFinProd (m :: ns)
    by simp[FinProd]; infer_instance

instance instToStringFinProd (l : List Nat) : ToString (FinProd l) := 
  match l with
  | []  => by simp[FinProd]; infer_instance
  | [n] => by simp[FinProd]; infer_instance
  | n :: m :: ns => 
    have e := instToStringFinProd (m :: ns)
    by simp[FinProd]; infer_instance

instance instAddFinProd (l : List Nat) : Add (FinProd l) := 
  match l with
  | []  => by simp[FinProd]; infer_instance
  | [n] => by simp[FinProd]; infer_instance
  | n :: m :: ns => 
    have e := instAddFinProd (m :: ns)
    by simp[FinProd]; infer_instance

instance instSubFinProd (l : List Nat) : Sub (FinProd l) := 
  match l with
  | []  => by simp[FinProd]; infer_instance
  | [n] => by simp[FinProd]; infer_instance
  | n :: m :: ns => 
    have e := instSubFinProd (m :: ns)
    by simp[FinProd]; infer_instance

instance instMulFinProd (l : List Nat) : Mul (FinProd l) := 
  match l with
  | []  => by simp[FinProd]; infer_instance
  | [n] => by simp[FinProd]; infer_instance
  | n :: m :: ns => 
    have e := instMulFinProd (m :: ns)
    by simp[FinProd]; infer_instance

/-- Given `(i₁, ..., iₘ) : Fin n₁ × ... × Fin nₘ` return `[i₁.1,..., iₘ.1]` -/
def FinProd.toList {l} (is : FinProd l) : List Nat :=
  match l, is with
  | [], _ => []
  | [_], i => [i.1]
  | _ :: _ :: _, (i, is) => i :: is.toList

-- /-- Given a list of values `[i₁,..., iₖ]` produce `(i₁ % n₁, ..., iₘ % nₘ) : Fin n₁ × ... × Fin nₘ`.
-- If `k > m` aditional values are ignored. If `k < n` then those extra values are set to zero. -/
-- def FinProd.fromList {l} (vals : List Nat) : FinProd l :=
--   match l, vals with
--   | [],  _ => Unit.unit
--   | [n], [i] => ⟨i % n, sorry⟩
--   | n :: m :: ns, i :: j :: is => (⟨i % n, sorry⟩, fromList (j :: is))
--   | [n], [] => 

/-- Given `(i₁, ..., iₘ) : Fin n₁ × ... × Fin nₘ` return `[n₁-i₁.1-1,..., nₘ-iₘ.1-1]` -/
def FinProd.toListComplement {l} (is : FinProd l) : List Nat :=
  match l, is with
  | [], _ => []
  | [n], i => [n-i.1-1]
  | n :: _ :: _, (i, is) => (n-i.1-1) :: is.toListComplement

