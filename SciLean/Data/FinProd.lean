import SciLean.Data.IndexType

namespace SciLean
#exit
/-- Give `Fin n₁ × ... × Fin nₘ` for a list `[n₁,..., nₘ]`  -/
def FinProd : List Nat → Type
  | [] => Unit
  | [n] => Fin n
  | n :: (m :: ns) => Fin n × FinProd (m :: ns)

instance instIndexTypeFinProd (l : List Nat) : IndexType (FinProd l) :=
  match l with
  | []  => by simp[FinProd]; infer_instance
  | [n] => by simp[FinProd]; infer_instance
  | n :: m :: ns =>
    have e := instIndexTypeFinProd (m :: ns)
    by simp[FinProd]; infer_instance

instance instToStringFinProd (l : List Nat) : ToString (FinProd l) :=
  match l with
  | []  => by simp[FinProd]; infer_instance
  | [n] => by simp[FinProd]; infer_instance
  | n :: m :: ns =>
    have e := instToStringFinProd (m :: ns)
    by simp[FinProd]; infer_instance

/-- Given `(i₁, ..., iₘ) : Fin n₁ × ... × Fin nₘ` return `[i₁.1,..., iₘ.1]` -/
def FinProd.toList {l} (is : FinProd l) : List Nat :=
  match l, is with
  | [], _ => []
  | [_], i => [i.1]
  | _ :: _ :: _, (i, is) => i :: is.toList

/-- Given `(i₁, ..., iₘ) : Fin n₁ × ... × Fin nₘ` return `[n₁-i₁.1-1,..., nₘ-iₘ.1-1]` -/
def FinProd.toListComplement {l} (is : FinProd l) : List Nat :=
  match l, is with
  | [], _ => []
  | [n], i => [n-i.1-1]
  | n :: _ :: _, (i, is) => (n-i.1-1) :: is.toListComplement


-- #eval show IO Unit from do
--   let l := [2,3,4]
--   let N := size (FinProd l)
--   for i in fullRange (Fin N) do
--     let x : FinProd l := IndexType.fromFin i
--     IO.println s!"{x}"

--   IO.println "hoho"

--   for i in fullRange (FinProd [2,3]) do
--     IO.println s!"{i}"

--   IO.println "hihi"


--- tests
example : FinProd [] = Unit := by rfl
example (n) : FinProd [n] = (Fin n) := by rfl
example (n m) : FinProd [n,m] = (Fin n × Fin m) := by rfl
example : FinProd [1,2,4] = (Fin 1 × Fin 2 × Fin 4) := by rfl
