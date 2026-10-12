module

public import Mathlib.Topology.Order

public import SciLean.Util.SorryProof
public import SciLean.Data.IndexType.Init

@[expose] public section


namespace SciLean

/--
`Idx n` is a natural number `i` with the constraint that `0 ≤ i < n`.

Same as `Fin n` but uses `USize` to represent its value. In some applications, mainly when indexing
arrays, the use of arbitrary sized `Nat` is too expensive and using `Idx n` can be significantly
faster.

Warning: This type is sometimes used in inconsistent way! It is treated identically as `Fin n`
         thus for `n > USize.size` some theorems are no longer true.
         For example `Idx m × Ind n ≃ Idx (m*n)` is not true for any `m n : Nat`, but we will
         state such theorem anyway.

         In applications, this type is never use with `n > USize.size` but assuming `n < USize.size`
         would be too cumbersome. At some point we will attempt to recover formal consistency by
         adding `n < USize.size` assumption everywhere where necessary and in applications panicking
         if not satisfied. Note that not satisfying `n < USize.size` will mean running out of memory
         and at that point programs has very limited cabability of recovering anyway.

         Another way to deal with this problem is to make this type completely opaque, add an
         axiom that it is isomorphic to `Fin n` and panic at runtime on overflow. This would
         prevent us from stating inconsitent theorems that could be exploited to prove `False`.
-/
structure Idx (n : ℕ) where
  /-- Creates a `Idx n` from `i : USize` and a proof that `i.toNat < n`. -/
  mk ::
  /-- If `i : Idx n`, then `i.val : USize` is the described number. It can also be
  written as `i.1` or just `i` when the target type is known. -/
  val  : USize
  /-- If `i : Idx n`, then `i.2` is a proof that `i.1.toNat < n`. -/
  isLt : val.toNat < n


attribute [coe] Idx.val

/-- Reducing a `USize` modulo `n` always produces a value smaller than `n`.

Note that this holds even when `n` does not fit into `USize` - then `n.toUSize` is `n % USize.size`
and the result is bounded by `USize.size ≤ n`. -/
theorem usize_mod_toNat_lt (x : USize) {n : Nat} (hn : 0 < n) :
    (x % n.toUSize).toNat < n := by
  have hx : x.toNat < USize.size := x.toNat_lt_size
  rw [USize.toNat_mod, USize.toNat_ofNat']
  rcases Nat.eq_zero_or_pos (n % USize.size) with h | h
  · have hdvd : USize.size ∣ n := Nat.dvd_of_mod_eq_zero h
    simpa [h] using lt_of_lt_of_le hx (Nat.le_of_dvd hn hdvd)
  · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ h) (Nat.mod_le _ _)

/-- `toNat` of `x % n`, where `%` is the default `HMod USize Nat USize` instance, i.e.
`USize.modn`. -/
theorem usize_modn_toNat (x : USize) (n : Nat) : (x % n).toNat = x.toNat % n := by
  show (USize.ofNat (x.toNat % n)).toNat = _
  rw [USize.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.toNat_lt_size)

theorem usize_modn_toNat_lt (x : USize) {n : Nat} (hn : 0 < n) : (x % n).toNat < n := by
  rw [usize_modn_toNat]
  exact Nat.mod_lt _ hn

/-- Addition of `USize` can only wrap around, hence it never exceeds the addition of `Nat`s. -/
theorem usize_toNat_add_le (x y : USize) : (x + y).toNat ≤ x.toNat + y.toNat := by
  rw [USize.toNat_add]; exact Nat.mod_le _ _

/-- Converting `Nat` to `USize` can only decrease its value. -/
theorem usize_toNat_ofNat_le (n : Nat) : n.toUSize.toNat ≤ n := by
  rw [USize.toNat_ofNat']; exact Nat.mod_le _ _

/-- Bound on a `Nat` is preserved when converting it to `USize`. -/
theorem usize_toNat_ofNat_lt {i n : Nat} (h : i < n) : i.toUSize.toNat < n :=
  Nat.lt_of_le_of_lt (usize_toNat_ofNat_le i) h

/-- Conversion of `Nat` to `USize` is exact for numbers fitting into `USize`. -/
theorem usize_toNat_ofNat_eq {n : Nat} (h : n < USize.size) : n.toUSize.toNat = n := by
  rw [USize.toNat_ofNat']; exact Nat.mod_eq_of_lt h

/-- Addition of `USize` does not wrap around if the result fits into `USize`. -/
theorem usize_toNat_add_eq {x y : USize} (h : x.toNat + y.toNat < USize.size) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [USize.toNat_add]; exact Nat.mod_eq_of_lt h

/-- Multiplication of `USize` does not wrap around if the result fits into `USize`. -/
theorem usize_toNat_mul_eq {x y : USize} (h : x.toNat * y.toNat < USize.size) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [USize.toNat_mul]; exact Nat.mod_eq_of_lt h

theorem Idx.eq_of_val_eq {n} : ∀ {i j : Idx n}, Eq i.val j.val → Eq i j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem Idx.val_eq_of_eq {n} {i j : Idx n} (h : Eq i j) : Eq i.val j.val :=
  h ▸ rfl

instance (n : Nat) : DecidableEq (Idx n) :=
  fun i j =>
    if h : i.val = j.val then
      .isTrue (Idx.eq_of_val_eq h)
    else
      .isFalse (fun h' => h (Idx.val_eq_of_eq h'))
    -- probably too slow
    -- match decEq i.val j.val with
    -- | isTrue h  => isTrue (Idx.eq_of_val_eq h)
    -- | isFalse h => isFalse (fun h' => absurd (Idx.val_eq_of_eq h') h)

instance {n} : LT (Idx n) where
  lt a b := LT.lt a.val b.val

instance {n} : LE (Idx n) where
  le a b := LE.le a.val b.val

instance Idx.decLt {n} (a b : Idx n) : Decidable (LT.lt a b) := -- Nat.decLt .. -- too slow
  if h : a.val < b.val then
    .isTrue h
  else
    .isFalse h
instance Idx.decLe {n} (a b : Idx n) : Decidable (LE.le a b) :=  -- Nat.decLe .. -- too slow
  if h : a.val ≤ b.val then
    .isTrue h
  else
    .isFalse h


/--
`Idx n` is equivalent to `Fin n`

This is blatanly false but we treat `Idx n` as `Fin n`, see documentation of `Idx n`.
-/
def Idx.finEquiv (n : Nat) : Idx n ≃ Fin n where
  toFun x := ⟨x.1.toNat, x.2⟩
  invFun x := ⟨x.1.toUSize, usize_toNat_ofNat_lt x.2⟩
  left_inv := fun x => Idx.eq_of_val_eq (by simp)
  -- this direction is false for `n > USize.size`, see the documentation of `Idx n`
  right_inv := sorry_proof

-- The rest of the file is direct copy of `Init.Data.Fin.Basic`
namespace Idx

instance coeToUSize : CoeOut (Idx n) USize :=
  ⟨fun v => v.val⟩

instance coeToNat : CoeOut (Idx n) Nat :=
  ⟨fun v => v.val.toNat⟩

def toFin (i : Idx n) : Fin n := ⟨i.1.toNat, i.2⟩
def _root_.Fin.toIdx (i : Fin n) : Idx n := ⟨i.1.toUSize, usize_toNat_ofNat_lt i.2⟩

/--
From the empty type `Idx 0`, any desired result `α` can be derived. This is similar to `Empty.elim`.
-/
def elim0.{u} {α : Sort u} : Idx 0 → α
  | ⟨_, h⟩ => absurd h (by omega)

/--
Returns the successor of the argument.

The bound in the result type is increased:
```
(2 : Idx 3).succ = (3 : Idx 4)
```
This differs from addition, which wraps around:
```
(2 : Idx 3) + 1 = (0 : Idx 3)
```
-/
def succ : Idx n → Idx (n + 1)
  | ⟨i, h⟩ => ⟨i+1, by
    have h1 := usize_toNat_add_le i 1
    have h2 : (1 : USize).toNat = 1 := USize.toNat_one
    omega⟩

variable {n : Nat}


/--
Returns `a` modulo `n` as a `Idx n`.

The assumption `NeZero n` ensures that `Idx n` is nonempty.
-/
protected def ofNat (n : Nat) [NeZero n] (a : Nat) : Idx n :=
  ⟨a.toUSize % n, usize_modn_toNat_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

/--
Returns `a` modulo `n` as a `Idx n`.

The assumption `NeZero n` ensures that `Idx n` is nonempty.
-/
protected def ofUSize (n : Nat) [NeZero n] (a : USize) : Idx n :=
  ⟨a % n, usize_modn_toNat_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

theorem mlt {b : Nat} : {a : Nat} → a < n → b % n < n
  | 0,   h => Nat.mod_lt _ h
  | _+1, h =>
    have : n > 0 := Nat.lt_trans (Nat.zero_lt_succ _) h;
    Nat.mod_lt _ this

/--
Override default instance of `HMod USize Nat USize` because it is implementex as `Fin.modn x.val n`
which does the operations with `Nat` rather than with `USize` which is bad.
 -/
instance (priority:=high) instHModUSizeNatFast : HMod USize Nat USize := ⟨fun x y => x % y.toUSize⟩

/-- Addition modulo `n` -/
@[inline] protected def add : Idx n → Idx n → Idx n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + b) % n, usize_mod_toNat_lt _ (Nat.zero_lt_of_lt h)⟩

/-- Multiplication modulo `n` -/
@[inline] protected def mul : Idx n → Idx n → Idx n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a * b) % n.toUSize, usize_mod_toNat_lt _ (Nat.zero_lt_of_lt h)⟩

/-- Subtraction modulo `n` -/
@[inline] protected def sub : Idx n → Idx n → Idx n
  /-
  The deidxition of `Idx.sub` has been updated to improve performance.
  The right-hand-side of the following `match` was originally
  ```
  ⟨(a + (n - b)) % n, mlt h⟩
  ```
  This caused significant performance issues when testing deidxitional equality,
  such as `x =?= x - 1` where `x : Idx n` and `n` is a big number,
  as Lean spent a long time reducing
  ```
  ((n - 1) + x.val) % n
  ```
  For example, this was an issue for `Idx 2^64` (i.e., `UInt64`).
  This change improves performance by leveraging the fact that `Nat.add` is deidxed
  using recursion on the second argument.
  See issue #4413.
  -/
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨((n.toUSize - b) + a) % n.toUSize, usize_mod_toNat_lt _ (Nat.zero_lt_of_lt h)⟩

/-!
Remark: land/lor can be deidxed without using (% n), but
we are trying to minimize the number of Nat theorems
needed to bootstrap Lean.
-/

@[inline] protected def mod : Idx n → Idx n → Idx n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨a % b,  Nat.lt_of_le_of_lt (Nat.mod_le _ _) h⟩

@[inline] protected def div : Idx n → Idx n → Idx n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨a / b, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h⟩

@[inline] def modn : Idx n → Nat → Idx n
  | ⟨a, h⟩, m => ⟨a % m, Nat.lt_of_le_of_lt (Nat.mod_le _ _) h⟩

@[inline] def land : Idx n → Idx n → Idx n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(USize.land a b) % n, usize_mod_toNat_lt _ (Nat.zero_lt_of_lt h)⟩

@[inline] def lor : Idx n → Idx n → Idx n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(USize.lor a b) % n, usize_mod_toNat_lt _ (Nat.zero_lt_of_lt h)⟩

@[inline] def xor : Idx n → Idx n → Idx n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(USize.xor a b) % n, usize_mod_toNat_lt _ (Nat.zero_lt_of_lt h)⟩

@[inline] def shiftLeft : Idx n → Idx n → Idx n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a <<< b) % n, usize_mod_toNat_lt _ (Nat.zero_lt_of_lt h)⟩

@[inline] def shiftRight : Idx n → Idx n → Idx n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a >>> b) % n, usize_mod_toNat_lt _ (Nat.zero_lt_of_lt h)⟩

instance : Add (Idx n) where
  add := Idx.add

instance : Sub (Idx n) where
  sub := Idx.sub

instance : Mul (Idx n) where
  mul := Idx.mul

instance : Mod (Idx n) where
  mod := Idx.mod

instance : Div (Idx n) where
  div := Idx.div

instance : AndOp (Idx n) where
  and := Idx.land
instance : OrOp (Idx n) where
  or := Idx.lor
instance : XorOp (Idx n) where
  xor := Idx.xor
instance : ShiftLeft (Idx n) where
  shiftLeft := Idx.shiftLeft
instance : ShiftRight (Idx n) where
  shiftRight := Idx.shiftRight

instance instOfNat {n : Nat} [NeZero n] {i : Nat} : OfNat (Idx n) i where
  ofNat := Idx.ofNat n i

instance instInhabited {n : Nat} [NeZero n] : Inhabited (Idx n) where
  default := 0

@[simp] theorem zero_eta : (⟨0, Nat.zero_lt_succ _⟩ : Idx (n + 1)) = 0 := rfl

/-- Every number smaller then `2^32` fits into `USize`. -/
theorem _root_.SciLean.usize_size_gt (k : ℕ) (h : k < 4294967296) : k < USize.size :=
  Nat.lt_of_lt_of_le h USize.le_size

/-- Value of the numeral `k : Idx n` is `k` provided that `k < n` and `n` fits into `USize`. -/
theorem toNat_ofNat {n : ℕ} [NeZero n] (k : ℕ) (hk : k < n) (hn : n < USize.size) :
    ((OfNat.ofNat k : Idx n) : USize).toNat = k := by
  show (Idx.ofNat n k).val.toNat = k
  simp only [Idx.ofNat]
  rw [usize_modn_toNat, usize_toNat_ofNat_eq (Nat.lt_trans hk hn)]
  exact Nat.mod_eq_of_lt hk

theorem eq_of_toNat {n : ℕ} [NeZero n] {i : Idx n} (k : ℕ) (hk : k < n) (hn : n < USize.size)
    (h : i.1.toNat = k) : i = OfNat.ofNat k :=
  Idx.eq_of_val_eq (USize.toNat_inj.mp (by rw [h, Idx.toNat_ofNat k hk hn]))

theorem ofNat_ne_ofNat {n : ℕ} [NeZero n] (k l : ℕ) (hk : k < n := by omega)
    (hl : l < n := by omega) (hn : n < 4294967296 := by omega) (hkl : k ≠ l := by omega) :
    (OfNat.ofNat k : Idx n) ≠ OfNat.ofNat l := by
  intro h
  have h' := congrArg (fun i : Idx n => i.1.toNat) h
  rw [Idx.toNat_ofNat k hk (SciLean.usize_size_gt n hn),
      Idx.toNat_ofNat l hl (SciLean.usize_size_gt n hn)] at h'
  exact hkl h'

theorem ne_of_val_ne {i j : Idx n} (h : val i ≠ val j) : i ≠ j :=
  fun h' => absurd (val_eq_of_eq h') h

theorem val_ne_of_ne {i j : Idx n} (h : i ≠ j) : val i ≠ val j :=
  fun h' => absurd (eq_of_val_eq h') h

-- theorem modn_lt : ∀ {m : USize} (i : Idx n), m > 0 → (modn i m).val < m
--   | _, ⟨_, _⟩, hp =>  by simp [modn]; apply Nat.mod_lt; assumption

-- theorem val_lt_of_le (i : Idx b) (h : b ≤ n) : i.val < n :=
--   Nat.lt_of_lt_of_le i.isLt h

/-- If you actually have an element of `Idx n`, then the `n` is always positive -/
protected theorem pos (i : Idx n) : 0 < n :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) i.2

/-- The greatest value of `Idx (n+1)`. -/
@[inline] def last (n : USize) : Idx (n.toNat + 1) := ⟨n, Nat.lt_succ_self _⟩

/-- `castLT i h` embeds `i` into a `Idx` where `h` proves it belongs into.  -/
@[inline] def castLT (i : Idx m) (h : i.1.toNat < n) : Idx n := ⟨i.1, h⟩

/-- `castLE h i` embeds `i` into a larger `Idx` type.  -/
@[inline] def castLE (h : n ≤ m) (i : Idx n) : Idx m := ⟨i, Nat.lt_of_lt_of_le i.2 h⟩

/-- `cast eq i` embeds `i` into an equal `Idx` type. -/
@[inline] protected def cast (eq : n = m) (i : Idx n) : Idx m := ⟨i, eq ▸ i.2⟩

/-- `castAdd m i` embeds `i : Idx n` in `Idx (n+m)`. See also `Idx.natAdd` and `Idx.addNat`. -/
@[inline] def castAdd (m) : Idx n → Idx (n + m) :=
  castLE <| Nat.le_add_right n m

/-- `castSucc i` embeds `i : Idx n` in `Idx (n+1)`. -/
@[inline] def castSucc : Idx n → Idx (n + 1) := castAdd 1

/-- `addNat m i` adds `m` to `i`, generalizes `Idx.succ`. -/
def addNat (i : Idx n) (m) : Idx (n + m) := ⟨i + m.toUSize, by
  have h1 := usize_toNat_add_le i.1 m.toUSize
  have h2 := usize_toNat_ofNat_le m
  have h3 := i.2
  omega⟩

/-- `natAdd n i` adds `n` to `i` "on the left". -/
def natAdd (n) (i : Idx m) : Idx (n + m) := ⟨n.toUSize + i, by
  have h1 := usize_toNat_add_le n.toUSize i.1
  have h2 := usize_toNat_ofNat_le n
  have h3 := i.2
  omega⟩

/-- Maps `0` to `n-1`, `1` to `n-2`, ..., `n-1` to `0`. -/
@[inline] def rev (i : Idx n) : Idx n := ⟨n.toUSize - (i + 1), by
  rcases Nat.lt_or_ge n USize.size with hn | hn
  · have hi := i.2
    have hnn : n.toUSize.toNat = n := by rw [USize.toNat_ofNat']; exact Nat.mod_eq_of_lt hn
    have h1 : (i.1 + 1).toNat = i.1.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]
      exact Nat.mod_eq_of_lt (by simp only [USize.size] at hn ⊢; omega)
    have hle : (i.1 + 1) ≤ n.toUSize := by
      rw [USize.le_iff_toNat_le, h1, hnn]; omega
    rw [USize.toNat_sub_of_le _ _ hle, hnn, h1]
    omega
  · exact Nat.lt_of_lt_of_le (USize.toNat_lt_size _) hn⟩

/-- `subNat i h` subtracts `m` from `i`, generalizes `Idx.pred`. -/
@[inline] def subNat (m) (i : Idx (n + m)) (h : m ≤ i.1.toNat) : Idx n :=
  ⟨i - m.toUSize, by
    have hi := i.2
    have hm : m < USize.size := Nat.lt_of_le_of_lt h (USize.toNat_lt_size _)
    have hmm : m.toUSize.toNat = m := by rw [USize.toNat_ofNat']; exact Nat.mod_eq_of_lt hm
    have hle : m.toUSize ≤ i.1 := by rw [USize.le_iff_toNat_le, hmm]; exact h
    rw [USize.toNat_sub_of_le _ _ hle, hmm]
    omega⟩

/-- Predecessor of a nonzero element of `Idx (n+1)`. -/
@[inline] def pred {n : Nat} (i : Idx (n + 1)) (h : i ≠ 0) : Idx n :=
  subNat 1 i (by
    apply Nat.pos_of_ne_zero
    refine mt (fun hi => ?_) h
    apply Idx.eq_of_val_eq
    show i.1 = (Idx.ofNat (n+1) 0).1
    simp [Idx.ofNat]
    apply USize.toNat_inj.mp
    simp [usize_modn_toNat, hi])

theorem val_inj {a b : Idx n} : a.1 = b.1 ↔ a = b := ⟨Idx.eq_of_val_eq, Idx.val_eq_of_eq⟩

theorem val_congr {n : Nat} {a b : Idx n} (h : a = b) : (a : USize) = (b : USize) :=
  Idx.val_inj.mpr h

theorem val_le_of_le {n : Nat} {a b : Idx n} (h : a ≤ b) : (a : Nat) ≤ (b : Nat) := h

theorem val_le_of_ge {n : Nat} {a b : Idx n} (h : a ≥ b) : (b : Nat) ≤ (a : Nat) := h

theorem val_add_one_le_of_lt {n : Nat} {a b : Idx n} (h : a < b) : (a : Nat) + 1 ≤ (b : Nat) := h

theorem val_add_one_le_of_gt {n : Nat} {a b : Idx n} (h : a > b) : (b : Nat) + 1 ≤ (a : Nat) := h

theorem exists_iff {p : Idx n → Prop} : (Exists fun i => p i) ↔ Exists fun i => Exists fun h => p ⟨i, h⟩ :=
  ⟨fun ⟨⟨i, hi⟩, hpi⟩ => ⟨i, hi, hpi⟩, fun ⟨i, hi, hpi⟩ => ⟨⟨i, hi⟩, hpi⟩⟩


----------------------------------------------------------------------------------------------------

private theorem usize_pred_toNat (x : USize) (h : 0 < x.toNat) : (x - 1).toNat = x.toNat - 1 := by
  have hx : x.toNat < 2^System.Platform.numBits := by
    have := USize.toNat_lt_size x; simpa [USize.size] using this
  have hpos : 0 < 2^System.Platform.numBits := Nat.two_pow_pos _
  have h1 : (1:USize).toNat = 1 := by simp
  rw [USize.toNat_sub, h1]
  have he : 2^System.Platform.numBits - 1 + x.toNat
            = 2^System.Platform.numBits + (x.toNat - 1) := by omega
  rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- The largest value of `USize` that fits into `Idx n`, i.e. `n-1`, is smaller than `n`. -/
theorem last_toNat_lt {n : Nat} (hn : n ≠ 0) : (n.toUSize - 1).toNat < n := by
  have h0 : 0 < n := Nat.pos_of_ne_zero hn
  have hlt : (n.toUSize - 1).toNat < USize.size := USize.toNat_lt_size _
  rcases Nat.lt_or_ge n USize.size with h | h
  · have hm : n.toUSize.toNat = n := by rw [USize.toNat_ofNat']; exact Nat.mod_eq_of_lt h
    have hpos : 0 < n.toUSize.toNat := by rw [hm]; exact h0
    rw [usize_pred_toNat _ hpos, hm]
    omega
  · omega

instance : ToString (Idx n) := ⟨fun i => toString i.1⟩

instance : Fintype (Idx n) := Fintype.ofEquiv _ (Idx.finEquiv n).symm

instance : Size (Idx n) where
  size := n

instance : Size' (Idx n) n where

instance : FirstLast (Idx n) (Idx n) where
  firstLast? :=
    if h : n ≠ 0 then
      some (⟨0, Nat.pos_of_ne_zero h⟩, ⟨n.toUSize-1, last_toNat_lt h⟩)
    else
      none

-- instance : IndexType (Idx n) where
--   toFin x := x.toFin
--   fromFin x := x.toIdx
--   rangeSize := fun r =>
--     match r with
--     | .empty => 0
--     | .full => n
--     | .interval a b => if a.1 ≤ b.1 then ((b.1 - a.1) + 1).toNat else ((a.1 - b.1) + 1).toNat
--   next? s :=
--     match s with
--     | .start r =>
--       match r with
--       | .empty => none
--       | .full =>
--         if h : n ≠ 0 then
--           let x : Idx n := ⟨0, by sorry_proof⟩
--           .some (x, .val x r)
--         else
--           .none
--       | .interval a _ => .some (a, .val a r)

--     | .val val r =>
--       match r with
--       | .empty => .none
--       | .full =>
--         if h : val.1 + 1 < n.toUSize then
--           let x := ⟨val.1+1, sorry_proof⟩
--           .some (x, .val x r)
--         else
--           .none
--       | .interval a b =>
--         if a.1 ≤ b.1 then
--           if h : val.1 + 1 ≤ b.1 then
--             let x := ⟨val.1+1, sorry_proof⟩
--             .some (x, .val x r)
--           else
--             .none
--         else
--           if h : b.1 + 1 ≤ val.1 then
--             let x := ⟨val.1-1, sorry_proof⟩
--             .some (x, .val x r)
--           else
--             .none
--   left_inv := sorry_proof
--   right_inv := sorry_proof
--   first_last := sorry_proof

-- maybe move these such that we do not have to import `Mathlib.Topology.Order`
instance {n} : TopologicalSpace (Idx n) := ⊥
instance {n} : DiscreteTopology (Idx n) := ⟨rfl⟩

end Idx
