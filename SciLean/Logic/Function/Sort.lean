module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Nat

public import SciLean.Util.SorryProof

-- `Array.qsort` does not export its body, `import all` is needed to reason about it
import all Init.Data.Array.QSort.Basic

@[expose] public section


namespace SciLean

open Classical in
/-- Returns permutation of indices `I` under which `x : I → X` is sorted.

--TODO: note implementations of this function
-/
noncomputable
def sortPermutation {I X} [PartialOrder I] [PartialOrder X] (x : I → X) : I ≃ I :=
  if h : ∃ p : I ≃ I, ∀ i j, i ≤ j → x (p i) ≤ x (p j) then
     choose h
  else
    Equiv.refl I


/-- Sorting an array does not change its size. -/
theorem _root_.Array.size_qsort {α} (xs : Array α) (f : α → α → Bool) (low high : Nat) :
    (Array.qsort xs f low high).size = xs.size := by
  unfold Array.qsort
  split <;> simp


/-- `qpartition.loop` only swaps elements, so it returns a permutation of its input. -/
private theorem _root_.Array.qpartition_loop_perm {α n} (lt : α → α → Bool) (lo hi : Nat) (hhi : hi < n)
    (pivot : α) (as : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi) :
    (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).2.toList.Perm as.toList := by
  induction as, i, k, ilo, ik, w using Array.qpartition.loop.induct lt lo hi hhi pivot with
  | case1 as i k _ _ _ h hlt ih =>
    rw [Array.qpartition.loop]; simp only [h, hlt, dite_true, ite_true]
    exact ih.trans (Vector.swap_perm _ _).toList
  | case2 as i k _ _ _ h hlt ih => rw [Array.qpartition.loop]; simpa [h, hlt] using ih
  | case3 as i k _ _ _ h => rw [Array.qpartition.loop]; simpa [h] using (Vector.swap_perm _ _).toList

/-- `qpartition` returns a permutation of its input. -/
private theorem _root_.Array.qpartition_perm {α n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (Array.qpartition as lt lo hi w hlo hhi).2.toList.Perm as.toList := by
  have hs : ∀ (c : Prop) [Decidable c] (v : Vector α n) i j (h₁ : i < n) (h₂ : j < n),
      (if c then v.swap i j h₁ h₂ else v).toList.Perm v.toList := by
    intro c _ v i j h₁ h₂; split
    · exact (Vector.swap_perm _ _).toList
    · exact .refl _
  exact (Array.qpartition_loop_perm ..).trans ((hs ..).trans ((hs ..).trans (hs ..)))

/-- `qsort.sort` returns a permutation of its input. -/
private theorem _root_.Array.qsort_sort_perm {α n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (Array.qsort.sort lt as lo hi w hlo hhi).toList.Perm as.toList := by
  induction as, lo, hi, w, hlo, hhi using Array.qsort.sort.induct lt with
  | case1 as lo hi w hlo hhi h mid hmid as' hq h2 =>
    rw [Array.qsort.sort]; simp only [h, dite_true, hq, h2]
    have := Array.qpartition_perm as lt lo hi w hlo hhi
    rw [hq] at this; exact this
  | case2 as lo hi w hlo hhi h mid hmid as' hq h2 ih1 _ ih3 =>
    rw [Array.qsort.sort]; simp only [h, dite_true, hq, h2]
    have := Array.qpartition_perm as lt lo hi w hlo hhi
    rw [hq] at this
    exact ih3.trans (ih1.trans this)
  | case3 as lo hi w hlo hhi h => rw [Array.qsort.sort]; simp [h]

/-- Sorting an array returns a permutation of it. -/
theorem _root_.Array.qsort_perm {α} (xs : Array α) (lt : α → α → Bool) (lo hi : Nat) :
    (xs.qsort lt lo hi).toList.Perm xs.toList := by
  unfold Array.qsort
  split
  · exact .refl _
  · exact Array.qsort_sort_perm ..

private theorem foldl_set_other {n} (g : Fin n → Fin n) (l : List (Fin n)) (v : Vector (Fin n) n)
    (p : Fin n) (hp : ∀ i ∈ l, g i ≠ p) :
    (l.foldl (fun js i => js.set (g i).1 i (g i).2) v)[p.1] = v[p.1] := by
  induction l generalizing v with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun i hi => hp i (by simp [hi]))]
    rw [Vector.getElem_set_ne]
    exact fun h => hp a (by simp) (Fin.ext h)

private theorem foldl_set_spec {n} (g : Fin n → Fin n) (hg : Function.Injective g)
    (l : List (Fin n)) (hl : l.Nodup) (v : Vector (Fin n) n) :
    ∀ i ∈ l, (l.foldl (fun js i => js.set (g i).1 i (g i).2) v)[(g i).1] = i := by
  induction l generalizing v with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    intro i hi
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hi with rfl | hi
    · rw [foldl_set_other g l _ _ (fun j hj h => hl.1 (by rwa [hg h] at hj))]
      simp
    · exact ih hl.2 _ i hi

/-- Returns permuation of indices under which the array is sorted. -/
def _root_.Array.qsortPermutation [LinearOrder X] (xs : Array X) : Fin xs.size ≃ Fin xs.size :=

  let n := xs.size
  let ps := (xs.mapFinIdx (fun i x h => ((⟨i,h⟩ : Fin n),x))).qsort (fun (_,x) (_,x') => x < x')
  let is : Array (Fin n) := ps.unzip.1
  -- sorting and unzipping preserve the size, so `is` has exactly `n` elements
  have his : is.size = n := by simp [is, ps, Array.size_qsort]; rfl
  -- `js` is kept as a `Vector` so that its size `n` is known and the index bounds below hold
  let js : Vector (Fin n) n := is.foldl (init := (⟨Array.finRange n, by simp⟩ : Vector (Fin n) n))
    (fun js i =>
      let i' := is[i.1]'(by omega)
      js.set i'.1 i i'.2)

  have hperm : is.toList.Perm (List.finRange n) := by
    have h : ps.toList.Perm _ := Array.qsort_perm _ _ _ _
    have h := h.map Prod.fst
    simp [is] at h ⊢
    refine h.trans (List.Perm.of_eq ?_)
    apply List.ext_getElem <;> simp [n]
  have hnodup : is.toList.Nodup := hperm.nodup_iff.2 (List.nodup_finRange n)
  have hinj : Function.Injective (fun i : Fin n => is[i.1]'(by omega)) := by
    intro a b hab
    exact Fin.ext (hnodup.eq_of_getElem_eq (by simp [his]) (by simp [his]) (by simpa using hab))
  have hjs : ∀ i : Fin n, js[(is[i.1]'(by omega)).1] = i := by
    intro i
    have := foldl_set_spec _ hinj is.toList hnodup ⟨Array.finRange n, by simp⟩ i
      (hperm.mem_iff.2 (List.mem_finRange i))
    simpa [js, ← Array.foldl_toList] using this
  {
    toFun := fun i => is[i.1]'(by omega)
    invFun := fun j => js[j.1]
    left_inv := hjs
    right_inv := by
      intro j
      obtain ⟨k, hk, hkj⟩ := List.getElem_of_mem (hperm.mem_iff.2 (List.mem_finRange j))
      have hk' : k < n := by simpa [his] using hk
      simp only [Array.getElem_toList] at hkj
      subst hkj
      simp only [hjs ⟨k, hk'⟩]
  }


/-- Returns permuation of indices under which the vector is sorted. -/
def _root_.Vector.qsortPermutation {n : ℕ} [LinearOrder X] (xs : Vector X n) :
    Fin n ≃ Fin n :=
  let P := xs.toArray.qsortPermutation
  cast (by simp[xs.2]) P
