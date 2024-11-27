import SciLean.Data.DataArray.DataArray

namespace SciLean.DataArrayN

variable {I : Type*} [IndexType I]
  {X : Type*} [PlainDataType X]


abbrev mapMono (x : DataArrayN X I) (f : X → X) :=
  ArrayType.mapMono f x


abbrev mapIdxMono (x : DataArrayN X I) (f : I → X → X) :=
  ArrayType.mapIdxMono f x


abbrev foldl (x : DataArrayN X I) (op : X → X → X) (init : X) :=
  IndexType.foldl (fun b i => op b x[i]) init


abbrev reduceD (x : DataArrayN X I) (f : X → X → X) (default : X):=
  IndexType.reduceD (fun i => x[i]) f default


abbrev reduce [Inhabited X] (x : DataArrayN X I) (f : X → X → X) :=
  IndexType.reduce (fun i => x[i]) f


abbrev max [Max X] [Inhabited X] (x : DataArrayN X I) : X :=
  IndexType.reduce (fun i : I => x[i]) (Max.max · ·)


abbrev min [Min X] [Inhabited X] (x : DataArrayN X I) : X :=
  IndexType.reduce (fun i : I => x[i]) (Min.min · ·)


macro "reshape_tactic" : tactic => `(tactic| first | decide | simp | (fail "failed to reshape"))

abbrev reshape1 (x : X^[I]) (n : ℕ)
    (h : Size.size I = n := by reshape_tactic) : X^[n] :=
  x.reshape (Fin n) (by simp[h])


abbrev reshape2 (x : X^[I]) (n₁ n₂ : ℕ)
    (h : Size.size I = n₁*n₂ := by reshape_tactic) : X^[n₁,n₂] :=
  x.reshape (Fin n₁ × Fin n₂) (by simp[h])


abbrev reshape3 (x : X^[I]) (n₁ n₂ n₃ : ℕ)
    (h : Size.size I = n₁*n₂*n₃ := by reshape_tactic) : X^[n₁,n₂,n₃] :=
  x.reshape (Fin n₁ × Fin n₂ × Fin n₃) (by simp[h]; ac_rfl)


abbrev reshape4 (x : X^[I]) (n₁ n₂ n₃ n₄ : ℕ)
    (h : Size.size I = n₁*n₂*n₃*n₄ := by reshape_tactic) : X^[n₁,n₂,n₃,n₄] :=
  x.reshape (Fin n₁ × Fin n₂ × Fin n₃ × Fin n₄) (by simp[h]; ac_rfl)


abbrev reshape5 (x : X^[I]) (n₁ n₂ n₃ n₄ n₅ : ℕ)
    (h : Size.size I = n₁*n₂*n₃*n₄*n₅ := by reshape_tactic) : X^[n₁,n₂,n₃,n₄,n₅] :=
  x.reshape (Fin n₁ × Fin n₂ × Fin n₃ × Fin n₄ × Fin n₅) (by simp[h]; ac_rfl)
