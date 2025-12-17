import SciLean

open SciLean

variable
  {K : Type} [RealScalar K]
  {ι : Type} [IndexType ι nι] [DecidableEq ι]

set_default_scalar K

#exit

example
  : (∇ (x : Fin 10 → K), fun i => x i)
    =
    fun x dx => dx :=
by
  (conv => lhs; autodiff)

example
  : (∇ (x : Fin 10 → K), ∑ i, x i)
    =
    fun x i => 1 :=
by
  unfold fgradient
  (conv => lhs; autodiff)

example
  : (∇ (x : Fin 10 → K), ∑ i, ‖x i‖₂²)
    =
    fun x i => 2 * (x i) :=
by
  (conv => lhs; unfold scalarGradient; autodiff; autodiff)

example (A : Fin 5 → Fin 10 → K)
  : (∇ (x : Fin 10 → K), fun i => ∑ j, A i j * x j)
    =
    fun _ dy j => ∑ i, A i j * dy i :=
by
  (conv => lhs; simp[SciLean.gradient]; autodiff)

variable [PlainDataType K]

example
  : (∇ (x : K ^ Idx 10), fun i => x[i])
    =
    fun _ x => ⊞ i => x i :=
by
  (conv => lhs; autodiff)

example
  : (∇ (x : K ^ Idx 10), ⊞ i => x[i])
    =
    fun _ x => x :=
by
  (conv => lhs; autodiff)

example
  : (∇ (x : Fin 10 → K), ∑ i, x i)
    =
    fun x i => 1 :=
by
  (conv => lhs; autodiff)

-- example
--   : (∇ (x : K ^ Idx 10), ∑ i, ‖x[i+1] - x[i]‖₂²)
--     =
--     fun x => ⊞ _ => (1:K) :=
-- by
--   (conv => lhs; unfold scalarGradient; autodiff)

example
  : (∇ (x : K ^ Idx 10), ∑ i, x[i])
    =
    fun x => ⊞ _ => (1:K) :=
by
  (conv => lhs; autodiff)


example
  : (∇ (x : Fin 10 → K), ∑ i, ‖x i‖₂²)
    =
    fun x i => 2 * (x i) :=
by
  (conv => lhs; autodiff)

example (A : Idx 5 → Idx 10 → K)
  : (∇ (x : K ^ Idx 10), fun i => ∑ j, A i j * x[j])
    =
    fun _ dy => ⊞ j => ∑ i, A i j * dy i :=
by
  (conv => lhs; autodiff)

example
  : (∇ (x : Fin 10 → K), fun i => x i)
    =
    fun _ dx => dx :=
by
  (conv => lhs; autodiff)

example
  : (∇ (x : Fin 5 → Fin 10 → K), fun i j => x i j)
    =
    fun _ dx => dx :=
by
  (conv => lhs; autodiff)

example
  : (∇ (x : Fin 5 → Fin 10 → Fin 15→ K), fun i j k => x i j k)
    =
    fun _ dx => dx :=
by
  (conv => lhs; autodiff)

example
  : (∇ (x : Fin 5 → Fin 10 → Fin 15→ K), fun k i j => x i j k)
    =
    fun _ dx i j k => dx k i j :=
by
  (conv => lhs; autodiff)

example
  : (∇ (x : Fin 10 → K), fun ij : Fin 5 × Fin 10 => x ij.2)
    =
    fun _ dx i => ∑ j, dx (j,i) :=
by
  (conv => lhs; autodiff)

example
  : (∇ (x : Fin 5 → K), fun ij : Fin 5 × Fin 10 => x ij.1)
    =
    fun _ dx i => ∑ j, dx (i,j) :=
by
  (conv => lhs; autodiff)

-- TODO remove `hf'` assumption, is should be automatically deduced from `hf` once #23 is resolved
example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, HasAdjDiff K (f · i j k))
  (hf' : HasAdjDiff K f)
  : (∇ (x : X), fun k i j => f x i j k)
    =
    fun x dy =>
      let ydf := <∂ f x
      ydf.2 fun i j k => dy k i j :=
by
  (conv => lhs; autodiff)


example
  : (∇ (x : K ^ Idx 10), fun (ij : Idx 5 × Idx 10) => x[ij.snd])
    =
    fun _ dx => ⊞ j => ∑ i, dx (i,j) :=
by
  (conv => lhs; autodiff)


example
  : (∇ (x : K ^ Idx 10), fun i => x[i])
    =
    fun _ dx => ⊞ i => dx i :=
by
  (conv => lhs; autodiff)


example
  : (∇ (x : K ^ (Idx 10 × Idx 5)), fun i j => x[(i,j)])
    =
    fun _ dx => ⊞ ij => dx ij.1 ij.2 :=
by
  (conv => lhs; autodiff)


example
  : (∇ (x : K ^ (Idx 5 × Idx 10 × Idx 15)), fun i j k => x[(k,i,j)])
    =
    fun _ dx => ⊞ kij => dx kij.2.1 kij.2.2 kij.1 :=
by
  (conv => lhs; autodiff)


example
  : (∇ (x : Fin 5 → Fin 10 → Fin 15→ K), fun k i j => x i j k)
    =
    fun _ dx i j k => dx k i j :=
by
  (conv => lhs; autodiff)


example
  : (∇ (x : Fin 10 → K), fun i j => x i * x j)
    =
    fun x dx i => ∑ j, x j * dx i j + ∑ j, x j * dx j i:=
by
  (conv => lhs; autodiff)


example
  : (∇ (x : Fin 10 → K), fun (i : Fin 10) (j : Fin 5) => x (i+j))
    =
    fun x dy i => ∑ (j : Fin 5), dy (i - j) j :=
by
  (conv => lhs; autodiff; autodiff)


example  (w : Idx' (-5) 5 → K)
  : (∇ (x : Idx 10 → K), fun (i : Idx 10) (j : Idx' (-5) 5) => w j * x (j.1 +ᵥ i))
    =
    fun _x dy i => ∑ (j : Idx' (-5) 5), w j * dy (-j.1 +ᵥ i) j :=
by
  conv => lhs; autodiff


example  (w : Idx' (-5) 5 → K)
  : (∇ (x : Idx 10 → K), fun (i : Idx 10) => ∑ j, w j * x (j.1 +ᵥ i))
    =
    fun _x dy i => ∑ (j : Idx' (-5) 5), w j * dy (-j.1 +ᵥ i) :=
by
  conv => lhs; autodiff


example  (w : K ^ Idx' (-5) 5)
  : (∇ (x : K ^ Idx 10), ⊞ (i : Idx 10) => ∑ j, w[j] * x[j.1 +ᵥ i])
    =
    fun _x dy => ⊞ i => ∑ (j : Idx' (-5) 5), w[j] * dy[-j.1 +ᵥ i] :=
by
  conv => lhs; autodiff


-- example  (w : K ^ (Idx' (-5) 5 × Idx' (-5) 5))
--   : (∇ (x : K ^ (Idx 10 × Idx 10)), ⊞ (i : Idx 10 × Idx 10) => ∑ j, w[j] * x[(j.1.1 +ᵥ i.1, j.2.1 +ᵥ i.2)])
--     =
--     fun _x dy =>
--       ⊞ i => ∑ j, w[j] * dy[(-j.fst.1 +ᵥ i.fst, -j.snd.1 +ᵥ i.snd)] :=
--       -- ⊞ i => ∑ (j : (Idx' (-5) 5 × Idx' (-5) 5)), w[(j.2,j.1)] * dy[(-j.2.1 +ᵥ i.fst, -j.1.1 +ᵥ i.snd)] :=
-- by
--   conv => lhs; unfold SciLean.gradient; autodiff
--   -- sorry_proof
