import SciLean

open SciLean

variable
  {K : Type} [RealScalar K]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {W : Type} [SemiInnerProductSpace K W]
  {Y₁ : Type} [SemiInnerProductSpace K Y₁]
  {Y₂ : Type} [SemiInnerProductSpace K Y₂]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]
  {ι κ : Type} [Index ι] [Index κ]

set_default_scalar K



-- theorem GetElem.getElem.arg_xs.revDerivUpdate_pi_rule
--   (f : X → Cont) (dom)
--   (hf : HasAdjDiff K f)
--   : revDerivUpdate K (fun x idx => getElem (f x) idx dom)
--     =
--     fun x =>
--       let ydf := revDerivUpdate K f x
--       (fun idx => getElem ydf.1 idx dom,
--        fun delem (k : K) dx =>
--          let dcont := introElem delem
--          ydf.2 dcont k dx) :=
-- by
--   have ⟨_,_⟩ := hf
--   unfold revDerivUpdate; ftrans; ftrans; simp


example (x : W → ι → K) (hx : ∀ i, HasAdjDiff K (fun w => (x w i))) (hx : HasAdjDiff K x)
  : revDerivUpdate K (fun w i => x w i)
    =
    fun w => sorry :=
      -- let xdx := <∂ (w':=w), x w'
      -- (fun i => xdx.1[i], fun dy => let dy' := ⊞ i => dy i; xdx.2 dy') :=
by
  ftrans
  sorry
  -- conv =>
  --   lhs
  --   simp (config := {zeta := false}) only [revCDeriv.factor_through_getElem (K:=K) (fun _ y => y) (fun w => x w) (fun i => i) sorry sorry sorry sorry]
  --   autodiff

variable [PlainDataType K]

example (x : W → K ^ ι) (hx : ∀ i, HasAdjDiff K (fun w => (x w)[i])) (hx : HasAdjDiff K x)
  : revDerivUpdate K (fun (x : K ^ ι) i => x[i])
    =
    fun w => sorry :=
      -- let xdx := revDerivUpdate K (w':=w), x w'
      -- (fun i => xdx.1[i], fun dy => let dy' := ⊞ i => dy i; xdx.2 dy') :=
by
  ftrans
  let_normalize
  let_normalize
  let_normalize
  sorry_proof


example (x : W → K ^ ι) (hx : ∀ i, HasAdjDiff K (fun w => (x w)[i])) (hx : HasAdjDiff K x)
  : revDerivUpdate K (fun w i => (x w)[i])
    =
    fun w => sorry :=
      -- let xdx := revDerivUpdate K (w':=w), x w'
      -- (fun i => xdx.1[i], fun dy => let dy' := ⊞ i => dy i; xdx.2 dy') :=
by
  ftrans
  let_normalize
  let_normalize
  let_normalize
  sorry_proof



variable (A : W → DataArrayN K (ι×κ)) (hA : HasAdjDiff K A) (x y : W → K^κ) (hx : HasAdjDiff K x) (hy : HasAdjDiff K y) (h : κ → κ) (hh : Function.Bijective h)


example
  : revDerivUpdate K (fun w j i => (A w)[(i,j)] * (x w)[j])
    =
    fun w =>
      let AdA := revDerivUpdate K A w
      let xdx := revDerivUpdate K x w
      (fun j i => AdA.1[(i,j)] * xdx.1[j],
       fun dB k dw =>
         let dA := ⊞ ij : ι×κ => xdx.1[ij.2] * dB ij.2 ij.1
         let dx := ⊞ j : κ => ∑ i, AdA.1[(i,j)] * dB j i
         AdA.2 dA k (xdx.2 dx k dw))
    :=
by
  sorry
