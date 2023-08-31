import SciLean
import SciLean.Util.Profile
import SciLean.Tactic.LetNormalize
import SciLean.Util.RewriteBy

import SciLean.Core.Simp.Sum

open SciLean

variable 
  {K : Type} [RealScalar K]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {ι : Type} [EnumType ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]

set_default_scalar K 

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
  (conv => lhs; autodiff)

example
  : (∇ (x : Fin 10 → K), ∑ i, ‖x i‖₂²)
    =
    fun x i => 2 * (x i) :=
by
  (conv => lhs; autodiff)

example (A : Fin 5 → Fin 10 → K)
  : (∇ (x : Fin 10 → K), fun i => ∑ j, A i j * x j)
    =
    fun _ dy j => ∑ i, A i j * dy i := 
by 
  (conv => lhs; autodiff)

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

example
  : (∇ (x : Fin 10 → K), ∑ i, ‖x i‖₂²)
    =
    fun x i => 2 * (x i) :=
by
  (conv => lhs; autodiff)

example (A : Fin 5 → Fin 10 → K)
  : (∇ (x : Fin 10 → K), fun i => ∑ j, A i j * x j)
    =
    fun _ dy j => ∑ i, A i j * dy i := 
by 
  (conv => lhs; autodiff)


