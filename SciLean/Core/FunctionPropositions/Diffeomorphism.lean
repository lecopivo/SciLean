import SciLean.Core.FunctionPropositions.Bijective
import SciLean.Core.FunctionPropositions.CDifferentiable

import SciLean.Core.FunctionTransformations.CDeriv

set_option linter.unusedVariables false
open SciLean LeanColls

variable
  (K : Type _) [RCLike K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {W : Type _} [Vec K W]
  {ι : Type _} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]

namespace SciLean

@[fun_prop]
structure Diffeomorphism (f : X → Y) : Prop where
  bijective : Function.Bijective f
  differentiable : CDifferentiable K f
  locally_diffeo : ∀ x, Function.Bijective (cderiv K f x)

-- This is a bad theorems as you can't infer `K` from the conclusion
-- @[fun_prop]
theorem diffeomorphism_to_bijective (f : X → Y) (hf : Diffeomorphism K f) :
    Function.Bijective f := hf.1

@[fun_prop]
theorem diffeomorphism_to_differentiables (f : X → Y) (hf : Diffeomorphism K f) :
    CDifferentiable K f := hf.2

@[fun_prop]
theorem cderiv.arg_dx.Bijective_rule (f : X → Y) (x : X) (hf : Diffeomorphism K f) :
    Function.Bijective (fun dx => cderiv K f x dx) := hf.3 x

namespace Diffeomorphism

@[fun_prop]
theorem id_rule
  : Diffeomorphism K (fun x : X => x)
  := by sorry_proof

@[fun_prop]
theorem comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : Diffeomorphism K f) (hg : Diffeomorphism K g)
  : Diffeomorphism K (fun x => f (g x))
  := by sorry_proof

end SciLean.Diffeomorphism

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem id.arg_a.Diffeomorphism_rule
  : Diffeomorphism K (fun x : X => id x) :=
by
  simp[id]; fun_prop


-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Function.comp.arg_a0.Diffeomorphism_rule
  (f : Y → Z) (g : X → Y)
  (hf : Diffeomorphism K f) (hg : Diffeomorphism K g)
  : Diffeomorphism K (fun x => (f ∘ g) x)
  := by simp[Function.comp]; fun_prop


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Neg.neg.arg_a0.Diffeomorphism_rule
  (f : X → Y) (hf : Diffeomorphism K f)
  : Diffeomorphism K (fun x => - f x) :=
by
  have ⟨_,_,_⟩ := hf
  constructor
  · fun_prop
  · fun_prop
  · fun_trans; fun_prop


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HAdd.hAdd.arg_a0.Diffeomorphism_rule
  (f : X → Y) (y : Y) (hf : Diffeomorphism K f)
  : Diffeomorphism K (fun x => f x + y) :=
by
  have ⟨_,_,_⟩ := hf
  constructor
  · fun_prop
  · fun_prop
  · fun_trans; fun_prop

@[fun_prop]
theorem HAdd.hAdd.arg_a1.Diffeomorphism_rule
  (y : Y) (f : X → Y) (hf : Diffeomorphism K f)
  : Diffeomorphism K (fun x => y + f x) :=
by
  have ⟨_,_,_⟩ := hf
  constructor
  · fun_prop
  · fun_prop
  · fun_trans; fun_prop



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSub.hSub.arg_a0.Diffeomorphism_rule
  (f : X → Y) (y : Y) (hf : Diffeomorphism K f)
  : Diffeomorphism K (fun x => f x - y) :=
by
  have ⟨_,_,_⟩ := hf
  constructor
  · fun_prop
  · fun_prop
  · fun_trans; fun_prop

@[fun_prop]
theorem HSub.hSub.arg_a1.Diffeomorphism_rule
  (y : Y) (f : X → Y) (hf : Diffeomorphism K f)
  : Diffeomorphism K (fun x => y - f x) :=
by
  have ⟨_,_,_⟩ := hf
  constructor
  · fun_prop
  · fun_prop
  · fun_trans; fun_prop


-- HMul.hMul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def HMul.hMul.arg_a0.Diffeomorphism_rule
  (f : X → K) (y : K) (hf : Diffeomorphism K f) (hy : y≠0)
  : Diffeomorphism K (fun x => f x * y) :=
by
  have ⟨_,_,_⟩ := hf
  constructor
  · fun_prop (disch:=assumption)
  · fun_prop
  · fun_trans; fun_prop (disch:=assumption)

@[fun_prop]
def HMul.hMul.arg_a1.Diffeomorphism_rule
  (y : K) (f : X → K) (hy : y≠0) (hf : Diffeomorphism K f)
  : Diffeomorphism K (fun x => y * f x) :=
by
  have ⟨_,_,_⟩ := hf
  constructor
  · fun_prop (disch:=assumption)
  · fun_prop
  · fun_trans; fun_prop (disch:=assumption)


-- SMul.sMul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def HSMul.hSMul.arg_a1.Diffeomorphism_rule
  (r : K) (f : X → Y) (hr : r≠0) (hf : Diffeomorphism K f)
  : Diffeomorphism K (fun x => r • f x) :=
by
  have ⟨_,_,_⟩ := hf
  constructor
  · fun_prop (disch:=assumption)
  · fun_prop
  · fun_trans; fun_prop (disch:=assumption)


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def HDiv.hDiv.arg_a0.Diffeomorphism_rule
  (f : X → K) (r : K)
  (hf : Diffeomorphism K f) (hr : r ≠ 0)
  : Diffeomorphism K (fun x => f x / r) :=
by
  have ⟨_,_,_⟩ := hf
  constructor
  · fun_prop (disch:=assumption)
  · fun_prop (disch:=assumption)
  · fun_trans (disch:=assumption); sorry_proof --fun_prop (disch:=assumption)


-- Nat.iterate -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
def Nat.iterate.arg_a1.Diffeomorphism_rule
  (n : Nat) (f : X → X) (hf : Diffeomorphism K f)
  : Diffeomorphism K (fun x => f^[n] x) := by
  induction n
  case zero => simp; fun_prop
  case succ n hn => simp; fun_prop

-- Function.invFun -------------------------------------------------------------
--------------------------------------------------------------------------------

open Function

@[fun_prop]
theorem Function.invFun.arg_fa1.CDifferentiable_rule
  (f : X → Y → Z) (g : W → X) (h : W → Z)
  (hf : ∀ x, Diffeomorphism K (f x))
  (hf' : CDifferentiable K (fun xy : X×Y => f xy.1 xy.2))
  (hg : CDifferentiable K g) (hh : CDifferentiable K h)
  : CDifferentiable K (fun w : W => invFun (f (g w)) (h w)) := sorry_proof


@[fun_trans]
theorem Function.invFun.arg_a1.cderiv_rule
  (f : Y → Z) (g : X → Z)
  (hf : Diffeomorphism K f) (hg : CDifferentiable K g)
  : cderiv K (fun x => invFun f (g x))
    =
    fun x dx =>
      let z := g x
      let dz := cderiv K g x dx
      let y := invFun f z
      let dy := invFun (cderiv K f y) dz
      dy :=
by
  funext x dx
  have H : (cderiv K (f ∘ invFun f) (g x))
           =
           id := by simp[show (f ∘ Function.invFun f) = id from sorry_proof]; unfold id; fun_trans
  have q : cderiv K f (invFun f (g x)) (cderiv K (fun x => invFun f (g x)) x dx) = cderiv K g x dx := sorry_proof
  sorry_proof

-- Which rule is preferable? This one or the second one?
-- Probably the second as it has Function.inv fully applied
@[fun_trans]
theorem Function.invFun.arg_f_a1.cderiv_rule
  (f : X → Y → Z)
  (hf : ∀ x, Diffeomorphism K (f x))
  (hf' : CDifferentiable K (fun xy : X×Y => f xy.1 xy.2))
  : cderiv K (fun x z => invFun (f x) z)
    =
    fun x dx z =>
      let y := invFun (f x) z
      let dfdx_y := (cderiv K f x dx) y
      let df'dy := cderiv K (invFun (f x)) (f x y) (dfdx_y)
      (-df'dy)
  :=
by
  funext x dx
  have H : ((cderiv K (fun x => invFun (f x) ∘ (f x)) x dx) ∘ (invFun (f x)))
           =
           0 := by simp[invFun_comp (hf _).1.1]; fun_trans
  rw[← sub_zero (cderiv K (fun x => Function.invFun (f x)) x dx)]
  rw[← H]
  fun_trans
  sorry_proof
  -- simp_rw[comp.arg_fg_a0.cderiv_rule (K:=K) (fun x => invFun (f x)) f (by fun_prop) (by fun_prop)]
  -- simp[comp]
  -- funext z
  -- simp[show f x (invFun (f x) z) = z from sorry_proof]


@[fun_trans]
theorem Function.invFun.arg_f.cderiv_rule'
  (f : X → Y → Z) (z : Z)
  (hf : ∀ x, Diffeomorphism K (f x))
  (hf' : CDifferentiable K (fun xy : X×Y => f xy.1 xy.2))
  : cderiv K (fun x => invFun (f x) z)
    =
    fun x dx =>
      let y := invFun (f x) z
      let dfdx_y := (cderiv K f x dx) y
      let df'dy := cderiv K (invFun (f x)) (f x y) (dfdx_y)
      (-df'dy)
  :=
by
  funext x dx
  have H : ((cderiv K (fun x => invFun (f x) ∘ (f x)) x dx) ∘ (invFun (f x)) <| z)
           =
           0 := by simp[invFun_comp (hf _).1.1]; fun_trans
  rw[← sub_zero (cderiv K (fun x => Function.invFun (f x) z) x dx)]
  rw[← H]
  sorry_proof
  -- simp_rw[comp.arg_fg_a0.cderiv_rule (K:=K) (fun x => invFun (f x)) f (by fun_prop) (by fun_prop)]
  -- simp[comp]
  -- simp[show f x (invFun (f x) z) = z from sorry_proof]
