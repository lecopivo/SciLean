import SciLean.Analysis.Calculus.FDeriv
import SciLean.Logic.Function.Bijective

set_option linter.unusedVariables false
open SciLean

variable
  (K : Type _) [RCLike K]
  {W : Type _} [NormedAddCommGroup W] [NormedSpace K W]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
  -- {ι : Type _} [IndexType ι] [DecidableEq ι]

namespace SciLean

@[fun_prop]
structure Diffeomorphism (f : X → Y) : Prop where
  bijective : Function.Bijective f
  differentiable : Differentiable K f
  locally_diffeo : ∀ x, Function.Bijective (fderiv K f x)

-- This is a bad theorems as you can't infer `K` from the conclusion
-- @[fun_prop]
theorem diffeomorphism_to_bijective (f : X → Y) (hf : Diffeomorphism K f) :
    Function.Bijective f := hf.1

@[fun_prop]
theorem diffeomorphism_to_differentiables (f : X → Y) (hf : Diffeomorphism K f) :
    Differentiable K f := hf.2

@[fun_prop]
theorem cderiv.arg_dx.Bijective_rule (f : X → Y) (x : X) (hf : Diffeomorphism K f) :
    Function.Bijective (fun dx => fderiv K f x dx) := hf.3 x

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
  (hf' : Differentiable K (fun xy : X×Y => f xy.1 xy.2))
  (hg : Differentiable K g) (hh : Differentiable K h)
  : Differentiable K (fun w : W => invFun (f (g w)) (h w)) := sorry_proof


@[fun_trans]
theorem Function.invFun.arg_a1.fderiv_rule
  (f : Y → Z) (g : X → Z)
  (hf : Diffeomorphism K f) (hg : Differentiable K g)
  : fderiv K (fun x => invFun f (g x))
    =
    fun x => ContinuousLinearMap.mk' K (fun dx =>
      let z := g x
      let dz := fderiv K g x dx
      let y := invFun f z
      let dy := invFun (fderiv K f y) dz
      dy) sorry_proof :=
by
  ext x dx
  have H : (fun dx => (fderiv K (f ∘ invFun f) (g x)) dx)
           =
           id := by simp[show (f ∘ Function.invFun f) = id from sorry_proof]; unfold id; fun_trans
  have q : fderiv K f (invFun f (g x)) (fderiv K (fun x => invFun f (g x)) x dx) = fderiv K g x dx := sorry_proof
  sorry_proof

-- Which rule is preferable? This one or the second one?
-- Probably the second as it has Function.inv fully applied
-- This can't be stated as `Z → Y` is not normed space
-- @[fun_trans]
-- theorem Function.invFun.arg_f_a1.fderiv_rule
--   (f : X → Y → Z)
--   (hf : ∀ x, Diffeomorphism K (f x))
--   (hf' : Differentiable K (fun xy : X×Y => f xy.1 xy.2))
--   : fderiv K (fun x z => invFun (f x) z)
--     =
--     fun x => fun dx =>L[K] fun z =>
--       let y := invFun (f x) z
--       let dfdx_y := (fderiv K f x dx) y
--       let df'dy := fderiv K (invFun (f x)) (f x y) (dfdx_y)
--       (-df'dy)
--   :=
-- by
--   funext x dx
--   have H : ((fderiv K (fun x => invFun (f x) ∘ (f x)) x dx) ∘ (invFun (f x)))
--            =
--            0 := by simp[invFun_comp (hf _).1.1]; fun_trans
--   rw[← sub_zero (fderiv K (fun x => Function.invFun (f x)) x dx)]
--   rw[← H]
--   fun_trans
--   sorry_proof


@[fun_trans]
theorem Function.invFun.arg_f.fderiv_rule'
  (f : X → Y → Z) (z : Z)
  (hf : ∀ x, Diffeomorphism K (f x))
  (hf' : Differentiable K (fun xy : X×Y => f xy.1 xy.2))
  : fderiv K (fun x => invFun (f x) z)
    =
    fun x => ContinuousLinearMap.mk' K (fun dx =>
      let y := invFun (f x) z
      let dfdx_y := (fderiv K (f · y) x dx)
      let df'dy := fderiv K (invFun (f x)) (f x y) (dfdx_y)
      (-df'dy)) sorry_proof
  :=
by
  ext x dx
  sorry_proof
  -- have H : ((fderiv K (fun x => invFun (f x) ∘ (f x)) x dx) ∘ (invFun (f x)) <| z)
  --          =
  --          0 := by simp[invFun_comp (hf _).1.1]; fun_trans
  -- rw[← sub_zero (fderiv K (fun x => Function.invFun (f x) z) x dx)]
  -- rw[← H]
  -- simp_rw[comp.arg_fg_a0.fderiv_rule (K:=K) (fun x => invFun (f x)) f (by fun_prop) (by fun_prop)]
  -- simp[comp]
  -- simp[show f x (invFun (f x) z) = z from sorry_proof]
