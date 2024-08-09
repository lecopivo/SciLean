import SciLean.Analysis.Convenient.ContCDiff
import SciLean.Analysis.Calculus.FwdCDeriv

import SciLean.Tactic.Autodiff
import SciLean.Util.RewriteBy

set_option linter.unusedVariables false

namespace SciLean

variable
  (K : Type _) [RCLike K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {W : Type _} [Vec K W]
  {ι : Type _} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]

local notation "∞" => (⊤ : ℕ∞)


-- Function space --------------------------------------------------------------
--------------------------------------------------------------------------------

structure ContCDiffMapFD (n : ℕ∞) (X Y : Type _)  [Vec K X] [Vec K Y] where
  toFun : X → X → Y×Y
  is_cont_cdiff_map : ContCDiff K n (fun x => (toFun x 0).1)
  cderiv_snd : cderiv K (fun x => (toFun x 0).1) = fun x dx => (toFun x dx).2
  dir_independence : ∀ x dx, toFun x dx = toFun x 0

attribute [simp, simp_core] ContCDiffMapFD.cderiv_snd ContCDiffMapFD.dir_independence

variable (n : ℕ∞)

instance : FunLike (ContCDiffMapFD K n X Y) X Y where
  coe f := fun x => (f.toFun x 0).1
  coe_injective' := sorry_proof

macro X:term:25 " ⟿FD[" K:term "," n:term "] " Y:term:26 : term =>
  `(ContCDiffMapFD $K $n $X $Y)

macro X:term:25 " ⟿FD[" n:term "] " Y:term:26 : term =>
  `(ContCDiffMapFD defaultScalar% $n $X $Y)

macro X:term:25 " ⟿FD " Y:term:26 : term =>
  `(ContCDiffMapFD defaultScalar% ∞ $X $Y)

@[app_unexpander ContCDiffMapFD] def unexpandContCDiffMapFD : Lean.PrettyPrinter.Unexpander
  | `($(_) $R $n $X $Y) => `($X ⟿FD[$R,$n] $Y)
  | _  => throw ()


@[fun_prop]
theorem ContCDiffMapFD_apply_right (f : X ⟿FD[K,n] Y) : ContCDiff K n (fun x => f x) := f.2


-- Lambda function notation ----------------------------------------------------
--------------------------------------------------------------------------------

def ContCDiffMapFD.mk' (f : X → Y) (f' : X → X → Y×Y) (h : fwdCDeriv K f = f') (hf : ContCDiff K n f) : X ⟿FD[K,n] Y :=
  ⟨f', sorry_proof, sorry_proof, sorry_proof⟩


open Lean Parser Term
macro "fun " x:funBinder " ⟿FD[" K:term "," n:term "] " b:term : term =>
  `(ContCDiffMapFD.mk' $K $n (fun $x => $b) ((fwdCDeriv $K fun $x => $b) rewrite_by autodiff /- check that derivative has been eliminated -/) (sorry_proof /- todo: add proof -/) sorry_proof)


macro "fun " x:funBinder " ⟿FD[" n:term "] " b:term : term => `(fun $x ⟿FD[defaultScalar%, $n] $b)
macro "fun " x:funBinder " ⟿FD "             b:term : term => `(fun $x ⟿FD[defaultScalar%,  ∞] $b)

variable {K n}

@[app_unexpander ContCDiffMapFD.mk'] def unexpandContCDiffMapFDMk : Lean.PrettyPrinter.Unexpander

  | `($(_) $R $n $f:term $_ $_ $_) =>
    match f with
    | `(fun $x':ident => $b:term) => `(fun $x' ⟿FD[$R,$n] $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(fun ($x' : $ty) ⟿FD[$R,$n] $b)
    | `(fun $x':ident : $ty => $b:term) => `(fun ($x' : $ty) ⟿FD[$R,$n] $b)
    | _  => throw ()
  | _  => throw ()

@[simp, simp_core]
theorem ContCDiffMapFD_eta (f : X ⟿FD[K,n] Y) : (fun x ⟿FD[K,n] f x) = f := by sorry_proof

def ContCDiffMapFD.FD (f : X ⟿FD[K,n] Y) (x dx : X) : Y×Y := f.toFun x dx

@[fun_trans]
theorem ContCDiffMapFD_eval_fwdCDeriv (f : X ⟿FD[K,n] Y) :
    fwdCDeriv K (fun x => f x) = f.FD := by
  unfold ContCDiffMapFD.FD fwdCDeriv
  simp[DFunLike.coe]

@[fun_prop]
theorem ContCDiffMapFD_eval_cdifferentiable (f : X ⟿FD[K,n] Y) (h : 0 < n) :
    CDifferentiable K (fun x => f x) := by
  simp[DFunLike.coe]
  apply CDifferentaible.ContCDiff_rule
  apply ContCDiffMapFD.is_cont_cdiff_map
  assumption

@[fun_prop]
theorem ContCDiffMapFD_eval_cdifferentiable' (f : X ⟿FD[K,∞] Y) :
    CDifferentiable K (fun x => f x) := by
  fun_prop (disch:=apply ENat.zero_lt_top)

@[simp, simp_core]
theorem ContCDiffMapFD.FD_fst (f : X ⟿FD[K,n] Y) (x dx : X) :
    (f.FD x dx).1 = f x := by rw[← ContCDiffMapFD_eval_fwdCDeriv]; unfold fwdCDeriv; simp


-- Algebra ---------------------------------------------------------------------
--------------------------------------------------------------------------------

variable (f g : X ⟿FD[K,∞] Y)

-- TODO: figure out what to do with `X ⟿FD[K,0] Y` and then change thse instancese to
--       `X ⟿FD[K,n] Y`
instance : Add (X ⟿FD[K,∞] Y) := ⟨fun f g => fun x ⟿FD[K,∞] f x + g x⟩
instance : Sub (X ⟿FD[K,∞] Y) := ⟨fun f g => fun x ⟿FD[K,∞] f x - g x⟩
instance : Neg (X ⟿FD[K,n] Y) := ⟨fun f => fun x ⟿FD[K,n] - f x⟩
instance : SMul K (X ⟿FD[K,∞] Y) := ⟨fun r f => fun x ⟿FD[K,∞] r • f x⟩
instance : Zero (X ⟿FD[K,n] Y) := ⟨fun (x : X) ⟿FD[K,n] (0:Y)⟩

section AlgebraSimps

variable (f g : X ⟿FD[K,∞] Y) (x : X) (r : K)

@[simp, simp_core]
theorem ContCDiffMapFD.add_apply : (f + g) x = f x + g x := by rfl

@[simp, simp_core]
theorem ContCDiffMapFD.sub_apply : (f - g) x = f x - g x := by rfl

@[simp, simp_core]
theorem ContCDiffMapFD.neg_apply : (- f) x = - f x := by rfl

@[simp, simp_core]
theorem ContCDiffMapFD.smul_apply : (r • f) x = r • f x := by rfl

@[simp, simp_core]
theorem ContCDiffMapFD.zero_apply : (0 : X ⟿FD[K,n] Y) x = 0 := by sorry_proof

end AlgebraSimps

instance : UniformSpace (X ⟿FD[K,n] Y) where
  IsOpen := default
  isOpen_univ := sorry_proof
  isOpen_inter := sorry_proof
  isOpen_sUnion := sorry_proof
  uniformity := default
  symm := sorry_proof
  comp := sorry_proof
  nhds_eq_comap_uniformity := sorry_proof

instance : Vec K (X ⟿FD[K,∞] Y) := Vec.mkSorryProofs


-- set_option trace.Meta.Tactic.fun_prop.attr true


-- The following two theorems are somehow related to catesian closedness of convenient vectors spaces
@[fun_prop]
theorem ContCDiffMapFD_apply (f : W → X ⟿FD[K,∞] Y) (g : W → X)
    (hf : ContCDiff K ∞ f) (hg : ContCDiff K ∞ g) : ContCDiff K ∞ (fun w => f w (g w)) := sorry_proof

-- this is hard to state as we have to be explicit about `f'`
@[fun_prop]
theorem ContCDiffMapFD.mk.arg_f.ContCDiff_rule (f : X → Y → Z) (f' : X → Y → Y → Z×Z)
    (hf : ContCDiff K ⊤ (fun xy : X×Y => f xy.1 xy.2))
    (h : ∀ x, SciLean.fwdCDeriv K (fun y => f x y) = f' x)
    (h' : ∀ x, ContCDiff K ∞ (f x))
    : ContCDiff K ∞ (fun x => (ContCDiffMapFD.mk' K ∞ (fun y => f x y) (f' x) (h x) (h' x))) := sorry_proof

-- I'm not sure if this is true but it sounds plausible
-- @[fun_prop]
-- theorem ContCDiffMapFD_partial (n : Nat) (f : W → X ⟿FD[K,n] Y) (g : W → X)
--     (hf : ContCDiff K n f) (hg : ContCDiff K n g) : ContCDiff K n (fun w => f w (g w)) := sorry_proof

-- -- I'm not sure if this is true but it sounds plausible
-- -- TODO: reformulate with `f'` as free variables as in `ContCDiffMapFD.mk.arg_f.ContCDiff_rule`
-- @[fun_prop]
-- theorem ContCDiffMapFD.mk.arg_f.ContCDiff_rule_partial (n l k : ℕ) (f : X → Y → Z)
--     (hf : ContCDiff K n (fun xy : X×Y => f xy.1 xy.2)) (h : l + k ≤ n) :
--     ContCDiff K k (fun x => (fun y ⟿FD[K,l] f x y)) := sorry_proof


----------------------------------------------------------------------------------------------------

@[fun_prop]
theorem ContCDiffMapFD_apply_linearSmoothMap
    (f : W → X ⟿FD[K,∞] Y) (hf : IsSmoothLinearMap K f) (x : X) :
    IsSmoothLinearMap K (fun w => f w x) := sorry_proof

-- this is hard to state as we have to be explicit about `f'`
@[fun_prop]
theorem ContCDiffMapFD.mk.arg_f.IsSmoothLinearMap_rule
    (f : W → X → Y) (f' : W → X → X → Y×Y)
    (hf₁ : CDifferentiable K (fun (w,x) => f w x))
    (hf₂ : IsLinearMap K f)
    (hf₃ : ∀ w, ContCDiff K ∞ (f w))
    (h : ∀ w, (SciLean.fwdCDeriv K fun x => f w x) = f' w)
    (h' : ∀ w, ContCDiff K ∞ (f w)) :
    IsSmoothLinearMap K (fun w => ContCDiffMapFD.mk' K ∞ (fun x => f w x) (f' w) (h w) (h' w)) := sorry_proof

example : IsLinearMap K (fun (w : K) => fun (x : K) ⟿FD[K,∞] w*x + w) := by fun_prop
example : (cderiv K fun (w : K) => fun (x : K) ⟿FD[K,∞] w*x + w)
          =
          fun w dw => fun (x : K) ⟿FD[K,∞] dw*x + dw := by
  (conv => lhs; fun_trans)

@[fun_prop]
theorem ContCDiffMapFD_eval_CDifferentiable :
    CDifferentiable K (fun (fx : (X ⟿FD[K,∞] Y)×X) => fx.1 fx.2) := by sorry_proof


@[fun_prop]
theorem ContCDiffMapFD_apply_CDifferentiable (f : W → X ⟿FD[K,∞] Y) (g : W → X)
    (hf : CDifferentiable K f) (hg : CDifferentiable K g) : CDifferentiable K (fun w => f w (g w)) := by sorry_proof

@[fun_prop]
theorem ContCDiffMapFD_apply_CDifferentiableAt (f : W → X ⟿FD[K,∞] Y) (g : W → X) (w : W)
    (hf : CDifferentiableAt K f w) (hg : CDifferentiableAt K g w) : CDifferentiableAt K (fun w => f w (g w)) w := by sorry_proof


@[fun_trans]
theorem ContCDiffMapFD_cderiv_rule (f : W → (X ⟿FD[K,∞] Y)×Z) (g : W → X) :
    cderiv K (fun w => (f w).1 (g w))
    =
    fun w dw =>
      let dfz := cderiv K f w dw
      let fwz := f w
      let x := g w
      let dx := cderiv K g w dw
      dfz.1 x + (fwz.1.FD x dx).2 := sorry_proof

@[fun_trans]
theorem ContCDiffMapFD_fwdCDeriv_rule (f : W → (X ⟿FD[K,∞] Y)×Z) (g : W → X) :
    fwdCDeriv K (fun w => (f w).1 (g w))
    =
    fun w dw =>
      let fdfz := fwdCDeriv K f w dw
      let xdx := fwdCDeriv K g w dw
      let fw := fdfz.1.1
      let df := fdfz.2.1
      let zdz := fw.FD xdx.1 xdx.2
      (zdz.1, df xdx.1 + zdz.2) := by
  unfold fwdCDeriv
  fun_trans
