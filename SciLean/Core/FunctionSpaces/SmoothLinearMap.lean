import SciLean.Core.FunctionPropositions.IsSmoothLinearMap

set_option linter.unusedVariables false

namespace SciLean

variable
  (K : Type _) [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {W : Type _} [Vec K W]
  {ι : Type _} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]


-- Function space --------------------------------------------------------------
--------------------------------------------------------------------------------

structure SmoothLinearMap (X Y : Type _) [Vec K X] [Vec K Y] where
  toFun : X → Y
  is_smooth_linear_map : IsSmoothLinearMap K toFun

instance : FunLike (SmoothLinearMap K X Y) X Y where
  coe f := f.toFun
  coe_injective' := sorry_proof

macro X:term:25 " ⊸[" K:term "] " Y:term:26 : term =>
  `(SmoothLinearMap $K $X $Y)

macro X:term:25 " ⊸ " Y:term:26 : term =>
  `(SmoothLinearMap defaultScalar% $X $Y)

@[app_unexpander SmoothLinearMap] def unexpandSmoothLinearMap : Lean.PrettyPrinter.Unexpander
  | `($(_) $R $X $Y) => `($X ⊸[$R] $Y)
  | _ => throw ()


@[fun_prop]
theorem SmoothLinearMap_apply_right (f : X ⊸[K] Y) : IsSmoothLinearMap K (fun x => f x) := f.2


-- Lambda function notation ----------------------------------------------------
--------------------------------------------------------------------------------

variable {K}

@[simp, ftrans_simp]
theorem SmoothLinearMap.mk_eval (x : X) (f : X → Y) (hf : IsSmoothLinearMap K f) :
    mk f hf x = f x := by rfl

@[simp]
theorem SmoothLinearMap.eta_reduce (f : SmoothLinearMap K X Y) :
    (mk f.1 f.2) = f := by rfl

@[ext]
theorem SmoothLinearMap.ext (f g : X ⊸[K] Y) : (∀ x, f x = g x) → f = g := sorry_proof

variable (K)
def SmoothLinearMap.mk' (f : X → Y) (hf : IsSmoothLinearMap K f) : X ⊸[K] Y := ⟨f,hf⟩

@[simp, ftrans_simp]
theorem SmoothLinearMap.mk'_eval (x : X) (f : X → Y) (hf : IsSmoothLinearMap K f) :
    mk' K f hf x = f x := by rfl

open Lean Parser Term in
macro "fun " x:funBinder " ⊸[" K:term "] " b:term : term =>
  `(SmoothLinearMap.mk' $K (fun $x => $b) (by fun_prop))

open Lean Parser Term in
macro "fun " x:funBinder " ⊸ " b:term : term =>
  `(SmoothLinearMap.mk' defaultScalar% (fun $x => $b) (by fun_prop))

@[app_unexpander SmoothLinearMap.mk'] def unexpandSmoothLinearMapMk' : Lean.PrettyPrinter.Unexpander

  | `($(_) $R $f:term $_:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(fun $x' ⊸[$R] $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(fun ($x' : $ty) ⊸[$R] $b)
    | `(fun $x':ident : $ty => $b:term) => `(fun ($x' : $ty) ⊸[$R] $b)
    | _  => throw ()
  | _  => throw ()

@[app_unexpander SmoothLinearMap.mk] def unexpandSmoothLinearMapMk : Lean.PrettyPrinter.Unexpander

  | `($(_) $f:term $_:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(fun $x' ⊸ $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(fun ($x' : $ty) ⊸ $b)
    | `(fun $x':ident : $ty => $b:term) => `(fun ($x' : $ty) ⊸ $b)
    | _  => throw ()
  | _  => throw ()


-- Algebra ---------------------------------------------------------------------
--------------------------------------------------------------------------------

instance : Add (X ⊸[K] Y) := ⟨fun f g => fun x ⊸[K] f x + g x⟩
instance : Sub (X ⊸[K] Y) := ⟨fun f g => fun x ⊸[K] f x - g x⟩
instance : Neg (X ⊸[K] Y) := ⟨fun f => fun x ⊸[K] - f x⟩
instance : SMul K (X ⊸[K] Y) := ⟨fun r f => fun x ⊸[K] r • f x⟩
instance : Zero (X ⊸[K] Y) := ⟨fun x ⊸[K] 0⟩

section AlgebraSimps

variable (f g : X ⊸[K] Y) (x : X) (r : K)

@[simp, ftrans_simp]
theorem SmoothLinearMap.add_apply : (f + g) x = f x + g x := by rfl

@[simp, ftrans_simp]
theorem SmoothLinearMap.sub_apply : (f - g) x = f x - g x := by rfl

@[simp, ftrans_simp]
theorem SmoothLinearMap.neg_apply : (- f) x = - f x := by rfl

@[simp, ftrans_simp]
theorem SmoothLinearMap.smul_apply : (r • f) x = r • f x := by rfl

@[simp, ftrans_simp]
theorem SmoothLinearMap.zero_apply : (0 : X⊸[K]Y) x = 0 := by sorry_proof

@[simp,ftrans_simp]
theorem SmoothLinearMap.apply_zero (f : X ⊸[K] Y) : f 0 = 0 := by sorry_proof

end AlgebraSimps

instance : UniformSpace (X ⊸[K] Y) := sorry
instance : Vec K (X ⊸[K] Y) := Vec.mkSorryProofs

open BigOperators in
@[simp, ftrans_simp]
theorem SmoothLinearMap.fintype_sum_apply {I} [Fintype I] (f : I → X⊸[K] Y) (x : X) :
    (∑ i, f i) x = ∑ i, f i x  := by sorry_proof

@[simp, ftrans_simp]
theorem SmoothLinearMap.indextype_sum_apply {I} [IndexType I] (f : I → X⊸[K] Y) (x : X) :
    (∑ i, f i) x = ∑ i, f i x  := by sorry_proof



----------------------------------------------------------------------------------------------------


@[fun_prop]
theorem SmoothLinearMap.mk'.arg_f.IsSmoothLinearMap_rule
    (f : W → X → Y)
    (hf : CDifferentiable K (fun (w,x) => f w x))
    (hf₁ : ∀ x, IsSmoothLinearMap K (f · x)) (hf₂ : ∀ w, IsSmoothLinearMap K (f w ·)) :
    IsSmoothLinearMap K (fun w => (fun x ⊸[K] f w x)) := sorry_proof

@[fun_prop]
theorem SmoothLinearMap_apply_left
    (f : W → X ⊸[K] Y) (x : X) (hf : IsSmoothLinearMap K f) :
    IsSmoothLinearMap K fun w => (f w) x := sorry_proof

@[fun_prop]
theorem SmoothLinearMap.mk'.arg_f.CDifferentiable_rule
    (f : W → X ⊸[K] Y) (g : W → X) (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    CDifferentiable K (fun w => f w (g w)) := sorry_proof



set_default_scalar K

variable (f : X ⊸ Y)

-- TODO: fix this!!! What is going on??
#check f -- f : sorryAx (Type (max ?u.29009 ?u.28996)) true
