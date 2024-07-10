import SciLean.Core.FunctionPropositions.CDifferentiable
import SciLean.Core.FunctionPropositions.IsSmoothLinearMap

import SciLean.Core.Meta.GenerateLinearMapSimp

import SciLean.Tactic.FunTrans.Attr
import SciLean.Tactic.FunTrans.Elab

set_option linter.unusedVariables false
set_option linter.hashCommand false

open LeanColls

namespace SciLean

variable
  (K : Type _) [RCLike K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {W : Type _} [Vec K W]
  {ι : Type _} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]

@[fun_trans]
noncomputable
def cderiv (f : X → Y) (x dx : X) : Y := Curve.deriv (fun t : K => f (x + t•dx)) 0

@[ftrans_simp]
noncomputable
def scalarCDeriv (f : K → X) (t : K) : X := cderiv K f t 1


-- Basic identities ------------------------------------------------------------
--------------------------------------------------------------------------------

variable {K}
@[fun_trans]
theorem cderiv_of_linear (f : X → Y) (hf : IsSmoothLinearMap K f)
  : cderiv K f = fun x dx => f dx := sorry_proof

@[simp, ftrans_simp]
theorem cderiv_apply
  (f : X → Y → Z) (x dx : X) (y : Y)
  : cderiv K f x dx y
    =
    cderiv K (fun x' => f x' y) x dx := sorry_proof

@[simp, ftrans_simp]
theorem cderiv_apply_zero
  (f : X → Y) (x : X)
  : cderiv K f x 0
    =
    0 := sorry_proof

@[fun_prop]
theorem cderiv.arg_dx.IsLinearMap_rule_simple
  (f : X → Y) (x : X) (hf : CDifferentiableAt K f x)
  : IsLinearMap K (fun dx => cderiv K f x dx) := sorry_proof

#generate_linear_map_simps SciLean.cderiv.arg_dx.IsLinearMap_rule_simple

@[fun_prop]
theorem cderiv.arg_dx.IsLinearMap_rule
  (f : X → Y) (x : X) (dx : W → X) (hf : CDifferentiableAt K f x) (hdx : IsLinearMap K dx)
  : IsLinearMap K (fun w => cderiv K f x (dx w)) := by fun_prop


@[fun_prop]
theorem cderiv.arg_f.IsLinearMap_rule
    (f : X → Y → Z) (hf : ∀ x, CDifferentiable K (fun y => f x y)) (hf' : ∀ y, IsLinearMap K (fun x => f x y)) :
    IsLinearMap K (fun x => cderiv K (f x ·)) := sorry_proof

@[fun_prop]
theorem cderiv.arg_f.IsSmoothLinearMap_rule
    (f : X → Y → Z) (hf : CDifferentiable K (fun (x,y) => f x y)) (hf' : ∀ y, IsLinearMap K (fun x => f x y)) :
    IsSmoothLinearMap K (fun x => cderiv K (f x ·)) := by constructor; fun_prop; sorry_proof /- differentiable and linear implies smooth -/


variable (K)

-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------
@[fun_trans]
theorem cderiv.id_rule :
    (cderiv K fun x : X => x) = fun _ => fun dx => dx := by sorry_proof

@[fun_trans]
theorem cderiv.const_rule (x : X) :
    (cderiv K fun _ : Y => x) = fun _ => fun dx => 0 := by sorry_proof

@[fun_trans]
theorem cderiv.comp_rule_at
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : CDifferentiableAt K f (g x)) (hg : CDifferentiableAt K g x)
  : (cderiv K fun x : X => f (g x)) x
    =
    let y := g x
    fun dx =>
      let dy := cderiv K g x dx
      let dz := cderiv K f y dy
      dz :=
by sorry_proof

@[fun_trans]
theorem cderiv.comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : CDifferentiable K f) (hg : CDifferentiable K g)
  : (cderiv K fun x : X => f (g x))
    =
    fun x =>
      let y := g x
      fun dx =>
        let dy := cderiv K g x dx
        let dz := cderiv K f y dy
        dz :=
by sorry_proof

@[fun_trans]
theorem cderiv.let_rule_at
  (f : X → Y → Z) (g : X → Y) (x : X)
  (hf : CDifferentiableAt K ↿f (x, g x))
  (hg : CDifferentiableAt K g x)
  : (cderiv K
      fun x : X =>
        let y := g x
        f x y) x
    =
    let y  := g x
    fun dx =>
      let dy := cderiv K g x dx
      let dz := cderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
      dz :=
by sorry_proof

@[fun_trans]
theorem cderiv.let_rule
  (f : X → Y → Z) (g : X → Y)
  (hf : CDifferentiable K fun xy : X×Y => f xy.1 xy.2) (hg : CDifferentiable K g)
  : (cderiv K fun x : X =>
       let y := g x
       f x y)
    =
    fun x =>
      let y  := g x
      fun dx =>
        let dy := cderiv K g x dx
        let dz := cderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
        dz :=
by sorry_proof

@[fun_trans]
theorem cderiv.apply_rule (i : ι) :
    (cderiv K fun (x : (i : ι) → E i) => x i)
    =
    fun _ => fun dx => dx i := by sorry_proof

@[fun_trans]
theorem cderiv.pi_rule_at
  (f : X → (i : ι) → E i) (x : X) (hf : ∀ i, CDifferentiableAt K (f · i) x)
  : (cderiv K fun (x : X) (i : ι) => f x i) x
    =
    fun dx => fun i =>
      cderiv K (f · i) x dx
  := by sorry_proof

@[fun_trans]
theorem cderiv.pi_rule
  (f : X → (i : ι) → E i) (hf : ∀ i, CDifferentiable K (f · i))
  : (cderiv K fun (x : X) (i : ι) => f x i)
    =
    fun x => fun dx => fun i =>
      cderiv K (f · i) x dx
  := by sorry_proof



--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean
open LeanColls

variable
  {K : Type _} [RCLike K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {W : Type _} [Vec K W]
  {ι : Type _} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]


-- Prod.mk -----------------------------------v---------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.mk.arg_fstsnd.cderiv_rule_at (x : X)
    (g : X → Y) (hg : CDifferentiableAt K g x)
    (f : X → Z) (hf : CDifferentiableAt K f x) :
    cderiv K (fun x => (g x, f x)) x
    =
    fun dx =>
      (cderiv K g x dx, cderiv K f x dx) := by
  sorry_proof


@[fun_trans]
  theorem Prod.mk.arg_fstsnd.cderiv_rule
    (g : X → Y) (hg : CDifferentiable K g)
    (f : X → Z) (hf : CDifferentiable K f) :
    cderiv K (fun x => (g x, f x))
    =
    fun x => fun dx =>
      (cderiv K g x dx, cderiv K f x dx) := by funext x; fun_trans


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.fst.arg_self.cderiv_rule_at (x : X)
    (f : X → Y×Z) (hf : CDifferentiableAt K f x) :
    cderiv K (fun x => (f x).1) x
    =
    fun dx => (cderiv K f x dx).1 := by fun_trans

@[fun_trans]
theorem Prod.fst.arg_self.cderiv_rule
    (f : X → Y×Z) (hf : CDifferentiable K f) :
    cderiv K (fun x => (f x).1)
    =
    fun x dx => (cderiv K f x dx).1 := by funext x; fun_trans


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.snd.arg_self.cderiv_rule_at (x : X)
    (f : X → Y×Z) (hf : CDifferentiableAt K f x) :
    cderiv K (fun x => (f x).2) x
    =
    fun dx => (cderiv K f x dx).2 := by fun_trans

@[fun_trans]
theorem Prod.snd.arg_self.cderiv_rule
    (f : X → Y×Z) (hf : CDifferentiable K f) :
    cderiv K (fun x => (f x).2)
    =
    fun x => fun dx => (cderiv K f x dx).2 := by funext x; fun_trans


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.cderiv_rule_at (x : X)
    (f g : X → Y) (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) :
    (cderiv K fun x => f x + g x) x
    =
    fun dx =>
      cderiv K f x dx + cderiv K g x dx := by fun_trans


@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.cderiv_rule
    (f g : X → Y) (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    (cderiv K fun x => f x + g x)
    =
    fun x => fun dx =>
      cderiv K f x dx + cderiv K g x dx := by funext x; fun_trans

@[fun_trans]
theorem HAdd.hAdd.arg_a0.cderiv_rule
    (f : X → Y) (y : Y) :
    (cderiv K fun x => f x + y)
    =
    fun x dx =>
      cderiv K f x dx := by funext x; sorry_proof

@[fun_trans]
theorem HAdd.hAdd.arg_a1.cderiv_rule
    (f : X → Y) (y : Y) :
    (cderiv K fun x => y + f x)
    =
    fun x dx =>
      cderiv K f x dx := by funext x; sorry_proof


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSub.hSub.arg_a0a1.cderiv_rule_at (x : X)
    (f g : X → Y) (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) :
    (cderiv K fun x => f x - g x) x
    =
    fun dx =>
      cderiv K f x dx - cderiv K g x dx := by fun_trans


@[fun_trans]
theorem HSub.hSub.arg_a0a1.cderiv_rule
    (f g : X → Y) (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    (cderiv K fun x => f x - g x)
    =
    fun x => fun dx =>
      cderiv K f x dx - cderiv K g x dx := by funext x; fun_trans

@[fun_trans]
theorem HSub.hSub.arg_a0.cderiv_rule
    (f : X → Y) (y : Y) :
    (cderiv K fun x => f x - y)
    =
    fun x dx =>
      cderiv K f x dx := by funext x; sorry_proof

@[fun_trans]
theorem HSub.hSub.arg_a1.cderiv_rule
    (f : X → Y) (y : Y) :
    (cderiv K fun x => y - f x)
    =
    fun x dx =>
      - cderiv K f x dx := by funext x; sorry_proof



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.cderiv_rule' (x : X) (f : X → Y) :
    (cderiv K fun x => - f x) x
    =
    fun dx => - cderiv K f x dx := by sorry_proof

@[fun_trans]
theorem Neg.neg.arg_a0.cderiv_rule (f : X → Y) :
    (cderiv K fun x => - f x)
    =
    fun x => fun dx => - cderiv K f x dx := by funext x; fun_trans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HMul.hMul.arg_a0a1.cderiv_rule_at (x : X) (f g : X → K)
    (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) :
    (cderiv K fun x => f x * g x) x
    =
    let fx := f x
    let gx := g x
    fun dx =>
      (cderiv K g x dx) * fx + (cderiv K f x dx) * gx := by sorry_proof


@[fun_trans]
theorem HMul.hMul.arg_a0a1.cderiv_rule (f g : X → K)
    (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    (cderiv K fun x => f x * g x)
    =
    fun x =>
      let fx := f x
      let gx := g x
      fun dx =>
        (cderiv K g x dx) * fx + (cderiv K f x dx) * gx := by funext x; fun_trans


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.cderiv_rule_at (x : X) (f : X → K) (g : X → Y)
    (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) :
    (cderiv K fun x => f x • g x) x
    =
    let k := f x
    let y := g x
    fun dx =>
      k • (cderiv K g x dx) + (cderiv K f x dx) • y := by sorry_proof

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.cderiv_rule (f : X → K) (g : X → Y)
    (hf : CDifferentiable K f) (hg : CDifferentiable K g) :
    (cderiv K fun x => f x • g x)
    =
    fun x =>
      let k := f x
      let y := g x
      fun dx =>
        k • (cderiv K g x dx) + (cderiv K f x dx) • y := by funext x; fun_trans


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.cderiv_rule_at (x : X) (f : X → K) (g : X → K)
    (hf : CDifferentiableAt K f x) (hg : CDifferentiableAt K g x) (hx : g x ≠ 0) :
    (cderiv K fun x => f x / g x) x
    =
    let k := f x
    let k' := g x
    fun dx =>
      ((cderiv K f x dx) * k' - k * (cderiv K g x dx)) / k'^2 := by sorry_proof

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.cderiv_rule (f : X → K) (g : X → K)
    (hf : CDifferentiable K f) (hg : CDifferentiable K g) (hx : ∀ x, g x ≠ 0) :
    (cderiv K fun x => f x / g x)
    =
    fun x =>
      let k := f x
      let k' := g x
      fun dx =>
        ((cderiv K f x dx) * k' - k * (cderiv K g x dx)) / k'^2 := by
  funext x; fun_trans (disch:=assumption); sorry_proof



-- HPow.hPow ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
def HPow.hPow.arg_a0.cderiv_rule_at (n : Nat) (x : X)
    (f : X → K) (hf : CDifferentiableAt K f x) :
    cderiv K (fun x => f x ^ n) x
    =
    fun dx => n * cderiv K f x dx * (f x ^ (n-1)) := by
  induction n
  case zero =>
    simp; fun_trans
  case succ n hn =>
    ext dx
    simp_rw[pow_succ]
    fun_trans
    induction n
    case zero => simp
    case succ => rw[pow_succ]; simp; ring

@[fun_trans]
def HPow.hPow.arg_a0.cderiv_rule (n : Nat)
    (f : X → K) (hf : CDifferentiable K f) :
    cderiv K (fun x => f x ^ n)
    =
    fun x => fun dx => n * cderiv K f x dx * (f x ^ (n-1)) := by
  funext x; fun_trans


-- IndexType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem IndexType.sum.arg_f.cderiv_rule_at
  (f : X → ι → Y) (x : X) (hf : ∀ i, CDifferentiableAt K (f · i) x)
  : cderiv K (fun x => ∑ i, f x i) x
    =
    fun dx => ∑ i, cderiv K (f · i) x dx :=
by
  fun_trans
  sorry_proof


@[fun_trans]
theorem IndexType.sum.arg_f.cderiv_rule
  (f : X → ι → Y) (hf : ∀ i, CDifferentiable K (f · i))
  : cderiv K (fun x => ∑ i, f x i)
    =
    fun x dx => ∑ i, cderiv K (f · i) x dx :=
by
  funext x; fun_trans


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem ite.arg_te.cderiv_rule
  (c : Prop) [dec : Decidable c] (t e : X → Y)
  : cderiv K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (cderiv K t y) (cderiv K e y) :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]

@[fun_trans]
theorem dite.arg_te.cderiv_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (e : ¬c → X → Y)
  : cderiv K (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => cderiv K (t p) y)
             (fun p => cderiv K (e p) y) :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]


-- not sure about the differentiability condition on `e`
theorem ite.arg_chte.cderiv_rule
  (c : X → Prop) [dec : ∀ x, Decidable (c x)] (t e : X → Y)
  (ht : ∀ x ∈ closure c, CDifferentiableAt K t x) (he : ∀ x ∈ (interior c)ᶜ, CDifferentiableAt K e x)
  (hc : (∀ x, x ∈ frontier c → cderiv K t x = cderiv K e x))
  : cderiv K (fun x => ite (c x) (t x) (e x))
    =
    fun y =>
      ite (c y) (cderiv K t y) (cderiv K e y) :=
by
  sorry_proof


--------------------------------------------------------------------------------

section InnerProductSpace

-- Inner -----------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate

section OverReals

variable
  {R : Type _} [RealScalar R]
  {X : Type _} [Vec R X]
  {Y : Type _} [SemiHilbert R Y]


@[fun_trans]
theorem Inner.inner.arg_a0a1.cderiv_rule_at
  (f : X → Y) (g : X → Y) (x : X)
  (hf : CDifferentiableAt R f x) (hg : CDifferentiableAt R g x)
  : cderiv R (fun x => ⟪f x, g x⟫[R]) x
    =
    fun dx =>
      let y₁ := f x
      let dy₁ := cderiv R f x dx
      let y₂ := g x
      let dy₂ := cderiv R g x dx
      ⟪dy₁, y₂⟫[R] + ⟪y₁, dy₂⟫[R] :=
by
  sorry_proof


@[fun_trans]
theorem Inner.inner.arg_a0a1.cderiv_rule
  (f : X → Y) (g : X → Y)
  (hf : CDifferentiable R f) (hg : CDifferentiable R g)
  : cderiv R (fun x => ⟪f x, g x⟫[R])
    =
    fun x dx =>
      let y₁ := f x
      let dy₁ := cderiv R f x dx
      let y₂ := g x
      let dy₂ := cderiv R g x dx
      ⟪dy₁, y₂⟫[R] + ⟪y₁, dy₂⟫[R] :=
by
  funext x; apply Inner.inner.arg_a0a1.cderiv_rule_at f g x (hf x) (hg x)

@[fun_trans]
theorem Norm2.norm2.arg_a0.cderiv_rule_at
  (f : X → Y) (x : X)
  (hf : CDifferentiableAt R f x)
  : cderiv R (fun x => ‖f x‖₂²[R]) x
    =
    fun dx =>
      let y := f x
      let dy := cderiv R f x dx
      2 * ⟪dy, y⟫[R] :=
by
  simp_rw [← SemiInnerProductSpace.inner_norm2]
  fun_trans
  funext dx
  conv =>
    lhs; enter[2]
    rw [← SemiInnerProductSpace.conj_sym]
  simp
  ring

@[fun_trans]
theorem Norm2.norm2.arg_a0.cderiv_rule
  (f : X → Y)
  (hf : CDifferentiable R f)
  : cderiv R (fun x => ‖f x‖₂²[R])
    =
    fun x dx =>
      let y := f x
      let dy := cderiv R f x dx
      2 * ⟪dy, y⟫[R] :=
by
  funext x; apply Norm2.norm2.arg_a0.cderiv_rule_at f x (hf x)

@[fun_trans]
theorem norm₂.arg_x.cderiv_rule_at
  (f : X → Y) (x : X)
  (hf : CDifferentiableAt R f x) (hx : f x≠0)
  : cderiv R (fun x => ‖f x‖₂[R]) x
    =
    fun dx =>
      let y := f x
      let dy := cderiv R f x dx
      ‖y‖₂[R]⁻¹ * ⟪dy,y⟫[R] :=
by
  sorry_proof


@[fun_trans]
theorem norm₂.arg_x.cderiv_rule
  (f : X → Y)
  (hf : CDifferentiable R f) (hx : ∀ x, f x≠0)
  : cderiv R (fun x => ‖f x‖₂[R])
    =
    fun x dx =>
      let y := f x
      let dy := cderiv R f x dx
      ‖y‖₂[R]⁻¹ * ⟪dy,y⟫[R] :=
by
  funext x
  rw [norm₂.arg_x.cderiv_rule_at f x (hf x) (hx x)]


end OverReals

end InnerProductSpace

-- cderiv ----------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_prop]
theorem cderiv.arg_dx.CDifferentiableAt_rule
  (f : Y → Z) (g : X → Y) (y : Y) (dx : X)
  (hf : CDifferentiableAt K f y) (hg : CDifferentiableAt K g dx)
  : CDifferentiableAt K (fun dx' => cderiv K f y (g dx')) dx :=
by
  sorry_proof

@[fun_prop]
theorem cderiv.arg_dx.CDifferentiable_rule
  (f : Y → Z) (g : X → Y) (y : Y)
  (hf : CDifferentiable K f) (hg : CDifferentiable K g)
  : CDifferentiable K (fun dx' => cderiv K f y (g dx')) :=
by
  intro dx
  apply cderiv.arg_dx.CDifferentiableAt_rule
  apply (hf y)
  apply (hg dx)


@[fun_trans]
theorem cderiv.arg_dx.cderiv_rule_at
  (f : Y → Z) (g : X → Y) (y : Y) (dx : X)
  (hf : CDifferentiableAt K f y) (hg : CDifferentiableAt K g dx)
  : cderiv K (fun dx' => cderiv K f y (g dx')) dx
    =
    fun ddx =>
      let ddy := cderiv K g dx ddx
      cderiv K f y ddy :=
by
  sorry_proof

@[fun_trans]
theorem cderiv.arg_dx.cderiv_rule
  (f : Y → Z) (g : X → Y) (y : Y)
  (hf : CDifferentiable K f) (hg : CDifferentiable K g)
  : cderiv K (fun dx => cderiv K f y (g dx))
    =
    fun dx ddx =>
      let ddy := cderiv K g dx ddx
      cderiv K f y ddy :=
by
  funext dx
  apply cderiv.arg_dx.cderiv_rule_at _ _ _ _ (hf y) (hg dx)
