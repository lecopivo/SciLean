import SciLean.FTrans.Adjoint.Basic

namespace  SciLean

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [InnerProductSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace K (E i)] [∀ i, CompleteSpace (E i)]


variable (K)

noncomputable
def adjoint' (f : X → Y) : Y → X :=
  match Classical.dec (IsContinuousLinearMap K f) with
  | isTrue h => (fun x =>L[K] f x)† 
  | isFalse _ => 0


-- Set up custom notation for adjoint. Mathlib's notation for adjoint seems to be broken
instance (f : X → Y) : SciLean.Dagger f (adjoint' K f) := ⟨⟩


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

namespace adjoint'

variable (X) 
theorem id_rule 
  : adjoint' K (fun (x : X) => x) = fun x => x := 
by
  unfold adjoint';
  cases (Classical.dec _)
  case isFalse h' => cases (h' (by fprop))
  case isTrue  h' => ext x; simp; ftrans


variable (Y)
theorem const_rule 
  : adjoint' K (fun (_ : X) => (0 : Y)) = fun x => 0 := 
by
  unfold adjoint';
  cases (Classical.dec _)
  case isFalse h' => cases (h' (by fprop))
  case isTrue  h' => ext x; simp; ftrans

variable {Y}

theorem proj_rule [DecidableEq ι]
   (i : ι) 
  : adjoint' K (fun (f : PiLp 2 (fun _ => X)) => f i)
    = 
    fun x => (fun j => if _ : i=j then x else (0 : X)) :=
by
  unfold adjoint';
  cases (Classical.dec _)
  case isFalse h' => cases (h' (by fprop))
  case isTrue  h' => ext x; simp; ftrans

variable {X}

theorem comp_rule 
  (f : Y → Z) (g : X → Y) 
  (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g)
  : adjoint' K (fun x => f (g x))
    =
    fun z =>
      let y := adjoint' K (fun y => f y) z
      let x := adjoint' K (fun x => g x) y
      x := 
by
  unfold adjoint'
  cases (Classical.dec _)
  case isFalse h' => cases (h' (by fprop))
  case isTrue  h' => 
    simp
    cases (Classical.dec _)
    case isFalse h'' => cases (h'' (by fprop))
    case isTrue  h'' => 
      simp
      cases (Classical.dec _)
      case isFalse h'' => cases (h'' (by fprop))
      case isTrue  h'' => ext _; simp; ftrans


theorem let_rule 
  (f : X → Y → Z) (g : X → Y)      
  (hf : IsContinuousLinearMap K (fun xy : X×Y => f xy.1 xy.2)) (hg : IsContinuousLinearMap K g)
  : adjoint' K (fun x => let y := g x; f x y)
    =
    fun z =>
      let xy := (adjoint' K (fun xy : X×₂Y => f xy.1 xy.2)) z
      let x' := (adjoint' K (fun x => g x)) xy.2
      xy.1 + x' := 
by
  sorry


open BigOperators in
theorem pi_rule
  (f : X → (i : ι) → E i) (hf : ∀ i, IsContinuousLinearMap K (f · i))
  : adjoint' K (Y:=PiLp 2 E) ((fun (x : X) => fun (i : ι) => f x i))
    = 
    (fun x' => ∑ i, adjoint' K (fun x => f x i) (x' i))
  := sorry



-- Register `adjoint'` as function transformation -------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq

def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `fwdDeriv_discharger (fun _ => return s!"discharge {← ppExpr e}") do
  let cache := (← get).cache
  let config : FProp.Config := {}
  let state  : FProp.State := { cache := cache }
  let (proof?, state) ← FProp.fprop e |>.run config |>.run state
  modify (fun simpState => { simpState with cache := state.cache })
  if proof?.isSome then
    return proof?
  else
    -- if `fprop` fails try assumption
    let tac := FTrans.tacticToDischarge (Syntax.mkLit ``Lean.Parser.Tactic.assumption "assumption")
    let proof? ← tac e
    return proof?

open Lean Elab Term FTrans
def ftransExt : FTransExt where
  ftransName := ``adjoint'

  getFTransFun? e := 
    if e.isAppOf ``adjoint' then

      if let .some f := e.getArg? 10 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``adjoint' then
      e.modifyArg (fun _ => f) 10
    else          
      e

  prodMk := ``ProdL2.mk
  prodFst := ``ProdL2.fst
  prodSnd := ``ProdL2.snd

  idRule  e X := do
    let K := e.getArg! 0
    tryTheorems
      #[ { proof := ← mkAppM ``id_rule #[K, X], origin := .decl ``id_rule, rfl := false} ]
      discharger e

  constRule e X y := do
    let K := e.getArg! 0
    tryTheorems
      #[ { proof := ← mkAppM ``const_rule #[K, X, (← inferType y)], origin := .decl ``const_rule, rfl := false} ]
      discharger e

  projRule e X i := do
    let K := e.getArg! 0
    let X' := X.bindingBody!
    if X'.hasLooseBVars then
      trace[Meta.Tactic.ftrans.step] "can't handle this bvar app case, projection rule for dependent function of type {← ppExpr X} is not supported"
      return none
    tryTheorems
      #[ { proof := ← mkAppM ``proj_rule #[K, X', i], origin := .decl ``proj_rule, rfl := false } ]
      discharger e

  compRule e f g := do
    let K := e.getArg! 0
    tryTheorems
      #[ { proof := ← mkAppM ``comp_rule #[K, f, g], origin := .decl ``comp_rule, rfl := false } ]
      discharger e

  letRule e f g := do
    let K := e.getArg! 0
    tryTheorems
      #[ { proof := ← mkAppM ``let_rule #[K, f, g], origin := .decl ``let_rule, rfl := false } ]
      discharger e

  piRule  e f := do
    let K := e.getArg! 0
    tryTheorems
      #[ { proof := ← mkAppM ``pi_rule #[K, f], origin := .decl ``pi_rule, rfl := false } ]
      discharger e

  discharger := discharger


-- register adjoint'
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``adjoint', adjoint'.ftransExt))

end SciLean.adjoint'


--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [InnerProductSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace K (E i)] [∀ i, CompleteSpace (E i)]

open SciLean


-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.mk.arg_fstsnd.adjoint'_rule
  (g : X → Y) (hg : IsContinuousLinearMap K g)
  (f : X → Z) (hf : IsContinuousLinearMap K f)
  : adjoint' K (Y:=Y×₂Z) (fun x => (g x, f x))
    =
    fun yz =>
      let x₁ := adjoint' K g yz.1
      let x₂ := adjoint' K f yz.2
      x₁ + x₂ :=
by sorry


@[ftrans]
theorem SciLean.ProdL2.mk.arg_fstsnd.adjoint'_rule
  (g : X → Y) (hg : IsContinuousLinearMap K g)
  (f : X → Z) (hf : IsContinuousLinearMap K f)
  : adjoint' K (fun x => ProdL2.mk (g x) (f x))
    =
    fun yz =>
      let x₁ := adjoint' K g yz.1
      let x₂ := adjoint' K f yz.2
      x₁ + x₂ :=
by 
  unfold ProdL2.mk; ftrans



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.fst.arg_self.adjoint'_rule
  (f : X → Y×Z) (hf : SciLean.IsContinuousLinearMap K f)
  : adjoint' K (fun x => (f x).1)
    =
    (fun y => adjoint' K (Y:=Y×₂Z) f (y,(0:Z))) :=
by
  sorry


@[ftrans]
theorem SciLean.ProdL2.fst.arg_self.adjoint'_rule
  (f : X → Y×₂Z) (hf : SciLean.IsContinuousLinearMap K f)
  : adjoint' K (fun x => ProdL2.fst (f x))
    =
    (fun y => adjoint' K (Y:=Y×₂Z) f (y,(0:Z))) :=
by
  unfold ProdL2.fst; ftrans



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.snd.arg_self.adjoint'_rule
  (f : X → Y×Z) (hf : SciLean.IsContinuousLinearMap K f)
  : adjoint' K (fun x => (f x).2)
    =
    (fun z => adjoint' K (Y:=Y×₂Z) f ((0 :Y),z)) :=
by
  sorry


@[ftrans]
theorem SciLean.ProdL2.snd.arg_self.adjoint'_rule
  (f : X → Y×₂Z) (hf : SciLean.IsContinuousLinearMap K f)
  : adjoint' K (fun x => ProdL2.snd (f x))
    =
    (fun z => adjoint' K f ((0:Y),z)) :=
by
  unfold ProdL2.snd; ftrans



-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.adjoint'_rule
  (f g : X → Y) (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g)
  : adjoint' K (fun x => f x + g x)
    =
    fun y => 
      let x₁ := adjoint' K f y
      let x₂ := adjoint' K g y
      x₁ + x₂ := 
by
  sorry


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0a1.adjoint'_rule
  (f g : X → Y) (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g)
  : adjoint' K (fun x => f x - g x)
    =
    fun y => 
      let x₁ := adjoint' K f y
      let x₂ := adjoint' K g y
      x₁ - x₂ := 
by
  sorry


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.adjoint'_rule
  (f : X → Y) (hf : IsContinuousLinearMap K f)
  : adjoint' K (fun x => - f x)
    =
    fun y => - adjoint' K f y := 
by 
  sorry


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[ftrans]
theorem HMul.hMul.arg_a0.adjoint'_rule
  (c : K) (f : X → K) (hf : IsContinuousLinearMap K f)
  : adjoint' K (fun x => f x * c)
    =
    fun y => conj c • adjoint' K f y :=
by 
  sorry

open ComplexConjugate in
@[ftrans]
theorem HMul.hMul.arg_a1.adjoint'_rule
  (c : K) (f : X → K) (hf : IsContinuousLinearMap K f)
  : adjoint' K (fun x => c * f x)
    =
    fun y => conj c • adjoint' K f y :=
by 
  sorry


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[ftrans]
theorem HSMul.hSMul.arg_a0.adjoint'_rule
  (x' : X) (f : X → K) (hf : IsContinuousLinearMap K f)
  : adjoint' K (fun x => f x • x')
    =
    fun y => @inner K _ _ x' y • adjoint' K f 1 :=
by 
  sorry

open ComplexConjugate in
@[ftrans]
theorem HSMul.hSMul.arg_a1.adjoint'_rule
  (c : K) (g : X → Y) (hg : IsContinuousLinearMap K g)
  : adjoint' K (fun x => c • g x)
    =
    fun y => (conj c) • adjoint' K g y :=
by 
  sorry


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[ftrans]
theorem HDiv.hDiv.arg_a0.adjoint'_rule
  (f : X → K) (c : K)
  (hf : IsContinuousLinearMap K f)
  : adjoint' K (fun x => f x / c)
    =
    fun y => (conj c)⁻¹ • (fun x => f x)† y := 
by
  sorry


-- Finset.sum ------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open BigOperators in
@[ftrans]
theorem Finset.sum.arg_f.adjoint'_rule
  (f : X → ι → Y) (hf : ∀ i, IsContinuousLinearMap K fun x : X => f x i)
  : adjoint' K (fun x => ∑ i, f x i)
    =
    (fun y => ∑ i, adjoint' K (fun x => f x i) y) := 
by
  sorry


-- d/ite -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
theorem ite.arg_te.adjoint'_rule
  (c : Prop) [dec : Decidable c] (t e : X → Y) 
  : adjoint' K (fun x => if c then t x else e x)
    =
    fun y =>
      if c then adjoint' K t y else adjoint' K e y := 
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]


@[ftrans]
theorem dite.arg_te.adjoint'_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (e : ¬c → X → Y)
  : adjoint' K (fun x => if h : c then t h x else e h x)
    =
    fun y => if h : c then adjoint' K (t h) y else adjoint' K (e h) y := 
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]


-- Inner -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open ComplexConjugate in
@[ftrans]
theorem Inner.inner.arg_a0.adjoint'_rule
  (f : X → Y) (hf : IsContinuousLinearMap K f) (y : Y)
  : adjoint' K (fun x => @inner K _ _ (f x) y)
    =
    fun z => (conj z) • adjoint' K f y := 
by
  sorry

@[ftrans]
theorem Inner.inner.arg_a1.adjoint'_rule
  (f : X → Y) (hf : IsContinuousLinearMap K f) (y : Y)
  : adjoint' K (fun x => @inner K _ _ y (f x))
    =
    fun z => z • adjoint' K f y :=
by
  sorry


-- conj/starRingEnd ------------------------------------------------------------
-------------------------------------------------------------------------------- 
set_option linter.ftransDeclName false in
open ComplexConjugate in
@[ftrans]
theorem starRingEnd.arg_a0.adjoint'_rule
  (f : X → K) (hf : IsContinuousLinearMap K f)
  : adjoint' K (fun x => conj (f x))
    =
    fun z => adjoint' K f z :=
by
  sorry
