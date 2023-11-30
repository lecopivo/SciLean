import SciLean.Core.FunctionPropositions.HasSemiAdjoint

import SciLean.Tactic.FTrans.Basic

set_option linter.unusedVariables false

namespace SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {ι : Type _} [EnumType ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]

namespace semiAdjoint

-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

variable (X)
theorem id_rule 
  : semiAdjoint K (fun (x : X) => x) = fun x => x := by sorry_proof

variable (Y)
theorem const_rule 
  : semiAdjoint K (fun (_ : X) => (0 : Y)) = fun x => 0 := 
by sorry_proof
variable {X Y}

variable (E)
theorem proj_rule [DecidableEq ι]
   (i : ι) 
  : semiAdjoint K (fun (f : (i:ι) → E i) => f i)
    = 
    fun y => (fun j => if h : i=j then h▸y else 0)
  := sorry_proof
variable {E}

theorem comp_rule 
  (f : Y → Z) (g : X → Y) 
  (hf : HasSemiAdjoint K f) (hg : HasSemiAdjoint K g)
  : semiAdjoint K (fun x => f (g x))
    =
    fun z =>
      let y := semiAdjoint K f z
      let x := semiAdjoint K g y
      x := 
by sorry_proof

theorem let_rule 
  (f : X → Y → Z) (g : X → Y)      
  (hf : HasSemiAdjoint K (fun xy : X×Y => f xy.1 xy.2)) (hg : HasSemiAdjoint K g)
  : semiAdjoint K (fun x => let y := g x; f x y)
    =
    fun z =>
      let xy := semiAdjoint K (fun xy : X×Y => f xy.1 xy.2) z
      let x' := semiAdjoint K g xy.2
      xy.1 + x' := 
by sorry_proof

theorem pi_rule
  (f : X → (i : ι) → E i) (hf : ∀ i, HasSemiAdjoint K (f · i))
  : semiAdjoint K (fun (x : X) (i : ι) => f x i)
    = 
    (fun x' => ∑ i, semiAdjoint K (fun x => f x i) (x' i))
  := sorry_proof



-- Register `adjoint` as function transformation -------------------------------
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
  ftransName := ``semiAdjoint

  getFTransFun? e := 
    if e.isAppOf ``semiAdjoint then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``semiAdjoint then
      e.setArg 6 f
    else          
      e

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
    tryTheorems
      #[ { proof := ← mkAppM ``proj_rule #[K, X, i], origin := .decl ``proj_rule, rfl := false} ]
      discharger e

  compRule e f g := do
    let K := e.getArg! 0
    tryTheorems
      #[ { proof := ← withTransparency .all <| 
             mkAppM ``comp_rule #[K, f, g], origin := .decl ``comp_rule, rfl := false} ]
      discharger e

  letRule e f g := do
    let K := e.getArg! 0
    tryTheorems
      #[ { proof := ← mkAppM ``let_rule #[K, f, g], origin := .decl ``let_rule, rfl := false} ]
      discharger e

  piRule  e f := do
    let K := e.getArg! 0
    tryTheorems
      #[ { proof := ← mkAppM ``pi_rule #[K, f], origin := .decl ``pi_rule, rfl := false} ]
      discharger e

  discharger := discharger


-- register adjoint
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``semiAdjoint, ftransExt))

end SciLean.semiAdjoint

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]
  {ι : Type _} [EnumType ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]

open SciLean


-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.mk.arg_fstsnd.semiAdjoint_rule
  (g : X → Y) (f : X → Z) 
  (hg : HasSemiAdjoint K g) (hf : HasSemiAdjoint K f)
  : semiAdjoint K (fun x => (g x, f x))
    =
    fun yz =>
      let x₁ := semiAdjoint K g yz.1
      let x₂ := semiAdjoint K f yz.2
      x₁ + x₂ :=
by sorry_proof


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.fst.arg_self.semiAdjoint_rule
  (f : X → Y×Z) (hf : SciLean.HasSemiAdjoint K f)
  : semiAdjoint K (fun x => (f x).1)
    =
    (fun y => semiAdjoint K (fun x => f x) (y,0)) :=
by
  sorry_proof


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.snd.arg_self.semiAdjoint_rule
  (f : X → Y×Z) (hf : SciLean.HasSemiAdjoint K f)
  : semiAdjoint K (fun x => (f x).2)
    =
    (fun z => semiAdjoint K f (0,z)) :=
by
  sorry_proof


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.semiAdjoint_rule
  (f g : X → Y) (hf : HasSemiAdjoint K f) (hg : HasSemiAdjoint K g)
  : semiAdjoint K (fun x => f x + g x)
    =
    fun y => 
      let x₁ := semiAdjoint K f y
      let x₂ := semiAdjoint K g y
      x₁ + x₂ := 
by
  sorry_proof


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0a1.semiAdjoint_rule
  (f g : X → Y) (hf : HasSemiAdjoint K f) (hg : HasSemiAdjoint K g)
  : semiAdjoint K (fun x => f x - g x)
    =
    fun y => 
      let x₁ := semiAdjoint K f y
      let x₂ := semiAdjoint K g y
      x₁ - x₂ := 
by sorry_proof


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.semiAdjoint_rule
  (f : X → Y)
  : semiAdjoint K (fun x => - f x)
    =
    fun y => - semiAdjoint K f y := 
by 
  sorry_proof


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[ftrans]
theorem HMul.hMul.arg_a0.semiAdjoint_rule
  (c : K) (f : X → K) (hf : HasSemiAdjoint K f)
  : semiAdjoint K (fun x => f x * c)
    =
    fun y => conj c • semiAdjoint K (fun x => f x) y :=
by 
  sorry_proof

open ComplexConjugate in
@[ftrans]
theorem HMul.hMul.arg_a1.semiAdjoint_rule
  (c : K) (f : X → K) (hf : HasSemiAdjoint K f)
  : semiAdjoint K (fun x => c * f x)
    =
    fun y => conj c • semiAdjoint K (fun x => f x) y :=
by sorry_proof


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[ftrans]
theorem HSMul.hSMul.arg_a0.semiAdjoint_rule
  {Y : Type _} [SemiHilbert K Y]
  (y' : Y) (f : X → K) (hf : HasSemiAdjoint K f)
  : semiAdjoint K (fun x => f x • y')
    =
    fun y => semiAdjoint K (fun x => f x) ⟪y',y⟫[K] :=
by 
  sorry_proof

open ComplexConjugate in
@[ftrans]
theorem HSMul.hSMul.arg_a1.semiAdjoint_rule
  (c : K) (g : X → Y) (hg : HasSemiAdjoint K g)
  : semiAdjoint K (fun x => c • g x)
    =
    fun y => (conj c) • semiAdjoint K g y :=
by sorry_proof


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[ftrans]
theorem HDiv.hDiv.arg_a0.semiAdjoint_rule
  (f : X → K) (c : K)
  (hf : HasSemiAdjoint K f)
  : semiAdjoint K (fun x => f x / c)
    =
    fun y => (conj c)⁻¹ • semiAdjoint K f y := 
by
  sorry_proof


-- Finset.sum ------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open BigOperators in
@[ftrans]
theorem Finset.sum.arg_f.semiAdjoint_rule {ι : Type _} [Fintype ι]
  (f : X → ι → Y) (hf : ∀ i, HasSemiAdjoint K (f · i))
  : semiAdjoint K (fun x => ∑ i, f x i)
    =
    (fun y => ∑ i, semiAdjoint K (f · i) y) := 
by
  sorry_proof


-- EnumType.sum ------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
theorem SciLean.EnumType.sum.arg_f.semiAdjoint_rule
  (f : X → ι → Y) (hf : ∀ i, HasSemiAdjoint K (f · i))
  : semiAdjoint K (fun x => ∑ i, f x i)
    =
    (fun y => ∑ i, semiAdjoint K (f · i) y) := 
by
  sorry_proof


-- d/ite -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
theorem ite.arg_te.semiAdjoint_rule
  (c : Prop) [dec : Decidable c] (t e : X → Y)
  : semiAdjoint K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (semiAdjoint K t y) (semiAdjoint K e y) := 
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]

@[ftrans]
theorem dite.arg_te.semiAdjoint_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (e : ¬c → X → Y)
  : semiAdjoint K (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => semiAdjoint K (t p) y) 
             (fun p => semiAdjoint K (e p) y) := 
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]


-- Inner -----------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[ftrans]
theorem Inner.inner.arg_a0.semiAdjoint_rule 
  {Y : Type _} [SemiHilbert K Y]
  (f : X → Y) (hf : HasSemiAdjoint K f) (y : Y)
  : semiAdjoint K (fun x => ⟪f x, y⟫[K])
    =
    fun z => (conj z) • semiAdjoint K f y :=
by sorry_proof

@[ftrans]
theorem Inner.inner.arg_a1.semiAdjoint_rule
  {Y : Type _} [SemiHilbert K Y]
  (f : X → Y) (hf : HasSemiAdjoint K f) (y : Y)
  : semiAdjoint K (fun x => ⟪y, f x⟫[K])
    =
    fun z => z • semiAdjoint K f y :=
by sorry_proof


-- conj/starRingEnd ------------------------------------------------------------ 
-------------------------------------------------------------------------------- 
set_option linter.ftransDeclName false in
open ComplexConjugate in
@[ftrans]
theorem starRingEnd.arg_a0.semiAdjoint_rule
  (f : X → K)
  : semiAdjoint K (fun x => conj (f x))
    =
    fun z => semiAdjoint K f z :=
by sorry_proof


-- semiAdjoint -----------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem SciLean.semiAdjoint.arg_y.semiAdjoint_rule
  (f : X → Y) (a3 : W → Y) (hf : HasSemiAdjoint K f) (ha3 : HasSemiAdjoint K a3)
  : semiAdjoint K (fun w => semiAdjoint K f (a3 w)) 
    =
    fun x => 
      let y := f x
      semiAdjoint K a3 y :=
by
  sorry_proof

