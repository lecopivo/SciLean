import Mathlib.Algebra.Module.LinearMap
import Mathlib.Algebra.Module.Prod
import SciLean.Core.Objects.FinVec

import SciLean.Tactic.FProp.Basic
import SciLean.Tactic.FProp.Notation

set_option linter.unusedVariables false

variable {R X Y Z ι : Type _} {E : ι → Type _}
  [Semiring R] 
  [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]  
  [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]


--------------------------------------------------------------------------------

namespace IsLinearMap

variable (X R)
theorem id_rule
  : IsLinearMap R (fun x : X => x) := by sorry_proof
  
variable (Y)
theorem const_zero_rule 
  : IsLinearMap R (fun _ : X => (0 : Y))
  := by sorry_proof
variable {Y}

theorem proj_rule (i : ι)
  : IsLinearMap R (fun (x : (i : ι) → E i) => x i)
  := by sorry_proof
variable {X}

theorem comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : IsLinearMap R f) (hg : IsLinearMap R g)
  : IsLinearMap R (fun x => f (g x)) := by sorry_proof

theorem let_rule
  (f : X → Y → Z) (g : X → Y)
  (hf : IsLinearMap R (fun (x,y) => f x y)) (hg : IsLinearMap R g)
  : IsLinearMap R (fun x => f x (g x)) := by sorry_proof


theorem pi_rule
  (f : X → (i : ι) → E i) (hf : ∀ i, IsLinearMap R (f · i))
  : IsLinearMap R fun x i => f x i := by sorry_proof


--------------------------------------------------------------------------------
-- Register IsLinearMap --------------------------------------------------------
--------------------------------------------------------------------------------

open Lean Meta SciLean FProp
def fpropExt : FPropExt where
  fpropName := ``IsLinearMap
  getFPropFun? e := 
    if e.isAppOf ``IsLinearMap then

      if let .some f := e.getArg? 8 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``IsLinearMap then
      e.setArg 8  f
    else          
      e

  identityRule    e := do
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``id_rule
      origin := .decl ``id_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  constantRule    e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``const_zero_rule
      origin := .decl ``const_zero_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  projRule e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``IsLinearMap.proj_rule 
      origin := .decl ``IsLinearMap.proj_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  compRule e f g := do
    let .some K := e.getArg? 0 | return none

    let thm : SimpTheorem :=
    {
      proof  := ← mkAppM ``comp_rule #[K,f,g]
      origin := .decl ``comp_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  lambdaLetRule e f g := do
    let .some K := e.getArg? 0 | return none

    let thm : SimpTheorem :=
    {
      proof  := ← mkAppM ``let_rule #[K,f,g]
      origin := .decl ``let_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  lambdaLambdaRule e _ :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``pi_rule 
      origin := .decl ``pi_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  discharger e := 
    FProp.tacticToDischarge (Syntax.mkLit ``Lean.Parser.Tactic.assumption "assumption") e


-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``IsLinearMap, fpropExt))


end IsLinearMap


variable {R X Y Z ι : Type _} {E : ι → Type _}
  [Semiring R] 
  [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]  
  [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]



-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fprop]
theorem id.arg_a.IsLinearMap_rule
  : IsLinearMap R (fun x : X => id x) := 
by
  sorry_proof
 
-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.mk.arg_fstsnd.IsLinearMap_rule
  (f : X → Z) (g : X → Y) 
  (hf : IsLinearMap R f) (hg : IsLinearMap R g)
  : IsLinearMap R fun x => (g x, f x) := 
by
  sorry_proof


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.fst.arg_self.IsLinearMap_rule
  (f : X → Y×Z) (hf : IsLinearMap R f)
  : IsLinearMap R fun (x : X) => (f x).fst := 
by
  sorry_proof


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.snd.arg_self.IsLinearMap_rule
  (f : X → Y×Z) (hf : IsLinearMap R f)
  : IsLinearMap R fun (x : X) => (f x).snd := 
by
  sorry_proof


-- Neg.neg ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem Neg.neg.arg_a0.IsLinearMap_rule 
  (f : X → Y) (hf : IsLinearMap R f)
  : IsLinearMap R fun x => - f x := 
by
  sorry_proof


-- HAdd.hAdd -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem HAdd.hAdd.arg_a0a1.IsLinearMap_rule
  (f g : X → Y) (hf : IsLinearMap R f) (hg : IsLinearMap R g)
  : IsLinearMap R fun x => f x + g x :=
by 
  sorry_proof



-- HSub.hSub -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem HSub.hSub.arg_a0a1.IsLinearMap_rule 
  (f g : X → Y) (hf : IsLinearMap R f) (hg : IsLinearMap R g)
  : IsLinearMap R fun x => f x - g x :=
by
  sorry_proof


-- HMul.hMul ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem HMul.hMul.arg_a0.IsLinearMap_rule
  (f : X → R) (hf : IsLinearMap R f)
  (y' : R) 
  : IsLinearMap R fun x => f x * y' := 
by
  sorry_proof


@[fprop]
theorem HMul.hMul.arg_a1.IsLinearMap_rule
  (f : X → R) (hf : IsLinearMap R f)
  (y' : R) 
  : IsLinearMap R fun x => y' * f x := 
by  
  sorry_proof


-- Smul.smul ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem HSMul.hSMul.arg_a0.IsLinearMap_rule
  (f : X → R) (y : Y) (hf : IsLinearMap R f)
  : IsLinearMap R fun x => f x • y :=
by 
  sorry_proof

@[fprop]
theorem HSMul.hSMul.arg_a1.IsLinearMap_rule 
  (c : R) (f : X → Y) (hf : IsLinearMap R f)
  : IsLinearMap R fun x => c • f x :=
by
  sorry_proof

@[fprop]
theorem HSMul.hSMul.arg_a1.IsLinearMap_rule_nat
  (c : ℕ) (f : X → Y) (hf : IsLinearMap R f)
  : IsLinearMap R fun x => c • f x :=
by
  sorry_proof

@[fprop]
theorem HSMul.hSMul.arg_a1.IsLinearMap_rule_int
  (c : ℤ) (f : X → Y) (hf : IsLinearMap R f)
  : IsLinearMap R fun x => c • f x :=
by
  sorry_proof


-- d/ite -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem ite.arg_te.IsLinearMap_rule
  (c : Prop) [dec : Decidable c]
  (t e : X → Y) (ht : IsLinearMap R t) (he : IsLinearMap R e)
  : IsLinearMap R fun x => ite c (t x) (e x) := 
by
  induction dec
  case isTrue h  => simp[h]; fprop
  case isFalse h => simp[h]; fprop


@[fprop]
theorem dite.arg_te.IsLinearMap_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (ht : ∀ p, IsLinearMap R (t p)) 
  (e : ¬c → X → Y) (he : ∀ p, IsLinearMap R (e p))
  : IsLinearMap R fun x => dite c (t · x) (e · x) := 
by
  induction dec
  case isTrue h  => simp[h]; apply ht
  case isFalse h => simp[h]; apply he


namespace SciLean
section OnFinVec 


variable 
  {K : Type _} [IsROrC K]
  {IX : Type} [EnumType IX] {X : Type _} [FinVec IX K X]
  {IY : Type} [EnumType IY] {Y : Type _} [FinVec IY K Y]
  {IZ : Type} [EnumType IZ] {Z : Type _} [FinVec IZ K Z]

@[fprop]
theorem Basis.proj.arg_x.IsLinearMap_rule (i : IX)
  : IsLinearMap K (fun x : X => ℼ i x) := by sorry_proof

@[fprop]
theorem DualBasis.dualProj.arg_x.IsLinearMap_rule (i : IX)
  : IsLinearMap K (fun x : X => ℼ' i x) := by sorry_proof

@[fprop]
theorem BasisDuality.toDual.arg_x.IsLinearMap_rule
  : IsLinearMap K (fun x : X => BasisDuality.toDual x) := by sorry_proof

@[fprop]
theorem BasisDuality.fromDual.arg_x.IsLinearMap_rule
  : IsLinearMap K (fun x : X => BasisDuality.fromDual x) := by sorry_proof

end OnFinVec
end SciLean
