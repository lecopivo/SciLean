import SciLean.Core.FunctionPropositions.IsLinearMap
import SciLean.Core.FunctionPropositions.IsDifferentiable

set_option linter.unusedVariables false

namespace SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [EnumType ι] 
  {E : ι → Type _} [∀ i, Vec K (E i)] 

def IsSmoothLinearMap (f : X → Y) : Prop :=
  IsLinearMap K f ∧ IsDifferentiable K f


--------------------------------------------------------------------------------

namespace IsSmoothLinearMap

variable (X)
theorem id_rule
  : IsSmoothLinearMap K (fun x : X => x) := by constructor <;> fprop
  
variable (Y)
theorem const_zero_rule 
  : IsSmoothLinearMap K (fun _ : X => (0 : Y))
  := by constructor <;> fprop
variable {Y}

theorem proj_rule (i : ι)
  : IsSmoothLinearMap K (fun (x : (i : ι) → E i) => x i)
  := by constructor <;> fprop
variable {X}

theorem comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : IsSmoothLinearMap K f) (hg : IsSmoothLinearMap K g)
  : IsSmoothLinearMap K (fun x => f (g x)) := 
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor <;> fprop

theorem let_rule
  (f : X → Y → Z) (g : X → Y)
  (hf : IsSmoothLinearMap K (fun (x,y) => f x y)) (hg : IsSmoothLinearMap K g)
  : IsSmoothLinearMap K (fun x => f x (g x)) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor <;> fprop


theorem pi_rule
  (f : X → (i : ι) → E i) (hf : ∀ i, IsSmoothLinearMap K (f · i))
  : IsSmoothLinearMap K fun x i => f x i := 
by
  have := fun i => (hf i).1
  have := fun i => (hf i).2
  constructor <;> fprop


--------------------------------------------------------------------------------
-- Register IsSmoothLinearMap --------------------------------------------------------
--------------------------------------------------------------------------------

open Lean Meta SciLean FProp
def fpropExt : FPropExt where
  fpropName := ``IsSmoothLinearMap
  getFPropFun? e := 
    if e.isAppOf ``IsSmoothLinearMap then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``IsSmoothLinearMap then
      e.setArg 6  f
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
      proof  := mkConst ``proj_rule 
      origin := .decl ``proj_rule 
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
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``IsSmoothLinearMap, fpropExt))


end SciLean.IsSmoothLinearMap

--------------------------------------------------------------------------------

open SciLean

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [EnumType ι] 
  {E : ι → Type _} [∀ i, Vec K (E i)] 


-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fprop]
theorem id.arg_a.IsSmoothLinearMap_rule
  : IsSmoothLinearMap K (fun x : X => id x) := 
by
  constructor <;> fprop
 
-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.mk.arg_fstsnd.IsSmoothLinearMap_rule
  (f : X → Z) (g : X → Y) 
  (hf : IsSmoothLinearMap K f) (hg : IsSmoothLinearMap K g)
  : IsSmoothLinearMap K fun x => (g x, f x) := 
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor <;> fprop


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.fst.arg_self.IsSmoothLinearMap_rule
  (f : X → Y×Z) (hf : IsSmoothLinearMap K f)
  : IsSmoothLinearMap K fun (x : X) => (f x).fst := 
by
  have ⟨_,_⟩ := hf
  constructor <;> fprop


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.snd.arg_self.IsSmoothLinearMap_rule
  (f : X → Y×Z) (hf : IsSmoothLinearMap K f)
  : IsSmoothLinearMap K fun (x : X) => (f x).snd := 
by
  have ⟨_,_⟩ := hf
  constructor <;> fprop


-- Neg.neg ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem Neg.neg.arg_a0.IsSmoothLinearMap_rule 
  (f : X → Y) (hf : IsSmoothLinearMap K f)
  : IsSmoothLinearMap K fun x => - f x := 
by
  have ⟨_,_⟩ := hf
  constructor <;> fprop


-- HAdd.hAdd -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem HAdd.hAdd.arg_a0a1.IsSmoothLinearMap_rule
  (f g : X → Y) (hf : IsSmoothLinearMap K f) (hg : IsSmoothLinearMap K g)
  : IsSmoothLinearMap K fun x => f x + g x :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor <;> fprop



-- HSub.hSub -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem HSub.hSub.arg_a0a1.IsSmoothLinearMap_rule 
  (f g : X → Y) (hf : IsSmoothLinearMap K f) (hg : IsSmoothLinearMap K g)
  : IsSmoothLinearMap K fun x => f x - g x :=
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor <;> fprop


-- -- HMul.hMul ---------------------------------------------------------------------
-- -------------------------------------------------------------------------------- 

-- @[fprop]
-- theorem HMul.hMul.arg_a0.IsSmoothLinearMap_rule
--   (f : X → Y) (hf : IsSmoothLinearMap K f)
--   (y' : Y) 
--   : IsSmoothLinearMap K fun x => f x * y'
-- := 
--   by_morphism (ContinuousLinearMap.comp (ContinuousLinearMap.mul_right y') (mk' K f hf))
--   (by simp[ContinuousLinearMap.mul_right])


-- @[fprop]
-- theorem HMul.hMul.arg_a1.IsSmoothLinearMap_rule
--   {R : Type _} [CommSemiring R] 
--   {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module K X]
--   {Y : Type _} [TopologicalSpace Y] [Semiring Y] [Algebra K Y] [TopologicalSemiring Y] 
--   (f : X → Y) (hf : IsSmoothLinearMap K f)
--   (y' : Y) 
--   : IsSmoothLinearMap K fun x => y' * f x
-- := 
--   by_morphism (ContinuousLinearMap.comp (ContinuousLinearMap.mul_left y') (mk' K f hf))
--   (by simp[ContinuousLinearMap.mul_left])


-- Smul.smul ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem HSMul.hSMul.arg_a0.IsSmoothLinearMap_rule
  (f : X → K) (y : Y) (hf : IsSmoothLinearMap K f)
  : IsSmoothLinearMap K fun x => f x • y :=
by 
  have ⟨_,_⟩ := hf
  constructor <;> fprop

@[fprop]
theorem HSMul.hSMul.arg_a1.IsSmoothLinearMap_rule 
  (c : K) (f : X → Y) (hf : IsSmoothLinearMap K f)
  : IsSmoothLinearMap K fun x => c • f x :=
by
  have ⟨_,_⟩ := hf
  constructor <;> fprop

@[fprop]
theorem HSMul.hSMul.arg_a1.IsSmoothLinearMap_rule_nat
  (c : ℕ) (f : X → Y) (hf : IsSmoothLinearMap K f)
  : IsSmoothLinearMap K fun x => c • f x :=
by
  have ⟨_,_⟩ := hf
  constructor <;> fprop

@[fprop]
theorem HSMul.hSMul.arg_a1.IsSmoothLinearMap_rule_int
  (c : ℤ) (f : X → Y) (hf : IsSmoothLinearMap K f)
  : IsSmoothLinearMap K fun x => c • f x :=
by
  have ⟨_,_⟩ := hf
  constructor <;> fprop


-- d/ite -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem ite.arg_te.IsSmoothLinearMap_rule
  (c : Prop) [dec : Decidable c]
  (t e : X → Y) (ht : IsSmoothLinearMap K t) (he : IsSmoothLinearMap K e)
  : IsSmoothLinearMap K fun x => ite c (t x) (e x) := 
by
  induction dec
  case isTrue h  => simp[h]; fprop
  case isFalse h => simp[h]; fprop


@[fprop]
theorem dite.arg_te.IsSmoothLinearMap_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (ht : ∀ p, IsSmoothLinearMap K (t p)) 
  (e : ¬c → X → Y) (he : ∀ p, IsSmoothLinearMap K (e p))
  : IsSmoothLinearMap K fun x => dite c (t · x) (e · x) := 
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
theorem Basis.proj.arg_x.IsSmoothLinearMap_rule (i : IX)
  : IsSmoothLinearMap K (fun x : X => ℼ i x) := by constructor <;> fprop

@[fprop]
theorem DualBasis.dualProj.arg_x.IsSmoothLinearMap_rule (i : IX)
  : IsSmoothLinearMap K (fun x : X => ℼ' i x) := by constructor <;> fprop

@[fprop]
theorem BasisDuality.toDual.arg_x.IsSmoothLinearMap_rule
  : IsSmoothLinearMap K (fun x : X => BasisDuality.toDual x) := by constructor <;> fprop

@[fprop]
theorem BasisDuality.fromDual.arg_x.IsSmoothLinearMap_rule
  : IsSmoothLinearMap K (fun x : X => BasisDuality.fromDual x) := by constructor <;> fprop

end OnFinVec
end SciLean
