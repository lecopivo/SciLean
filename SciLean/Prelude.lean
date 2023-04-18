import Lean
-- import SciLean.Data.Index
import SciLean.Data.EnumType
import SciLean.Notation

--- In this file we define bunch of conventions and conveniences through out the library

-- Export symbols from Mathlib
export SciLean.EnumType (sum)

@[inline]
def hold {α} (a : α) := a

abbrev typeOf {α} (_ : α) := α

instance : Fact (x=x) := ⟨by rfl⟩

instance instInhabitedSigma 
  {α : Type u} (β : α → Type v) [Inhabited α] [∀ a, Inhabited (β a)] 
  : Inhabited (Sigma β) := ⟨Sigma.mk default default⟩
instance instInhabitedFin [Fact (n≠0)] : Inhabited (Fin n) := ⟨⟨0, sorry⟩⟩
-- instance {ι : Type} [EnumType ι] [Nonempty ι] : Fact (numOf ι≠0) := sorry

--- !i creates an element of a subtype with an omitted proof
--- much nicer then writing ⟨i, sorry⟩
-- macro:max "!" noWs t:term : term => `(⟨$t, sorry⟩)

-- notation "!?" P => (sorry : P)

abbrev QuotientMk {α} [SA : Setoid α] (a : α) := Quotient.mk SA a
notation " ⟦ " x " ⟧ " => QuotientMk x

-- macro:max "#" noWs t:term : term => `(⟨$t, by first | decide | simp | native_decide⟩)

-- TODO: Add compiler flag to diplay proof 
axiom sorryProofAxiom {P : Prop} : P 
macro "sorry_proof" : term => do  `(sorryProofAxiom)
macro "sorry_proof" : tactic => `(tactic| apply sorry_proof)

-- class OTimes (α : Type u) (β : Type v) (γ : outParam $ Type w) where
--   otimes : α → β → γ

open Lean.Meta

-- register_simp_attr lambdaPush "Propagate Lambdas Inside"
-- register_simp_attr lambdaPull "Propagate Lambdas Outside"

-- register_simp_attr addPush "Propagate Add Inside"
-- register_simp_attr addPull "Propagate Add Outside"

-- initialize lambdaPush_simp_extension 
--   : SimpExtension ← registerSimpAttr `lambdaPush "Propagate Lambdas Inside"

-- initialize lambdaPull_simp_extension 
--   : SimpExtension ← registerSimpAttr `lambdaPull "Propagate Lambdas Outside"

-- initialize differentiation_simp_extension 
--   : SimpExtension ← registerSimpAttr `my_simp "my own simp attribute"

open Lean Elab Term Meta in
elab "reduce_type_of" t:term : term => do
  let val ← elabTerm t none
  let typ ← inferType val
  let reduced ← reduce typ (skipTypes := false)
  Expr.letE `x reduced (val) (Expr.bvar 0) false |> pure

open SciLean EnumType in
-- TOOD: move me
def find? {α ι} [EnumType ι] (p : α → Bool) (f : ι → α) : Option α := Id.run do
  for i in fullRange ι do
    let a := f i
    if p a then
      return some a
  return none

open SciLean EnumType in
-- TOOD: move me
def findIdx? {α ι} [EnumType ι] (p : α → Bool) (f : ι → α) : Option ι := Id.run do
  for i in fullRange ι do
    let a := f i
    if p a then
      return some i
  return none




-- @[inline]
-- def sort3 {α} (a b c : α) [LT α] [∀ x y : α, Decidable (x<y)] : α×α×α := Id.run do
--   let mut a' := a
--   let mut b' := b
--   let mut c' := c

--   if a > b then
--     a' := b
--     b' := a
--   else 
--     a' := a
--     b' := b
  
--   if b' > c then
--     c' := b'
--     if a' > c then
--       b' := a'
--       a' := c
--     else
--       b' := c
--   else
--     c' := c

--   (a',b',c')
  
 
