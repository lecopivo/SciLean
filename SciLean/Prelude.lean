import Lean
import SciLean.Mathlib.Data.Enumtype
import SciLean.Notation

--- In this file we define bunch of conventions and conveniences through out the library

-- Export symbols from Mathlib
export Enumtype (sum)

@[inline]
def hold {α} (a : α) := a

class Fact (P : Prop) : Prop where
  proof : P

instance : Fact (x=x) := ⟨by rfl⟩

instance [Fact (n≠0)] : Inhabited (Fin n) := ⟨⟨0, sorry⟩⟩
instance {ι : Type} [Enumtype ι] [Nonempty ι] : Fact (numOf ι≠0) := sorry


--- !i creates an element of a subtype with an omitted proof
--- much nicer then writing ⟨i, sorry⟩
macro:max "!" noWs t:term : term => `(⟨$t, sorry⟩)

notation "!?" P => (sorry : P)

abbrev QuotientMk {α} [SA : Setoid α] (a : α) := Quotient.mk SA a
notation " ⟦ " x " ⟧ " => QuotientMk x

macro:max "#" noWs t:term : term => `(⟨$t, by first | decide | simp | native_decide⟩)

-- TODO: Add compiler flag to diplay proof 
axiom sorryProofAxiom {P : Prop} : P 
macro "sorry_proof" : term => do  `(sorryProofAxiom)
macro "sorry_proof" : tactic => `(apply sorry_proof)

-- class OTimes (α : Type u) (β : Type v) (γ : outParam $ Type w) where
--   otimes : α → β → γ

open Lean.Meta

register_simp_attr lambdaPush "Propagate Lambdas Inside"
register_simp_attr lambdaPull "Propagate Lambdas Outside"

register_simp_attr addPush "Propagate Add Inside"
register_simp_attr addPull "Propagate Add Outside"

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
  let proof ← mkAppOptM ``rfl #[mkSort levelOne, reduced]
  mkAppOptM ``cast #[typ, reduced, proof, val]
