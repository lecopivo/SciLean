namespace SciLean

axiom sorryProofAxiom {P : Prop} : P

/-- Same as `sorry` but makes sure that the term is of type `Prop`.

`sorry_proof` is very useful when writing programs such that you do not accidantelly add `sorry`
which would prevent compiler generating executable code. -/
macro "sorry_proof" : term => do  `(sorryProofAxiom)

/-- Same as `sorry` but makes sure that the term is of type `Prop`.

`sorry_proof` is very useful when writing programs such that you do not accidantelly add `sorry`
which would prevent compiler generating executable code. -/
macro "sorry_proof" : tactic => `(tactic| apply sorry_proof)


axiom sorryDataAxiom {α : Type _} : α
/-- Same as `sorry` but makes sure that the term is of type `Type _` -/
macro "sorry_data" : term => do  `(sorryDataAxiom)
/-- Same as `sorry` but makes sure that the term is of type `Type _` -/
macro "sorry_data" : tactic => `(tactic| apply sorry_data)
