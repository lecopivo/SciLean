namespace SciLean

axiom sorryProofAxiom {P : Prop} : P 
macro "sorry_proof" : term => do  `(sorryProofAxiom)
macro "sorry_proof" : tactic => `(tactic| apply sorry_proof)


axiom sorryDataAxiom {α : Type _} : α
macro "sorry_data" : term => do  `(sorryDataAxiom)
macro "sorry_data" : tactic => `(tactic| apply sorry_data)
