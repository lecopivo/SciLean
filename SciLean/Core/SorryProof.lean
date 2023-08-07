namespace SciLean

axiom sorryProofAxiom2 {P : Prop} : P 

-- TODO: turn into elaborator and add option to trigger warning
macro "sorry_proof" : term => do  `(sorryProofAxiom2)
macro "sorry_proof" : tactic => `(tactic| apply sorry_proof)
