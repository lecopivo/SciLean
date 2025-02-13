import SciLean.Data.DataArray

open SciLean


/-- info: ⊞[4.000000, 5.000000, 6.000000] -/
#guard_msgs in
#eval ⊞[1.0,2.0,3.0;4,5,6].curry[⟨1,sorry_proof⟩]


/-- info: ⊞[⊞[0.000000, 100.000000, 200.000000], ⊞[1.000000, 101.000000, 201.000000]] -/
#guard_msgs in
#eval ⊞ (i : Fin 2) => ⊞ (j : Fin 3) => (i.1+j.1*100).toFloat
