import SciLean

open SciLean

@[simp high]
axiom isomorphicType_equiv_zero
  : (IsomorphicType.equiv `RealToFloat) (0 : ℝ) = (0 : Float)

example
  : isomorph `RealToFloat (fun (p : Real × (Fin 2 → Real)) => Real.exp p.1 + p.2 0)
    =
    fun (p : Float × (Fin 2 → Float)) => Float.exp p.1 + p.2 0 :=
by
  conv => 
    lhs
    ftrans; ftrans


example
  : isomorph `RealToFloat (fun (p : Real × (Fin 2 → Real)) => Real.exp p.1 + p.2 0 ≤ 0 ∧ Real.exp p.1 + p.2 1 ≤ 0)
    =
    fun (p : Float × (Fin 2 → Float)) => Float.exp p.1 + p.2 0 ≤ 0 ∧ Float.exp p.1 + p.2 1 ≤ 0 :=
by
  conv => 
    lhs
    ftrans; ftrans
  
