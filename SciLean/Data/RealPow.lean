import SciLean.Mathlib.Data.PowType
import SciLean.Categories
import SciLean.Data.Table

namespace SciLean


instance (n : Nat) : PowType ℝ n := 
{
  powType := {a : FloatArray // a.size = n}
  intro := λ f => Id.run do
    let mut x := FloatArray.mkEmpty n
    for i in [0:n] do
      let i := ⟨i, sorry⟩
      x := x.push (f i)
    ⟨x, sorry⟩
  get := λ x i => x.1.get ⟨i.1, sorry⟩
  set := λ x i xi => ⟨x.1.set ⟨i.1, sorry⟩ xi, sorry⟩
  ext := sorry
}

def u : (ℝ^(2 : Nat)) := ^[-2.0,2.0]

#eval u[(1 : Fin 2)]
#eval (u + u : ℝ^(2 : Nat))
#eval 2*⟪u, u⟫


open Table Trait
example : Table.Trait (ℝ^(2 : Nat)) := by infer_instance
example : Table (ℝ^(2 : Nat)) (Index (ℝ^(2 : Nat))) (Value (ℝ^(2 : Nat))) := by infer_instance
example : Enumtype (Index (ℝ^(2 : Nat))) := by infer_instance
example : SemiInner (Value (ℝ^(2 : Nat))) ℝ Unit (λ r _ => r) := by infer_instance
example : SemiInner (ℝ^(2 : Nat)) ℝ Unit (λ r _ => r) := by infer_instance
example : SemiInner.Trait (ℝ^(2 : Nat)) := by infer_instance

