import SciLean.Core.Mor
import SciLean.Core.Fun
import SciLean.Core.Functions

namespace SciLean

  abbrev LinMap (X Y : Type) [Vec X] [Vec Y] := (f : X → Y) ×' (IsLin f)

  infixr:25 " ⊸ " => LinMap

  variable {X Y} [Vec X] [Vec Y]

  variable (f : X → Y) [IsLin f]
  variable (g : X → Y) [IsLin g]
  variable (r : ℝ)

  instance : IsLin (-f)    := by (conv => enter [1,x]); simp; infer_instance done
  instance : IsLin (f + g) := by (conv => enter [1,x]); simp; infer_instance done
  instance : IsLin (f - g) := by (conv => enter [1,x]); simp; infer_instance done
  instance : IsLin (r * f) := by (conv => enter [1,x]); simp; infer_instance done
  instance : IsLin (0 : X → Y) :=  by (conv => enter [1,x]); simp; infer_instance done

  instance : Neg (X⊸Y) := ⟨λ f   => ⟨-f.1, by have hf := f.2; infer_instance⟩⟩
  instance : Add (X⊸Y) := ⟨λ f g => ⟨f.1 + g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
  instance : Sub (X⊸Y) := ⟨λ f g => ⟨f.1 + g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
  instance : Mul (X⊸ℝ) := ⟨λ f g => ⟨f.1 + g.1, by have hf := f.2; have hg := g.2; infer_instance⟩⟩
  instance : HMul ℝ (X⊸Y) (X⊸Y) := ⟨λ r f => ⟨r * f.1, by have hf := f.2; infer_instance⟩⟩
 
  instance : Zero (X ⊸ Y) := ⟨⟨0, by (conv => enter [1,x]); simp; infer_instance done⟩⟩

  instance : AddSemigroup (X ⊸ Y) := AddSemigroup.mk sorry
  instance : AddMonoid (X ⊸ Y)    := AddMonoid.mk sorry sorry nsmul_rec sorry sorry
  instance : SubNegMonoid (X ⊸ Y) := SubNegMonoid.mk sorry gsmul_rec sorry sorry sorry
  instance : AddGroup (X ⊸ Y)     := AddGroup.mk sorry
  instance : AddCommGroup (X ⊸ Y) := AddCommGroup.mk sorry

  instance : MulAction ℝ (X ⊸ Y) := MulAction.mk sorry sorry
  instance : DistribMulAction ℝ (X ⊸ Y) := DistribMulAction.mk sorry sorry
  instance : Module ℝ (X ⊸ Y) := Module.mk sorry sorry

  instance : Vec (X ⊸ Y) := Vec.mk

  instance : CoeFun (X⊸Y) (λ _ => X→Y) := ⟨λ f => f.1⟩

