import SciLean.Core.FunctionProperties


namespace SciLean

--------------------------------------------------------------------------------
-- Core bootstrapping theorems
--------------------------------------------------------------------------------

instance IsLin_is_IsSmooth {X Y : Type} {Xs Y' : Type} [Vec Xs] [Vec Y'] 
  (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] [inst : IsLinN n f] 
  : IsSmoothN n f := IsSmoothN.mk (toIsSmoothNT:=⟨inst.proof.2⟩)



function_properties Neg.neg {X} [Vec X] (x : X) : X
argument x 
  isLin := sorry_proof,
  isSmooth,
  abbrev ∂,
  abbrev 𝒯

function_properties Neg.neg {X} [SemiHilbert X] (x : X) : X
argument x
  hasAdjoint := sorry_proof,
  abbrev † x' := x' by sorry_proof,
  hasAdjDiff,
  abbrev ∂†,
  abbrev ℛ
