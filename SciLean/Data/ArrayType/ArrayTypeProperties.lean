import SciLean.Data.ArrayType.ArrayType
import SciLean.Data.ArrayType.Properties


namespace SciLean

variable {X I} {T : outParam Type} [Enumtype I] [ArrayType T I X] -- [Inhabited X]

--------------------------------------------------------------------------------
-- introElem 
--------------------------------------------------------------------------------

function_properties SciLean.introArrayElem 
  {X I} {T : outParam Type} [Enumtype I] [ArrayType T I X] [Vec X] 
  (f : I → X) 
argument f
  IsLin := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ df => ⊞ i, df i by sorry_proof,
  abbrev 𝒯 := λ df => (⊞ i, f i, ⊞ i, df i) by sorry_proof

function_properties SciLean.introArrayElem 
  {X I} {T : outParam Type} [Enumtype I] [ArrayType T I X] [SemiHilbert X] 
  (f : I → X) 
argument f
  HasAdjoint := sorry_proof,
  abbrev † := λ f' idx => f'[idx] by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ df' idx => df'[idx] by sorry_proof,
  abbrev ℛ := (⊞ i, f i, λ df' idx => df'[idx]) by sorry_proof
