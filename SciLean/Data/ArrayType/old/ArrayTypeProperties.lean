import SciLean.Data.ArrayType.ArrayType
import SciLean.Data.ArrayType.GenericArrayTypeProperties


namespace SciLean

variable {XI X I} [Index I] [ArrayType XI I X] -- [Inhabited X]
variable {YI Y} [Index I] [ArrayType YI I Y] -- [Inhabited X]


theorem adjointDifferential.rule_piMap {Y:Type} [SemiHilbert X] [SemiHilbert Y]
  (f : I → X → Y) [∀ i, HasAdjDiff (f i)]
  : ∂† (λ (g : X^I) (i : I) => f i g[i])
    =
    λ g dg' => ⊞ i, ∂† (f i) (g[i]) (dg' i)
  := sorry

theorem adjointDifferential.rule_piMapComp {J Y:Type} [SemiHilbert X] [SemiHilbert Y] [Index J] [Nonempty J]
  (f : J → XI → X → Y) [∀ i, HasAdjDiff (λ (g,x) => f i g x)]
  (h : J → I)
  : ∂† (λ (g : X^I) (j : J) => f j g g[h j])
    =
    λ g dg' => ⊞ i,
      let dg₁ := λ i' => ∂† (λ x => f (h⁻¹ i) g x) (g[i']) (dg' (h⁻¹ i'))
      let dg₂ := λ i' => (∂† (λ (g' : X^I) (j : J) => f j g' g[h j]) g dg')[i'] -- we are expecting to (array)beta reduce
      dg₁ i + dg₂ i
  := sorry

--------------------------------------------------------------------------------
-- introElem
--------------------------------------------------------------------------------

function_properties SciLean.introArrayElem
  {X I} {T : outParam Type} [Index I] [ArrayType T I X] [Vec X]
  (f : I → X)
argument f
  IsLin := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ df => ⊞ i, df i by sorry_proof,
  abbrev 𝒯 := λ df => (⊞ i, f i, ⊞ i, df i) by sorry_proof

function_properties SciLean.introArrayElem
  {X I} {T : outParam Type} [Index I] [ArrayType T I X] [SemiHilbert X]
  (f : I → X)
argument f
  HasAdjoint := sorry_proof,
  abbrev † := λ f' idx => f'[idx] by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ df' idx => df'[idx] by sorry_proof,
  abbrev ℛ := (⊞ i, f i, λ df' idx => df'[idx]) by sorry_proof
