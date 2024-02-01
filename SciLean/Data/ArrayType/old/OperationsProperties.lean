-- import SciLean.Data.ArrayType.Notation
import SciLean.Data.ArrayType.GenericArrayTypeProperties

namespace SciLean
namespace GenericArrayType
section LinearGenericArrayType

variable {Cont : USize → Type} {Elem : Type |> outParam}
variable [LinearGenericArrayType Cont Elem]

------------------------------------------------------------------------------
-- dropElem
--------------------------------------------------------------------------------

function_properties SciLean.DropElem.dropElem
  {Cont : Nat → Type} {Elem : Type |> outParam} [LinearGenericArrayType Cont Elem] Vec Elem]
  {n : Nat} (k : Nat) (cont : Cont (n+k))
argument cont
  IsLin := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dcont => dropElem k dcont by sorry_proof,
  abbrev 𝒯 := λ dcont => (dropElem k cont, dropElem k dcont) by sorry_proof

function_properties SciLean.DropElem.dropElem
  {Cont : Nat → Type} {Elem : Type |> outParam} [LinearGenericArrayType Cont Elem] SemiHilbert Elem]
  {n : Nat} (k : Nat) (cont : Cont (n+k))
argument cont
  HasAdjoint := sorry_proof,
  abbrev † := λ cont' => pushElem k 0 cont' by sorry_proof,
  HasAdjDiff := by sorry_proof,
  abbrev ∂† := λ dcont' => pushElem k 0 dcont' by sorry_proof,
  abbrev ℛ := (dropElem k cont, λ dcont' => pushElem k 0 dcont') by sorry_proof


--------------------------------------------------------------------------------
-- pushElem
--------------------------------------------------------------------------------

function_properties SciLean.PushElem.pushElem
  {Cont : Nat → Type} {Elem : Type |> outParam} [LinearGenericArrayType Cont Elem] Vec Elem]
  {n : Nat} (k : Nat) (elem : Elem) (cont : Cont n)
argument (elem, cont)
  IsLin := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ delem dcont => pushElem k delem dcont by sorry_proof,
  abbrev 𝒯 := λ delem dcont => (pushElem k elem cont, pushElem k delem dcont) by sory_proof
argument cont
  IsLin [Fact (elem=0)] := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dcont => pushElem k 0 dcont by sorry_proof,
  abbrev 𝒯 := λ dcont => (pushElem k elem cont, pushElem k 0 dcont) by sorry_proof
argument elem
  IsLin [Fact (cont=0)] := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ delem => pushElem k delem 0 by sorry_proof,
  abbrev 𝒯 := λ delem => (pushElem k elem cont, pushElem k delem 0) by sorry_proof

function_properties SciLean.PushElem.pushElem
  {Cont : Nat → Type} {Elem : Type |> outParam} [LinearGenericArrayType Cont Elem] SemiHilbert Elem]
  {n : Nat} (k : Nat) (elem : Elem) (cont : Cont n)
argument (elem, cont)
  HasAdjoint := sorry_proof,
  abbrev † := λ elemcont' => (∑ i : Fin k, elemcont'[⟨n+i.1, sorry_proof⟩], dropEle k elemcont') by sorry_proof,
  HasAdjDiff := sorry,
  abbrev ∂† := λ delemcont' => (∑ i : Fin k, delemcont'[⟨n+i.1, sorry_proof⟩], droplem k delemcont') by sorry_proof
argument cont
  HasAdjoint [Fact (elem=0)] := sorry_proof,
  abbrev † [Fact (elem=0)] := λ cont' => dropElem k cont' by sorry_proof,
  HasAdjDiff := sorry,
  abbrev ∂† := λ dcont' => dropElem k dcont' by sorry_proof
argument elem
  HasAdjoint [Fact (cont=0)] := sorry_proof,
  abbrev † [Fact (cont=0)] := λ elem' => ∑ i : Fin k, elem'[⟨n+i.1, sorry_proof⟩] b sorry_proof,
  HasAdjDiff := sorry,
  abbrev ∂† := λ delem' => ∑ i : Fin k, delem'[⟨n+i.1, sorry_proof⟩] by sorry_proof
