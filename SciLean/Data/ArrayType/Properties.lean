import SciLean.Data.ArrayType.Algebra

namespace SciLean

variable {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam}
variable [GenericArrayType Cont Idx Elem] [Enumtype Idx] 

-- There are some issues working with `getElem : (x : Cont) → (i : Idx) → Dom x i → Elem`
-- bacause it has inherently dependent types plus `Dom x i : Prop` and 
-- we do not have `Vec (P → X)` for `P : Prop` and `X : Type`

--------------------------------------------------------------------------------
-- getElem 
--------------------------------------------------------------------------------


theorem getElem.arg_cont.IsLin [Vec Elem] (idx : Idx) (dom)
  : IsLin (λ (cont : Cont) => getElem cont idx dom) := sorry_proof
instance getElem.arg_cont.IsLin' [Vec Elem] {T : Type} [Vec T] (cont : T → Cont) (idx : Idx) (dom) [SciLean.IsLin cont] 
  : SciLean.IsLin (λ t => getElem (cont t) idx dom) := sorry_proof

instance getElem.arg_cont.IsSmooth [Vec Elem] (idx : Idx) (dom)
  : IsSmooth (λ (cont : Cont) => getElem cont idx dom) := sorry_proof
instance getElem.arg_cont.IsSmooth' [Vec Elem] {T : Type} [Vec T] (cont : T → Cont) (idx : Idx) (dom) [SciLean.IsSmooth cont] 
  : SciLean.IsSmooth (λ t => getElem (cont t) idx dom) := sorry_proof


theorem getElem.arg_cont.differential_simp [Vec Elem] (idx : Idx) (dom)
  : ∂ (λ (cont : Cont) => getElem cont idx dom)
    =
    λ cont dcont => dcont[idx] := sorry_proof

theorem getElem.arg_cont.differential_simp' [Vec Elem] {T : Type} [Vec T] (cont : T → Cont) (idx : Idx) (dom) [SciLean.IsSmooth cont]
  : ∂ (λ t => getElem (cont t) idx dom)
    =
    λ t dt => (∂ cont t dt)[idx]
  := sorry_proof


theorem getElem.arg_cont.tangentMap_simp [Vec Elem] (idx : Idx) (dom)
  : 𝒯 (λ (cont : Cont) => getElem cont idx dom)
    =
    λ cont dcont => (cont[idx], dcont[idx]) := sorry_proof

theorem getElem.arg_cont.tangentMap_simp' [Vec Elem] {T : Type} [Vec T] (cont : T → Cont) (idx : Idx) (dom) [SciLean.IsSmooth cont]
  : 𝒯 (λ t => getElem (cont t) idx dom)
    =
    λ t dt => 
      let Tcont := 𝒯 cont t dt
      (Tcont.fst[idx], Tcont.snd[idx])
  := sorry_proof


instance getElem.arg_cont.HasAdjoint [SemiHilbert Elem] (idx : Idx) (dom)
  : HasAdjoint (λ (cont : Cont) => getElem cont idx dom) := sorry_proof
instance getElem.arg_cont.HasAdjoint' [SemiHilbert Elem] {T : Type} [SemiHilbert T] (cont : T → Cont) (idx : Idx) (dom) [SciLean.HasAdjoint cont] 
  : SciLean.HasAdjoint (λ t => getElem (cont t) idx dom) := sorry_proof

theorem getElem.arg_cont.adjoint_simp [SemiHilbert Elem] (idx : Idx) (dom)
  : (λ (cont : Cont) => getElem cont idx dom)†
    =
    λ cont' => setElem 0 idx cont' := sorry_proof

theorem getElem.arg_cont.adjoint_simp' [SemiHilbert Elem] {T : Type} [SemiHilbert T] (cont : T → Cont) (idx : Idx) (dom) [SciLean.HasAdjoint cont]
  : (λ t => getElem (cont t) idx dom)†
    =
    λ t' => cont† (setElem 0 idx t')
  := sorry_proof


instance getElem.arg_cont.HasAdjDiff [SemiHilbert Elem] (idx : Idx) (dom)
  : HasAdjDiff (λ (cont : Cont) => getElem cont idx dom) := sorry_proof
instance getElem.arg_cont.HasAdjDiff' [SemiHilbert Elem] {T : Type} [SemiHilbert T] (cont : T → Cont) (idx : Idx) (dom) [SciLean.HasAdjDiff cont] 
  : SciLean.HasAdjDiff (λ t => getElem (cont t) idx dom) := sorry_proof

theorem getElem.arg_cont.adjointDifferential_simp [SemiHilbert Elem] (idx : Idx) (dom)
  : ∂† (λ (cont : Cont) => getElem cont idx dom)
    =
    λ _ dcont' => setElem 0 idx dcont' := sorry_proof

theorem getElem.arg_cont.adjointDifferential_simp' [SemiHilbert Elem] {T : Type} [SemiHilbert T] (cont : T → Cont) (idx : Idx) (dom) [SciLean.HasAdjoint cont]
  : ∂† (λ t => getElem (cont t) idx dom)
    =
    λ t dt' => ∂† cont t (setElem 0 idx dt')
  := sorry_proof

theorem getElem.arg_cont.reverseDifferential_simp [SemiHilbert Elem] (idx : Idx) (dom)
  : ℛ (λ (cont : Cont) => getElem cont idx dom)
    =
    λ cont => (cont[idx], λ dcont' => setElem 0 idx dcont') := sorry_proof

theorem getElem.arg_cont.reverseDifferential_simp' [SemiHilbert Elem] {T : Type} [SemiHilbert T] (cont : T → Cont) (idx : Idx) (dom) [SciLean.HasAdjoint cont]
  : ℛ (λ t => getElem (cont t) idx dom)
    =
    λ t => 
      let Rcont := ℛ cont t
      (Rcont.fst[idx], λ dt' => Rcont.snd (setElem 0 idx dt'))
  := sorry_proof

-- register function transformations for ite
#eval show Lean.CoreM Unit from do

  addFunctionProperty ``getElem ``IsSmooth #[5].toArraySet ``getElem.arg_cont.IsSmooth ``getElem.arg_cont.IsSmooth' none
  addFunctionProperty ``getElem ``HasAdjoint #[5].toArraySet ``getElem.arg_cont.HasAdjoint ``getElem.arg_cont.HasAdjoint' none
  addFunctionProperty ``getElem ``HasAdjDiff #[5].toArraySet ``getElem.arg_cont.HasAdjDiff ``getElem.arg_cont.HasAdjDiff' none
  addFunctionProperty ``getElem ``differential #[5].toArraySet ``getElem.arg_cont.differential_simp ``getElem.arg_cont.differential_simp' none
  addFunctionProperty ``getElem ``tangentMap #[5].toArraySet ``getElem.arg_cont.tangentMap_simp ``getElem.arg_cont.tangentMap_simp' none
  addFunctionProperty ``getElem ``adjointDifferential #[5].toArraySet ``getElem.arg_cont.adjointDifferential_simp ``getElem.arg_cont.adjointDifferential_simp' none
  addFunctionProperty ``getElem ``reverseDifferential #[5].toArraySet ``getElem.arg_cont.reverseDifferential_simp ``getElem.arg_cont.reverseDifferential_simp' none


--------------------------------------------------------------------------------
-- setElem 
--------------------------------------------------------------------------------

function_properties SciLean.SetElem.setElem {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam} 
  [GenericArrayType Cont Idx Elem] [Enumtype Idx] [Vec Elem] 
  (cont : Cont) (idx : Idx) (elem : Elem)
argument (cont, elem)
  IsLin := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dcont delem => setElem dcont idx delem by sorry_proof,
  abbrev 𝒯 := λ dcont delem => (setElem cont idx elem, setElem dcont idx delem) by sorry_proof
argument cont
  IsLin [Fact (elem = 0)] := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dcont => setElem dcont idx 0 by sorry_proof,
  abbrev 𝒯 := λ dcont=> (setElem cont idx elem, setElem dcont idx 0) by sorry_proof
argument elem
  IsLin [Fact (cont = 0)] := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ delem => setElem 0 idx delem by sorry_proof,
  abbrev 𝒯 := λ delem => (setElem cont idx elem, setElem 0 idx delem) by sorry_proof

function_properties SciLean.SetElem.setElem {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam} 
  [GenericArrayType Cont Idx Elem] [Enumtype Idx] [SemiHilbert Elem] 
  (cont : Cont) (idx : Idx) (elem : Elem)
argument (cont, elem)
  HasAdjoint := sorry_proof,
  abbrev † := λ contelem' => (setElem contelem' idx 0 , contelem'[idx]) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dcontelem' => (setElem dcontelem' idx 0 , dcontelem'[idx]) by sorry_proof,
  abbrev ℛ := (setElem cont idx elem, λ dcontelem' => (setElem dcontelem' idx 0 , dcontelem'[idx])) by sorry_proof
argument cont
  HasAdjoint [Fact (elem = 0)] := sorry_proof,
  abbrev † [Fact (elem = 0)] := λ cont' => (setElem cont' idx 0) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dcont' => (setElem dcont' idx 0) by sorry_proof,
  abbrev ℛ := (setElem cont idx elem, λ dcont' => (setElem dcont' idx 0)) by sorry_proof
argument elem
  HasAdjoint [Fact (cont = 0)] := sorry_proof,
  abbrev † [Fact (cont = 0)] := λ elem' => (elem'[idx]) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ delem' => delem'[idx] by sorry_proof,
  abbrev ℛ := (setElem cont idx elem, λ delem' => delem'[idx]) by sorry_proof

--------------------------------------------------------------------------------
-- introElem 
--------------------------------------------------------------------------------

-- function_properties SciLean.IntroElem.introElem {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam} 
--   [GenericArrayType Cont Idx Elem] [Enumtype Idx] [Vec Elem] (f : Idx → Elem) 
-- argument f
--   IsLin := sorry_proof,
--   IsSmooth := sorry_proof,
--   abbrev ∂ := introElem df by sorry_proof

-- function_properties introElem [SemiHilbert Elem] (f : Idx → Elem) : Cont
-- argument f
--   hasAdjoint := sorry_proof,
--   abbrev † := λ idx => f'[idx] by sorry_proof,
--   hasAdjDiff, 
--   abbrev ∂† ℛ := λ idx => df'[idx] by unfold adjointDifferential; symdiff; symdiff; done


---

-- TODO: modify, mapIdx, map
