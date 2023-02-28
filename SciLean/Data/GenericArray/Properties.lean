import SciLean.Data.GenericArray.Algebra
import SciLean.Tactic.CustomSimp.DebugSimp

namespace SciLean

variable {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam}
variable [GenericArray Cont Idx Elem] [Enumtype Idx] 

-- There are some issues working with `getElem : (x : Cont) → (i : Idx) → Dom x i → Elem`
-- bacause it has inherently dependent types plus `Dom x i : Prop` and 
-- we do not have `Vec (P → X)` for `P : Prop` and `X : Type`

--------------------------------------------------------------------------------
-- getElem 
--------------------------------------------------------------------------------

instance getElem.arg_cont_.isLin [Vec Elem]
  : IsLin (λ (cont : Cont) (idx : Idx) => cont[idx]) := sorry_proof
instance getElem.arg_cont.isLin [Vec Elem] (idx : Idx)
  : IsLin (λ (cont : Cont) => cont[idx]) := sorry_proof

instance getElem.arg_cont_.isSmooth [Vec Elem]
  : IsSmooth (λ (cont : Cont) (idx : Idx) => cont[idx]) := by infer_instance
instance getElem.arg_cont.isSmooth [Vec Elem] (idx : Idx)  
  : IsSmooth (λ (cont : Cont) => cont[idx]) := by infer_instance
instance getElem.arg_cont.composition.isSmooth [Vec Elem] [Vec X]
  (f : X → Cont) [IsSmoothT f] (idx : Idx)
  : IsSmoothT (λ (x : X) => (f x)[idx]) := comp.arg_x.isSmooth (λ cont => cont[idx]) f


@[diff] theorem getElem.arg_cont_.diff_simp [Vec Elem]
  : ∂ (λ (cont : Cont) (idx : Idx) => cont[idx]) = λ cont dcont idx => dcont[idx]
  := by symdiff; done
@[diff] theorem getElem.arg_cont_.tangentMap_simp [Vec Elem]
  : 𝒯 (λ (cont : Cont) (idx : Idx) => cont[idx])
    = 
    λ cont dcont => (λ idx => cont[idx], λ idx => dcont[idx])
  := by symdiff; done
@[diff] theorem getElem.arg_cont.diff_simp [Vec Elem] (idx : Idx)
  : ∂ (λ (cont : Cont) => cont[idx]) = λ cont dcont => dcont[idx]
  := by symdiff; done
@[diff] theorem getElem.arg_cont.tangentMap_simp [Vec Elem] (idx : Idx)
  : 𝒯 (λ (cont : Cont) => cont[idx])
    = 
    λ cont dcont => (cont[idx],dcont[idx])
  := by symdiff; done
@[diff] theorem getElem.arg_cont.comp.diff_simp [Vec Elem] [Vec X]
  (f : X → Cont) [IsSmoothT f] (idx : Idx)
  : ∂ (λ (x : X) => (f x)[idx]) = λ x dx => (∂ f x dx)[idx]
  := by rw[differential.of_comp (λ cont => cont[idx]'sorry_proof) f]; symdiff; done


instance getElem.arg_cont.hasAdjoint [SemiHilbert Elem] (idx : Idx)
  : HasAdjoint (λ (cont : Cont) => cont[idx]) := sorry_proof
@[diff] theorem getElem.arg_cont.adj_simp [SemiHilbert Elem] (idx : Idx)
  : (λ (cont : Cont) => cont[idx])† = λ cont' => setElem 0 idx cont' := sorry_proof
@[diff] theorem getElem.arg_cont.comp.adj_simp [SemiHilbert Elem] [SemiHilbert X] (idx : Idx)
  (f : X → Cont) [HasAdjointT f]
  : (λ x => (f x)[idx])† = λ x' => f† (setElem 0 idx x') :=
by 
  rw[comp.arg_x.adj_simp (λ cont : Cont => cont[idx]'True.intro) f]; symdiff; done

instance getElem.arg_cont.hasAdjDiff [SemiHilbert Elem] (idx : Idx)
  : HasAdjDiff (λ (cont : Cont) => cont[idx]) := by apply infer_HasAdjDiff'; symdiff; infer_instance; done

@[diff] theorem getElem.arg_cont.adjDiff_simp [SemiHilbert Elem] (idx : Idx)
  : ∂† (λ (cont : Cont) => cont[idx]) = λ _ dcont' => setElem 0 idx dcont' := by unfold adjointDifferential; symdiff; symdiff; done
@[diff] theorem getElem.arg_cont.comp.adjDiff_simp [SemiHilbert Elem] [SemiHilbert X] (idx : Idx)
  (f : X → Cont) [inst : HasAdjDiffT f]
  : ∂† (λ (x : X) => (f x)[idx]) = λ x dx' => ∂† f x (setElem 0 idx dx') := 
by 
  have _ := inst.1.1
  have _ := inst.1.2

  unfold adjointDifferential
  symdiff; symdiff
  done


-- This unfortunatelly does not solve automatically :( the unification fails
set_option trace.Meta.Tactic.simp true in
set_option trace.Meta.Tactic.simp.rewrite true in
example (x : Idx) (f : ℝ → Cont) [Vec Elem] [IsSmoothT f] 
  : ∂ (λ (s : ℝ) => (f s)[x]) = λ s ds => (∂ f s ds)[x] := 
by 
  rw[differential.of_comp (λ g => getElem g x True.intro) f]
  symdiff
  done


--------------------------------------------------------------------------------
-- setElem 
--------------------------------------------------------------------------------

function_properties setElem [Vec Elem] (cont : Cont) (idx : Idx) (elem : Elem) : Cont
-- argument (cont,elem)
--   isLin := sorry_proof,
--   isSmooth,
--   abbrev ∂ 𝒯 := setElem dcont idx delem by sorry_proof
argument cont
  isSmooth := sorry_proof, 
  abbrev ∂ 𝒯 := setElem dcont idx 0 by sorry_proof
argument elem
  isSmooth := sorry_proof,
  abbrev ∂ 𝒯 := setElem 0 idx delem by sorry_proof

function_properties setElem [SemiHilbert Elem] (cont : Cont) (idx : Idx) (elem : Elem) : Cont
argument cont 
  hasAdjoint [Fact (elem=0)] := sorry_proof,
  abbrev † [Fact (elem=0)] := setElem cont' idx 0 by sorry_proof,
  hasAdjDiff := by apply infer_HasAdjDiff'; symdiff; infer_instance; done,
  abbrev ∂† ℛ := setElem dcont' idx 0 by unfold adjointDifferential; symdiff; symdiff; done
argument elem
  hasAdjoint [Fact (cont=0)] := sorry_proof,
  abbrev † [Fact (cont=0)] := elem'[idx] by sorry_proof,
  hasAdjDiff := by apply infer_HasAdjDiff'; symdiff; infer_instance; done,
  abbrev ∂† := delem'[idx] by unfold adjointDifferential; symdiff; symdiff; done


--------------------------------------------------------------------------------
-- introElem 
--------------------------------------------------------------------------------

function_properties introElem [Vec Elem] (f : Idx → Elem) : Cont
argument f
  isLin := sorry_proof,
  isSmooth,
  abbrev ∂ 𝒯 := introElem df by symdiff

function_properties introElem [SemiHilbert Elem] (f : Idx → Elem) : Cont
argument f
  hasAdjoint := sorry_proof,
  abbrev † := λ idx => f'[idx] by sorry_proof,
  hasAdjDiff := by apply infer_HasAdjDiff'; symdiff; infer_instance; done,
  abbrev ∂† ℛ := λ idx => df'[idx] by unfold adjointDifferential; symdiff; symdiff; done


---

-- TODO: modify, mapIdx, map

