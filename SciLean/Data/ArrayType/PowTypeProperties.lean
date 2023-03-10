import SciLean.Data.ArrayType.PowType
import SciLean.Data.ArrayType.Properties


namespace SciLean

variable {X I} {T : outParam Type} [Enumtype I] [PowType T I X] -- [Inhabited X]

--------------------------------------------------------------------------------
-- introElem 
--------------------------------------------------------------------------------

function_properties introPowElem [Vec X] (f : I → X) : X^I
argument f
  isLin := by unfold introPowElem; apply IsLinN.mk,
  isSmooth,
  abbrev ∂ 𝒯 := introPowElem df by symdiff


function_properties introPowElem [SemiHilbert X] (f : I → X) : X^I
argument f
  hasAdjoint := by unfold introPowElem; apply HasAdjointN.mk,
  abbrev † := λ idx => f'[idx] by unfold introPowElem; rw[introElem.arg_f.adjoint_simp], -- TODO: Figure out why I have to manually invoke `introElem.arg_f.adjoint_simp`
  hasAdjDiff
  -- This causes some issues, the `dom` in `getElem` fails to be infered automatically  
  -- and even when provided explicitly it casauses mayham.
  -- Therefore we state it separetely
  -- abbrev ∂† ℛ := λ idx => df'[idx] by unfold adjointDifferential; symdiff; symdiff; done

-- TODO: 
@[diff]
theorem introPowElem.arg_f.adjDiff_simp [SemiHilbert X]
  : ∂† (λ (f : I → X) => introPowElem f)
    =
    λ f df' => (λ idx => df'[idx]) := sorry_proof

@[diff]
theorem introPowElem.arg_f.revDiff_simp [SemiHilbert X]
  : ℛ (λ (f : I → X) => introPowElem f)
    =
    λ f => (introPowElem f, λ df' => (λ idx => df'[idx])) := by unfold reverseDifferential; symdiff


-- This example was timing out if `introPowElem` is `abbrev` instead of `def`
example {ι} [Enumtype ι] (i : ι)
  : (λ (f : ι → ℝ) => f i)†
    = 
    λ f' i' => [[i=i']] * f' := 
by 
  symdiff
  done
