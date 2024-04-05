import SciLean.Core.Rand.Rand
import SciLean.Core.Rand.Distributions.Normal
import SciLean.Core.Distribution.Basic
import SciLean.Core.Distribution.ParametricDistribDeriv
namespace SciLean.Rand


variable {R} [RealScalar R]


def model : Rand (R×R) := do
  let v ← normal R (0:R) (5:R)
  if v > 0 then
    let obs ← normal R 1 1 -- 1 1
    return (v,obs)
  else
    let obs ← normal R (-2) 1
    return (v,obs)

def prior : Rand R := normal R 0 5

def likelihood (v : R) : Rand R :=
  if v > 0 then
    normal R 1 1
  else
    normal R (-2) 1

open Classical in

noncomputable
def Rand.condition [Inhabited X₂] (rx : Rand X) (mk : X₁ → X₂ → X) (x₁ : X₁) : Rand X₂ :=
  if h : ∃ rx₂ : X₁ → Rand X₂, ∀ (rx₁ : Rand X₁), (do let x₁ ← rx₁; let x₂ ← rx₂ x₁; return mk x₁ x₂) = rx then
    choose h x₁
  else
    return default


variable [Inhabited X]
noncomputable
def posterior (prior : Rand X) (likelihood : X → Rand Y) (obs : Y) : Rand X := do
  let joint := do
    let x ← prior
    let y ← likelihood x
    return (x,y)

  joint.condition (fun y x => (x,y)) obs


def guide (θ : R) : Rand R := normal R θ 1

open MeasureTheory
variable {X} [MeasurableSpace X]

noncomputable
def KLDiv (P Q : Rand X) : R := P.E (fun x => Scalar.log (P.pdf R Q.ℙ x))



noncomputable
def loss (θ : R) := KLDiv (R:=R) (guide θ) (posterior prior likelihood (0 : R))

variable
  {W} [Vec R W]
  [Vec R X]


theorem KLDiv.arg_P.cderiv_rule (P : W → Rand X) (Q : Rand X) :
    cderiv R (fun w => KLDiv (R:=R) (P w) Q)
    =
    fun w dw =>
      let dP := parDistribDeriv (fun w => (P w).ℙ.toDistribution (R:=R)) w dw
      dP.extAction' (fun x => Scalar.log ((P w).pdf R Q.ℙ x) - 1) := sorry_proof
