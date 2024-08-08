import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Algebra.Module.LocallyConvex

import SciLean.Util.SorryProof


namespace SciLean

set_option linter.unusedVariables false

-- TODO: move this section
namespace Curve

variable {K : Type u} [NontriviallyNormedField K]
variable {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F] -- [TopologicalAddGroup F] [ContinuousSMul K F]
variable {E : Type w} [AddCommGroup E] [Module K E] [TopologicalSpace E] -- [TopologicalAddGroup E] [ContinuousSMul K E]

open scoped Classical Topology BigOperators Filter ENNReal

open Filter Asymptotics Set

def HasDerivAtFilter (f : K → F) (f' : F) (x : K) (L : Filter K) :=
  Tendsto (fun x' => (x' - x)⁻¹ • (f x' - f x)) L (nhds f')

def HasDerivAt (f : K → F) (f' : F) (x : K) :=
  HasDerivAtFilter f f' x (𝓝 x)

def DifferentiableAt (f : K → F) (x : K) :=
  ∃ f' : F, HasDerivAt f f' x

noncomputable
def deriv (f : K → F) (x : K) :=
  if h : ∃ f', HasDerivAt f f' x then Classical.choose h else 0

def Differentiable (f : K → F) :=
  ∀ x, DifferentiableAt f x

-- TODO: This should probably be true on small neighborhood of x not just *at* x
def ContDiffAt' (f : K → F) (x : K) (n : ℕ) :=
  match n with
  | 0 => ContinuousAt f x
  | (n+1) => DifferentiableAt f x ∧ ContDiffAt' (deriv f) x n

def ContDiffAt (f : K → F) (x : K) (n : ℕ∞) :=
  match n with
  | .none => ∀ n', ContDiffAt' f x n'
  | .some n' => ContDiffAt' f x n'

abbrev ContDiff (f : K → F) (n : ℕ∞) := ∀ x, ContDiffAt f x n
abbrev SmoothAt        (f : K → F) (x : K)   := ContDiffAt f x ⊤
abbrev Smooth          (f : K → F)           := ContDiff f ⊤

end Curve
