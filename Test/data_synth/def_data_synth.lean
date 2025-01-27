import SciLean.Analysis.Calculus.HasFDeriv
import SciLean.Analysis.AdjointSpace.HasAdjoint
import SciLean.Tactic.ConvAssign

open SciLean


variable
  {K : Type*} [RCLike K]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace K Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace K Z]


def foo (r : K) (x : X) : X := x + r•x

abbrev_data_synth foo in x : HasAdjoint K by unfold foo; data_synth
abbrev_data_synth foo in x : HasAdjointUpdate K by unfold foo; data_synth

abbrev_data_synth foo in x (x₀) : (HasFDerivAt (𝕜:=K) · · x₀) by unfold foo; data_synth
abbrev_data_synth foo in r (r₀) : (HasFDerivAt (𝕜:=K) · · r₀) by unfold foo; data_synth
abbrev_data_synth foo in r x (rx₀) : (HasFDerivAt (𝕜:=K) · · rx₀) by unfold foo; data_synth


def bar (x : X) : X := x

-- todo: allow universe polymorphic `R` here!
abbrev_data_synth bar in x {R : Type} [RealScalar R] [NormedAddCommGroup X] [AdjointSpace R X] :
    HasAdjoint R by
  conv => enter [3]; assign (fun x => x)
  constructor
  case adjoint   => simp [bar]
  case is_linear => fun_prop [bar]

abbrev_data_synth bar in x {R : Type} [RealScalar R] [NormedAddCommGroup X] [AdjointSpace R X] (x₀) :
    (HasFDerivAt (𝕜:=R) · · x₀) by
  conv => enter [2]; assign (fun dx : X =>L[R] dx)
  sorry_proof
