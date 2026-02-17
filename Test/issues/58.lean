import SciLean.Analysis.Calculus.HasFwdFDeriv
import SciLean.Analysis.Calculus.HasRevFDeriv

open SciLean

variable {R} [RCLike R]

/--
info: HasFwdFDeriv R
  (fun x =>
    match x with
    | ((a, fst, snd), snd_1) => a)
  fun x dx =>
  have x₁ := x.1;
  have x₂ := dx.1;
  have x₁ := x₁.1;
  have x₂ := x₂.1;
  (x₁, x₂) : Prop
-/
#guard_msgs in
#check (HasFwdFDeriv R (fun (((a,_,_),_) : (R×R×R)×R) => a) _)
  rewrite_by
    data_synth -domainDec


/--
info: HasRevFDerivUpdate R
  (fun x =>
    match x with
    | ((a, fst, snd), snd_1) => a)
  fun x =>
  have x₁ := x.1;
  have x₁ := x₁.1;
  (x₁, fun dz dx =>
    have dy₂ := 0;
    have dx' := dx.1;
    have dy' := dx.2;
    have dx₁ := dx' + (dz, dy₂);
    (dx₁, dy')) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun (((a,_,_),_) : (R×R×R)×R) => a) _)
  rewrite_by
    data_synth -domainDec
