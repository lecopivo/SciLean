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
  let x₁ := x.1;
  let x₂ := dx.1;
  let x₁ := x₁.1;
  let x₂ := x₂.1;
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
  let x₁ := x.1;
  let x₁ := x₁.1;
  (x₁, fun dz dx =>
    let dy₂ := 0;
    let dx' := dx.1;
    let dy' := dx.2;
    let dx₁ := dx' + (dz, dy₂);
    (dx₁, dy')) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun (((a,_,_),_) : (R×R×R)×R) => a) _)
  rewrite_by
    data_synth -domainDec
