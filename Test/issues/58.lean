import SciLean.Analysis.Calculus.HasFwdFDeriv

open SciLean


variable {R} [RCLike R]


/-- warning: unknown free variable '_fvar.1235' -/
#guard_msgs in
#check_failure (HasFwdFDeriv R (fun (((a,b,c),d) : (R×R×R)×R) => a) _)
  rewrite_by
    data_synth -domainDec
