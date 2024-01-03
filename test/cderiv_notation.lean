import SciLean.Core.Notation.CDeriv

open SciLean

variable {K} [IsROrC K]

set_default_scalar K

#check ∂ (fun x : K => x*x)
#check ∂ (fun x => x*x) 1
#check ∂ (x:=(1:K)), x*x
#check ∂ (x:=1), x*x
#check ∂ (x:=0.1), x*x
#check ∂ (x:=((1:K),(2:K))), (x + x)

#check ∂! (fun x : K => x^2)
#check ∂! (fun x : K×K => x + x)
#check ∂! (fun x => x*x) 1
#check ∂! (x:=((1:K),(2:K))), (x + x)
#check ∂! (x:=1), x*x


variable {X} [Vec K X] (f : X → X)

#check ∂ (x:=0), f x
