import SciLean.Core.Notation.CDeriv
import SciLean.Core.Notation.Gradient
import SciLean.Core.Notation.FwdCDeriv
import SciLean.Core.Notation.RevCDeriv
import SciLean.Core.FloatAsReal


open SciLean

variable {K} [RealScalar K]

set_default_scalar K

#check ∂ (fun x : K => x*x)
#check ∂ (fun x => x*x) 1
#check ∂ (x:=(1:K)), x*x
#check ∂ (x:=1), x*x
#check ∂ (x:=0.1), x*x
#check ∂ (x:=((1:K),(2:K))), (x + x)
#check 
  let df := ∂ (fun x : K×K => (x.1 + x.2*x.1)) (0,0)
  df (0,0)


#check ∂! (fun x : K => x^2)
#check ∂! (fun x : K×K => x + x)
#check ∂! (fun x => x*x) 1
#check ∂! (x:=((1:K),(2:K))), (x + x)
#check ∂! (x:=1), x*x


#check ∂ (fun x : K => x*x)
       =
       (fun x => x + x)

variable {X} [Vec K X] (f : X → X)

#check ∂ (x:=0), f x

set_default_scalar Float 

#eval ∂! (fun x => x^2) 1
#eval ∂! (fun x => x*x) 1
#eval ∂! (x:=1), x*x
#eval ∂! (fun x => x + x) (1.0,2.0) (1.0,0.0)
#eval ∂! (x:=(1.0,2.0);(1.0,0.0)), (x + x)



--------------------------------------------------------------------------------

set_default_scalar K 

#check ∇ x : (K×K), x.1
#check ∇! x : (K×K), x.1
#check ∇! x : (K×K), x.2

variable (y : K × K)

#check ∇ (x:=y), (x + x)
#check ∇ (fun x => x + x) y
#check ∇ (fun x => x + x) ((1.0,2.0) : K×K)
#check (∇! x : (K×K), ⟪x,(1,0)⟫)


set_default_scalar Float

#eval ∇! (fun x => x^2) 1
#eval ∇! (fun x => x*x) 1
#eval ∇! (x:=1), x*x
#eval ∇! (fun x : Float×Float => (x + x).2) (1.0,2.0)
#eval ∇! (x:=((1.0 : Float),(2.0:Float))), (x + x).1



--------------------------------------------------------------------------------

set_default_scalar K

#check ∂>! x : K×K, (x.1 + x.2*x.1)
#check ∂>! x:=(1:K);2, (x + x*x)
#check 
  let a := ∂> (fun x : K×K => (x.1 + x.2*x.1))
  a (0,0)


--------------------------------------------------------------------------------

set_default_scalar K

#check <∂! x : K×K, (x.1 + x.2*x.1)
#check <∂! x:=(1:K), (x + x*x)

