import SciLean.Analysis.Calculus.Notation.Deriv
import SciLean.Analysis.Calculus.Notation.FwdDeriv
import SciLean.Analysis.Calculus.Notation.RevDeriv
import SciLean.Analysis.Calculus.Notation.Gradient

open SciLean

section CDeriv

variable
  (K) [RCLike K]
  {X} [NormedAddCommGroup X] [NormedSpace K X]
  {Y} [NormedAddCommGroup Y] [NormedSpace K Y]
  (f : X → Y) (g : K → X) (x dx : X) (t dt : K) (y : Y)

set_default_scalar K


/--
info: ∂ f : X → X →L[K] Y
-/
#guard_msgs in
#check ∂ f

/--
info: ∂ f x : X →L[K] Y
-/
#guard_msgs in
#check ∂ f x

/--
info: ∂ x', f x' : X → X →L[K] Y
-/
#guard_msgs in
#check (∂ x', f x')

/--
info: (∂ (x':=x), f x') dx + y : Y
-/
#guard_msgs in
#check (∂ x':=x, f x') dx + y

/--
info: (∂ (x':=x), f x') dx + y : Y
-/
#guard_msgs in
#check ∂ x':=x;dx, f x' + y

/--
info: ∂ g : K → X
-/
#guard_msgs in
#check ∂ g

/--
info: ∂ g t : X
-/
#guard_msgs in
#check ∂ g t

/--
info: ∂ t', g t' : K → X
-/
#guard_msgs in
#check (∂ t', g t')

/--
info: ∂ (t':=t), g t' : X
-/
#guard_msgs in
#check (∂ t':=t, g t')

/--
info: (∂ (t':=t), g t') dt + x : X
-/
#guard_msgs in
#check ∂ t':=t;dt, g t' + x

end CDeriv


section Gradient

variable (K) [RCLike K]
  {X} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X] [SMul (Kᵐᵒᵖ) X] [Star X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  {XX} [NormedAddCommGroup XX] [AdjointSpace K XX] [TensorProductType K X X XX] [TensorProductSelf K X XX]
  {YX} [NormedAddCommGroup YX] [AdjointSpace K YX] [TensorProductType K Y X YX]
  (f : X → Y) (g : X → K) (x dx : X) (y dy : Y) (k dk : K)

set_default_scalar K

/-- info: ∇ f : X → YX -/
#guard_msgs in
#check ∇ f

/-- info: ∇ x', f x' : X → YX -/
#guard_msgs in
#check ∇ x', f x'

/-- info: ∇ (x':=x), f x' : YX -/
#guard_msgs in
#check ∇ x':=x, f x'


/-- info: ∇ g : X → X -/
#guard_msgs in
#check ∇ g

/-- info: ∇ x', g x' : X → X -/
#guard_msgs in
#check ∇ x', g x'

/-- info: ∇ (x':=x), g x' : X -/
#guard_msgs in
#check ∇ x':=x, g x'


end Gradient



section FwdCDeriv

variable
  (K) [RCLike K]
  {X} [NormedAddCommGroup X] [NormedSpace K X]
  {Y} [NormedAddCommGroup Y] [NormedSpace K Y]
  (f : X → Y) (g : K → X) (x dx : X) (t dt : K) (y dy : Y)

set_default_scalar K


/--
info: ∂> f : X → X → Y × Y
-/
#guard_msgs in
#check ∂> f

/--
info: ∂> f x : X → Y × Y
-/
#guard_msgs in
#check ∂> f x

/--
info: ∂> x', f x' : X → X → Y × Y
-/
#guard_msgs in
#check (∂> x', f x')

/--
info: ∂> (x':=x;dx), f x' + (y, dy) : Y × Y
-/
#guard_msgs in
#check (∂> x':=x, f x') dx + (y,dy)

/--
info: ∂> (x':=x;dx), f x' + (y, dy) : Y × Y
-/
#guard_msgs in
#check ∂> x':=x;dx, f x' + (y,dy)

end FwdCDeriv



section RevCDeriv

variable
  (K) [RCLike K]
  {X} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  (f : X → Y) (g : K → X) (x dx : X) (t dt : K) (y dy : Y)

set_default_scalar K


/--
info: <∂ f : X → Y × (Y → X)
-/
#guard_msgs in
#check <∂ f

/--
info: <∂ f x : Y × (Y → X)
-/
#guard_msgs in
#check <∂ f x

/--
info: <∂ x', f x' : X → Y × (Y → X)
-/
#guard_msgs in
#check (<∂ x', f x')

/--
info: <∂ (x':=x), f x' : Y × (Y → X)
-/
#guard_msgs in
#check (<∂ x':=x, f x')


end RevCDeriv
