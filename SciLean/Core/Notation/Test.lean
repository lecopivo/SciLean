import SciLean.Core.Notation

open SciLean

section CDeriv

variable
  (K) [IsROrC K]
  {X Y} [Vec K X] [Vec K Y]
  (f : X → Y) (g : K → X) (x dx : X) (t dt : K) (y : Y)

set_default_scalar K


/--
info: ∂ f : X → X → Y
-/
#guard_msgs in
#check ∂ f

/--
info: ∂ f x : X → Y
-/
#guard_msgs in
#check ∂ f x

/--
info: ∂ x', f x' : X → X → Y
-/
#guard_msgs in
#check (∂ x', f x')

/--
info: ∂ (x':=x;dx), f x' + y : Y
-/
#guard_msgs in
#check (∂ x':=x, f x') dx + y

/--
info: ∂ (x':=x;dx), f x' + y : Y
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
info: ∂ (t':=t;dt), g t' + x : X
-/
#guard_msgs in
#check ∂ t':=t;dt, g t' + x

end CDeriv


section Gradient

variable (K) [IsROrC K]
  {X Y} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y]
  (f : X → Y) (g : X → K) (x dx : X) (y dy : Y) (k dk : K)

set_default_scalar K

/--
info: ∇ f : X → Y → X
-/
#guard_msgs in
#check ∇ f

/--
info: ∇ x', f x' : X → Y → X
-/
#guard_msgs in
#check ∇ x', f x'

/--
info: ∇ (x':=x), f x' : Y → X
-/
#guard_msgs in
#check ∇ x':=x, f x'

/--
info: ∇ (x':=x;dy), f x' + dx : X
-/
#guard_msgs in
#check ∇ x':=x;dy, f x' + dx

--TODO: this should produce eroror `function expected at f x'`
/--
warning: unexpected syntax
  ∇ fun x' => f x' dx
-/
#guard_msgs in
#check_failure ∇ x', f x' dx


/--
info: ∇ g : X → X
-/
#guard_msgs in
#check ∇ g

/--
info: ∇ x', g x' : X → X
-/
#guard_msgs in
#check ∇ x', g x'

/--
info: ∇ (x':=x), g x' : X
-/
#guard_msgs in
#check ∇ x':=x, g x'

/--
info: ∇ (x':=x;dk), g x' + dx : X
-/
#guard_msgs in
#check ∇ x':=x;dk, g x' + dx

end Gradient



section FwdCDeriv

variable
  (K) [IsROrC K]
  {X Y} [Vec K X] [Vec K Y]
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
  (K) [IsROrC K]
  {X Y} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y]
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

/--
info: <∂ (x':=x;dy), f x' : Y × X
-/
#guard_msgs in
#check <∂ x':=x;dy, f x'

end RevCDeriv
