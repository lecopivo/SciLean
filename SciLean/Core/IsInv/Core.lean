import SciLean.Algebra

namespace SciLean

class IsInv {X Y} (f : X → Y) where
  (is_inv : Function.bijective f)


variable {α β γ : Type}
variable {X Y Z : Type} 

instance id.arg_x.isInv
  : IsInv λ x : X => x := sorry

instance const.arg_x.isInv [Subsingleton ι] [Nonempty ι]
  : IsInv (λ (x : X) (i : ι) => x)
:= sorry

instance comp.arg_x.isInv
  (f : Y → Z) [IsInv f] 
  (g : X → Y) [IsInv g] 
  : IsInv (λ x => f (g x)) := sorry

--------------------------------------------------------------------
-- Variants a of theorems at points --
-- These are necessary as higher order unification is only approximated

instance comp.arg_x.parm1.isInv
  (a : α)
  (f : Y → α → Z) [IsInv (λ y => f y a)]
  (g : X → Y) [IsInv g] 
  : IsInv (λ x => f (g x) a)
:= by 
  (apply comp.arg_x.isInv (λ y => f y a) g) done

instance comp.arg_x.parm2.isInv
  (a : α) (b : β)
  (f : Y → α → β → Z) [IsInv (λ y => f y a b)]
  (g : X → Y) [IsInv g] 
  : IsInv (λ x => f (g x) a b)
:= by 
  (apply comp.arg_x.isInv (λ y => f y a b) g) done

instance comp.arg_x.parm3.isInv
  (a : α) (b : β) (c : γ)
  (f : Y → α → β → γ → Z) [IsInv (λ y => f y a b c)]
  (g : X → Y) [IsInv g] 
  : IsInv (λ x => f (g x) a b c)
:= by 
  (apply comp.arg_x.isInv (λ y => f y a b c) g) done



