import Qq

import SciLean

open SciLean

set_option linter.longLine false
set_option linter.unusedVariables false

@[gtrans]
opaque HasDeriv (f : α → β) (df : outParam <| α → α → β) : Prop

@[gtrans]
theorem hasDeriv_id : HasDeriv (fun x : α => x) (fun x dx => dx) := sorry_proof

@[gtrans]
theorem hasDeriv_const [Inhabited β] (b : β) : HasDeriv (fun x : α => b) (fun x dx => default) := sorry_proof

-- @[gtrans]
theorem hasDeriv_comp
  (f : β → γ) (g : α → β)
  (f' : β → β → γ) (g' : α → α → β)
  (hf : HasDeriv f f') (hg : HasDeriv g g') :
  HasDeriv (fun x => f (g x)) (fun x dx => f' (g x) (g' x dx)) := sorry_proof

@[gtrans]
theorem hasDeriv_add [Add β]
  (f g : α → β)
  (f' g' : α → α → β)
  (hf : HasDeriv f f') (hg : HasDeriv g g') :
  HasDeriv
    (fun x => f x + g x)
    (fun x dx =>
      let dy := f' x dx
      let dz := g' x dx
      dy + dz) := sorry_proof

@[gtrans]
theorem hasDeriv_mul [Add β] [Mul β]
  (f g : α → β)
  (f' g' : α → α → β)
  (hf : HasDeriv f f') (hg : HasDeriv g g') :
  HasDeriv
    (fun x => f x * g x)
    (fun x dx =>
      let y := f x
      let dy := f' x dx
      let z := g x
      let dz := g' x dx
      y*dz+z*dy) := sorry_proof


variable (n : ℕ)

/--
info: HasDeriv (fun x => x * x * x * x * x * x) fun x =>
  let y := x * x * x * x * x;
  fun dx =>
  let dy := x * dx + x * dx;
  let dy := x * x * dx + x * dy;
  let dy := x * x * x * dx + x * dy;
  let dy := x * x * x * x * dx + x * dy;
  y * dx + x * dy : Prop
-/
#guard_msgs in
#check (HasDeriv (fun x : Nat => x*x*x*x*x*x) _) rewrite_by gtrans (norm:=lsimp)

@[gtrans]
opaque HasDerivOn (f : α → β) (x : outParam <| Set α) (df : outParam <| α → α → β) : Prop

@[gtrans]
theorem hasDerivOn_id : HasDerivOn (fun x : α => x) ⊤ (fun x dx => dx) := sorry_proof

@[gtrans]
theorem hasDerivOn_const [Inhabited β] (b : β) : HasDerivOn (fun x : α => b) ⊤ (fun x dx => default) := sorry_proof

-- @[gtrans]
theorem hasDerivOn_comp
  (f : β → γ) (g : α → β) (s : Set α)
  (f' : β → β → γ) (g' : α → α → β)
  (hf : HasDerivOn f (g '' s) f') (hg : HasDerivOn g s g') :
  HasDerivOn (fun x => f (g x)) s (fun x dx => f' (g x) (g' x dx)) := sorry_proof

@[gtrans]
theorem hasDerivOn_add [Add β]
  (f g : α → β)
  (f' g' : α → α → β) (sf sg : Set α)
  (hf : HasDerivOn f sf f') (hg : HasDerivOn g sg g') :
  HasDerivOn
    (fun x => f x + g x)
    (sf ∩ sg)
    (fun x dx =>
      let dy := f' x dx
      let dz := g' x dx
      dy + dz) := sorry_proof

@[gtrans]
theorem hasDerivOn_mul [Add β] [Mul β]
  (f g : α → β)
  (f' g' : α → α → β) (sf sg : Set α)
  (hf : HasDerivOn f sf f') (hg : HasDerivOn g sg g') :
  HasDerivOn
    (fun x => f x * g x)
    (sf ∩ sg)
    (fun x dx =>
      let y := f x
      let dy := f' x dx
      let z := g x
      let dz := g' x dx
      y*dz+z*dy) := sorry_proof

@[gtrans]
theorem hasDerivOn_div [Add β] [Sub β] [Mul β] [Div β] [Inhabited β]
  (f g : α → β)
  (f' g' : α → α → β) (sf sg : Set α)
  (hf : HasDerivOn f sf f') (hg : HasDerivOn g sg g') :
  HasDerivOn
    (fun x => f x / g x)
    (sf ∩ sg ∩ g ⁻¹' {default}ᶜ)
    (fun x dx =>
      let y := f x
      let dy := f' x dx
      let z := g x
      let dz := g' x dx
      (dy*z-y*dz)/(z*z)) := sorry_proof


variable (n:Nat)


/--
info: HasDerivOn (fun x => x * n / (x * n)) ((fun x => x * n) ⁻¹' {0})ᶜ fun x =>
  let y := x * n;
  let z := x * n;
  fun dx =>
  let dy := n * dx;
  let dz := n * dx;
  (dy * z - y * dz) / (z * z) : Prop
-/
#guard_msgs in
#check (HasDerivOn (fun x : Nat => x*n/(x*n)) _ _) rewrite_by gtrans (norm:=lsimp)


/--
info: HasDerivOn (fun x => x * x / (x + x * x * n)) ((fun x => x + x * x * n) ⁻¹' {0})ᶜ fun x =>
  let y := x * x;
  let z := x + x * x * n;
  fun dx =>
  let dy := x * dx + x * dx;
  let dy_1 := x * dx + x * dx;
  let dz := n * dy_1;
  let dz := dx + dz;
  (dy * z - y * dz) / (z * z) : Prop
-/
#guard_msgs in
#check (HasDerivOn (fun x : Nat => x*x/(x+x*x*n)) _ _) rewrite_by gtrans (norm:=lsimp)
