import SciLean.Tactic.FProp.Basic
import SciLean.Tactic.FProp.Notation

import SciLean.Core.Objects.SemiInnerProductSpace

set_option linter.unusedVariables false

namespace SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {ι : Type _} [Fintype ι] 
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)] 

def HasSemiAdjoint (f : X → Y) : Prop :=
   ∃ f' : Y → X, 
     ∀ x y, TestFunction x → ⟪y, f x⟫[K] = ⟪f' y, x⟫[K]
   -- at some point I was convinced that these conditions are important
   -- maybe add: ∀ x, TestFunction x → TestFunction (f x) - I think this is important for proving linearity of f'
   -- maybe add: ∀ y, TestFunction y → TestFunction (f' y)

noncomputable
def semiAdjoint (f : X → Y) :=
  match Classical.dec (HasSemiAdjoint K f) with
  | isTrue h => Classical.choose h
  | isFalse _ => 0

def semi_inner_ext (x x' : X)
  : (∀ φ, TestFunction φ → ⟪x, φ⟫[K] = ⟪x', φ⟫[K])
    →
    x = x' := sorry_proof

theorem semiAdjoint_choose {f : X → Y} (hf : HasSemiAdjoint K f)
  : semiAdjoint K f = Classical.choose hf := sorry_proof

def semiAdjoint_unique (f : X → Y) (hf : HasSemiAdjoint K f)
  (f' : Y → X) (hf' : ∀ x y, TestFunction x → ⟪y, f x⟫[K] = ⟪f' y, x⟫[K])
  : f' = semiAdjoint K f :=
by
  funext y
  apply semi_inner_ext K
  intro φ hφ
  rw[← hf' φ y hφ]
  rw[semiAdjoint_choose _ hf]
  rw[← Classical.choose_spec hf φ y hφ]


namespace HasSemiAdjoint 


variable (X)
theorem id_rule (x : X)
  : HasSemiAdjoint K (fun x : X => x) := 
by 
  apply Exists.intro (fun x => x) _
  simp
  
theorem const_rule 
  : HasSemiAdjoint K (fun _ : X => (0:Y)) := 
by 
  apply Exists.intro (fun _ => 0) _
  simp; sorry_proof
variable {X}

variable (E)
theorem proj_rule
  (i : ι)
  : HasSemiAdjoint K (fun x : (i : ι) → E i => x i) := 
by sorry_proof
variable {E}

theorem comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : HasSemiAdjoint K f) (hg : HasSemiAdjoint K g)
  : HasSemiAdjoint K (fun x => f (g x))
  := by sorry_proof

theorem let_rule
  (f : X → Y → Z) (g : X → Y)
  (hf : HasSemiAdjoint K (fun (xy : X×Y) => f xy.1 xy.2))
  (hg : HasSemiAdjoint K g)
  : HasSemiAdjoint K (fun x => let y := g x; f x y) := 
by sorry_proof
  
theorem pi_rule
  (f : (i : ι) → X → E i)
  (hf : ∀ i, HasSemiAdjoint K (f i))
  : HasSemiAdjoint K (fun x i => f i x)
  := by sorry_proof


end HasSemiAdjoint 
