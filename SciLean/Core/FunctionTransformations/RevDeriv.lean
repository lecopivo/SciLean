import SciLean.Core.FunctionPropositions.HasAdjDiffAt
import SciLean.Core.FunctionPropositions.HasAdjDiff

import SciLean.Core.FunctionTransformations.SemiAdjoint

import SciLean.Data.StructLike

import SciLean.Data.Curry

set_option linter.unusedVariables false

namespace SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]
  {ι : Type _} [EnumType ι]
  {κ : Type _} [EnumType κ]
  {E I : Type _} {EI : I → Type _} 
  [StructLike E I EI] [EnumType I]
  [SemiInnerProductSpace K E] [∀ i, SemiInnerProductSpace K (EI i)]
  [SemiInnerProductSpaceStruct K E I EI]
  {F J : Type _} {FJ : J → Type _} 
  [StructLike F J FJ] [EnumType J]
  [SemiInnerProductSpace K F] [∀ j, SemiInnerProductSpace K (FJ j)]
  [SemiInnerProductSpaceStruct K F J FJ]


noncomputable
def revDeriv
  (f : X → Y) (x : X) : Y×(Y→X) :=
  (f x, semiAdjoint K (cderiv K f x))


noncomputable
def revDerivUpdate
  (f : X → Y) (x : X) : Y×(Y→X→X) :=
  let ydf := revDeriv K f x
  (ydf.1, fun dy dx => dx + ydf.2 dy)

noncomputable
def revDerivProj
  (f : X → E) (x : X) : E×((i : I)→EI i→X) :=
  let ydf' := revDeriv K f x
  (ydf'.1, fun i de => 
    have := Classical.propDecidable
    ydf'.2 (StructLike.make fun i' => if h:i=i' then h▸de else 0))

noncomputable
def revDerivProjUpdate
  (f : X → E) (x : X) : E×((i : I)→EI i→X→X) :=
  let ydf' := revDerivProj K f x
  (ydf'.1, fun i de dx => dx + ydf'.2 i de)


--------------------------------------------------------------------------------
-- simplification rules for individual components ------------------------------
--------------------------------------------------------------------------------

@[simp, ftrans_simp]
theorem revDeriv_fst (f : X → Y) (x : X)
  : (revDeriv K f x).1 = f x :=
by
  rfl

@[simp, ftrans_simp]
theorem revDeriv_snd_zero (f : X → Y) (x : X)
  : (revDeriv K f x).2 0 = 0 := 
by
  simp[revDeriv]

@[simp, ftrans_simp]
theorem revDerivUpdate_fst (f : X → Y) (x : X)
  : (revDerivUpdate K f x).1 = f x :=
by
  rfl

@[simp, ftrans_simp]
theorem revDerivUpdate_snd_zero (f : X → Y) (x dx : X)
  : (revDerivUpdate K f x).2 0 dx = dx := 
by
  simp[revDerivUpdate]

@[simp, ftrans_simp]
theorem revDerivUpdate_snd_zero' (f : X → Y) (x : X) (dy : Y)
  : (revDerivUpdate K f x).2 dy 0 = (revDeriv K f x).2 dy := 
by
  simp[revDerivUpdate]


@[simp, ftrans_simp]
theorem revDerivProj_fst (f : X → E) (x : X)
  : (revDerivProj K f x).1 = f x :=
by
  rfl

@[simp, ftrans_simp]
theorem revDerivProj_snd_zero (f : X → E) (x : X) (i : I)
  : (revDerivProj K f x).2 i 0 = 0 := 
by
  simp[revDerivProj]
  conv in (StructLike.make _) => 
    equals (0:E) =>
      apply StructLike.ext
      intro i'; simp
      if h : i=i' then subst h; simp else simp[h]
  simp

@[simp, ftrans_simp]
theorem revDerivProjUpdate_fst (f : X → E) (x : X)
  : (revDerivProjUpdate K f x).1 = f x :=
by
  rfl

@[simp, ftrans_simp]
theorem revDerivProjUpdate_snd_zero (f : X → E) (x dx : X) (i : I)
  : (revDerivProjUpdate K f x).2 i 0 dx = dx := 
by
  simp[revDerivProjUpdate]

@[simp, ftrans_simp]
theorem revDerivProjUpdate_snd_zero' (f : X → Y) (x : X) (dy : Y)
  : (revDerivUpdate K f x).2 dy 0 = (revDeriv K f x).2 dy := 
by
  simp[revDerivUpdate]


--------------------------------------------------------------------------------
-- Lambda calculus rules for revDeriv ------------------------------------------
--------------------------------------------------------------------------------

namespace revDeriv

variable (X)
theorem id_rule 
  : revDeriv K (fun x : X => x) = fun x => (x, fun dx => dx) :=
by
  unfold revDeriv
  funext _; ftrans; ftrans


theorem const_rule (y : Y)
  : revDeriv K (fun _ : X => y) = fun x => (y, fun _ => 0) :=
by
  unfold revDeriv
  funext _; ftrans; ftrans
variable{X}

variable(E)
theorem proj_rule (i : I)
  : revDeriv K (fun (x : (i:I) → EI i) => x i)
    = 
    fun x => 
      (x i, fun dxi j => if h : i=j then h ▸ dxi else 0) :=
by
  unfold revDeriv
  funext _; ftrans; ftrans
variable {E}


theorem comp_rule 
  (f : Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revDeriv K (fun x : X => f (g x))
    = 
    fun x =>
      let ydg := revDeriv K g x
      let zdf := revDeriv K f ydg.1
      (zdf.1,
       fun dz =>
         let dy := zdf.2 dz
         ydg.2 dy)  := 
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDeriv
  funext _; ftrans; ftrans
  rfl

theorem let_rule 
  (f : X → Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : HasAdjDiff K g)
  : revDeriv K (fun x : X => let y := g x; f x y) 
    = 
    fun x => 
      let ydg := revDerivUpdate K g x
      let zdf := revDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz => 
         let dxdy := zdf.2 dz
         let dx := ydg.2 dxdy.2 dxdy.1
         dx)  :=
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDeriv
  funext _; ftrans; ftrans; rfl

theorem pi_rule
  (f :  X → (i : I) → EI i) (hf : ∀ i, HasAdjDiff K (f · i))
  : (revDeriv K fun (x : X) (i : I) => f x i)
    =
    fun x =>
      let xdf := revDerivProjUpdate K f x
      (fun i => xdf.1 i,
       fun dy => Id.run do
         let mut dx : X := 0
         for i in fullRange I do
           dx := xdf.2 ⟨i,()⟩ (dy i) dx
         dx) :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  unfold revDeriv
  funext _; ftrans; ftrans

end revDeriv

--------------------------------------------------------------------------------
-- Lambda calculus rules for revDerivUpdate ------------------------------------
--------------------------------------------------------------------------------
