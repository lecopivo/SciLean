module

public import SciLean.Algebra.TensorProduct.Basic

@[expose] public section
set_option linter.overlappingInstances false


set_option linter.unusedSectionVars false

open SciLean

macro "variable_vec[" k:term "]" X:ident : command =>
  `(variable {$X :Type*} [NormedAddCommGroup $X] [AdjointSpace $k $X])


open Lean Elab Command Term Meta in
/--
Command `variable_tprod[𝕜] X ⊗ Y` will add to the context all the instances necessary for `X ⊗ Y`

Expands into
```
variable {XY :Type*} [NormedAddCommGroup XY] [AdjointSpace 𝕜 XY] [TensorProductType 𝕜 X Y XY]
         [TensorProductGetYX 𝕜 X Y XY] [TensorProductGetRXY 𝕜 X Y XY]
```
-/
elab "variable_tprod[" k:term "]" X:term:120 "⊗'" Y:term:120 : command => do

  let (x,y) ← runTermElabM fun _ => do
    let xVar ← elabTermAndSynthesize X none
    let yVar ← elabTermAndSynthesize Y none

    unless xVar.isFVar do throwError s!"invalid type {X}"
    unless yVar.isFVar do throwError s!"invalid type {Y}"

    pure (← xVar.fvarId!.getUserName,
          ← yVar.fvarId!.getUserName)

  let X : Ident := mkIdent x
  let Y : Ident := mkIdent y
  let XY : Ident := mkIdent (x.appendAfter y.toString)

  elabCommand (← `(variable {$XY :Type*} [NormedAddCommGroup $XY] [AdjointSpace $k $XY]
      [TensorProductType $k $X $Y $XY]
      [TensorProductGetYX $k $X $Y $XY] [TensorProductGetRXY $k $X $Y $XY]))

variable {𝕜} [RCLike 𝕜]

set_default_scalar 𝕜


section TMap

variable_vec[𝕜] A
variable_vec[𝕜] B
variable_vec[𝕜] C
variable_vec[𝕜] D

variable_tprod[𝕜] A ⊗' B
variable_tprod[𝕜] C ⊗' D

-- variable [TensorProductCurry 𝕜 A B CD]

-- def tmap (f : A →L[𝕜] C) (g : B →L[𝕜] D) : A⊗B →L[𝕜] C⊗D :=
--   tcurry.symm (fun (a : A) =>L[𝕜]'(sorry_proof) fun (b : B) =>L[𝕜]'(sorry_proof) (f a ⊗ g b))


-- set_option linter.unusedSectionVars false in
-- theorem tmap_apply (f : A →L[𝕜] C) (g : B →L[𝕜] D) (a : A) (b : B) :
--   tmap f g (a ⊗ b) = f a ⊗ g b := sorry_proof

end TMap

section SwapLeft

variable_vec[𝕜] A
variable_vec[𝕜] B
variable_vec[𝕜] C

variable_tprod[𝕜] A ⊗' B
variable_tprod[𝕜] B ⊗' A
variable_tprod[𝕜] (A ⊗ B) ⊗' C
variable_tprod[𝕜] (B ⊗ A) ⊗' C

noncomputable
def tswapLeft [TensorProductGetRXY 𝕜 AB C ABC] : (A⊗B)⊗C → (B⊗A)⊗C :=
  tmap (fun x : A⊗B =>L[𝕜] tswap x) (fun x : C =>L[𝕜] x)

set_option linter.unusedSectionVars false in
@[simp, simp_core]
theorem tswapLeft_apply (a : A) (b : B) (c : C) :
  tswapLeft ((a ⊗ b) ⊗ c) = (b ⊗ a) ⊗ c := sorry_proof

@[simp, simp_core]
theorem tswapLeft_tswapLeft (x : (A⊗B)⊗C) :
  tswapLeft (tswapLeft x) = x := by
  have hl : IsLinearMap 𝕜 (fun x : (A⊗B)⊗C => tswapLeft (tswapLeft x)) := by
    unfold tswapLeft; fun_prop
  have key : (fun x : (A⊗B)⊗C => tswapLeft (tswapLeft x)) = fun x => x := by
    apply tmul_ext (R:=𝕜) (Y:=A⊗B) (X:=C) hl (by fun_prop)
    intro ab c
    refine congrFun (tmul_ext (R:=𝕜) (Y:=A) (X:=B)
      (f := fun ab : A⊗B => tswapLeft (tswapLeft (ab ⊗ c))) (g := fun ab => ab ⊗ c)
      ?_ (by fun_prop) (fun a b => by simp)) ab
    unfold tswapLeft; fun_prop
  exact congrFun key x

end SwapLeft



section SwapRight

variable_vec[𝕜] A
variable_vec[𝕜] B
variable_vec[𝕜] C

variable_tprod[𝕜] B ⊗' C
variable_tprod[𝕜] C ⊗' B
variable_tprod[𝕜] A ⊗' (B ⊗ C)
variable_tprod[𝕜] A ⊗' (C ⊗ B)

noncomputable
def tswapRight [TensorProductGetRXY 𝕜 A BC ABC] : A⊗(B⊗C) → A⊗(C⊗B) :=
  tmap (fun x : A =>L[𝕜] x) (fun x : BC =>L[𝕜]'(by fun_prop) tswap x)

@[simp, simp_core]
theorem tswapRigh_apply (a : A) (b : B) (c : C) :
  tswapRight (a ⊗ (b ⊗ c)) = a ⊗ (c ⊗ b) := sorry_proof

@[simp, simp_core]
theorem tswapRight_tswapRight (x : A⊗(B⊗C)) :
  tswapRight (tswapRight x) = x := by
  have hl : IsLinearMap 𝕜 (fun x : A⊗(B⊗C) => tswapRight (tswapRight x)) := by
    unfold tswapRight; fun_prop
  have key : (fun x : A⊗(B⊗C) => tswapRight (tswapRight x)) = fun x => x := by
    apply tmul_ext (R:=𝕜) (Y:=A) (X:=B⊗C) hl (by fun_prop)
    intro a bc
    refine congrFun (tmul_ext (R:=𝕜) (Y:=B) (X:=C)
      (f := fun bc : B⊗C => tswapRight (tswapRight (a ⊗ bc))) (g := fun bc => a ⊗ bc)
      ?_ (by fun_prop) (fun b c => by simp)) bc
    unfold tswapRight; fun_prop
  exact congrFun key x

end SwapRight
