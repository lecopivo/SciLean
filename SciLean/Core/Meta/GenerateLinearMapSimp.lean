import SciLean.Core.FunctionPropositions.IsSmoothLinearMap
import SciLean.Core.Simp

import SciLean.Tactic.FTrans.Init
import SciLean.Tactic.AnalyzeConstLambda

namespace SciLean


section HelperTheorems 

variable 
  {K} [IsROrC K] {X Y Z} [Vec K X] [Vec K Y] [Vec K Z]
  {f : X → Y} (hf : IsLinearMap K f)

theorem _root_.IsLinearMap.add_push (x x' : X)
  : f x + f x' = f (x + x') := by rw[hf.map_add]

theorem _root_.IsLinearMap.add_pull (x x' : X)
  : f (x + x') = f x + f x' := by rw[hf.map_add]

theorem _root_.IsLinearMap.sub_push (x x' : X)
  : f x - f x' = f (x - x') := by rw[hf.map_sub]

theorem _root_.IsLinearMap.sub_pull (x x' : X)
  : f (x - x') = f x - f x' := by rw[hf.map_sub]

theorem _root_.IsLinearMap.smul_push (x : X) (k : K)
  : k • f x = f (k • x) := by rw[hf.map_smul]

theorem _root_.IsLinearMap.smul_pull (x : X) (k : K)
  : f (k • x) = k • f x := by rw[hf.map_smul]

theorem _root_.IsLinearMap.neg_push (x : X)
  : - f x = f (- x) := by rw[hf.map_neg]

theorem _root_.IsLinearMap.neg_pull (x : X)
  : f (- x) = - f x := by rw[hf.map_neg]

theorem _root_.IsLinearMap.app_zero 
  : f 0 = 0 := by rw[hf.map_zero]

variable {g : X → Y → Z} (hg : IsLinearMap K fun xy : X×Y => g xy.1 xy.2)

theorem _root_.IsLinearMap.add_push₂ (x x' : X) (y y' : Y)
  : g x y + g x' y' = g (x + x') (y + y') := 
by 
  have h := hg.map_add (x,y) (x',y')
  simp at h; rw[h]
  
theorem _root_.IsLinearMap.add_pull₂  (x x' : X) (y y' : Y)
  : g (x + x') (y + y') = g x y + g x' y' := 
by 
  have h := hg.map_add (x,y) (x',y')
  simp at h; rw[h]

theorem _root_.IsLinearMap.sub_push₂ (x x' : X) (y y' : Y)
  : g x y - g x' y' = g (x - x') (y - y') := 
by 
  have h := hg.map_sub (x,y) (x',y')
  simp at h; rw[h]
  
theorem _root_.IsLinearMap.sub_pull₂  (x x' : X) (y y' : Y)
  : g (x - x') (y - y') = g x y - g x' y' := 
by 
  have h := hg.map_sub (x,y) (x',y')
  simp at h; rw[h]

theorem _root_.IsLinearMap.smul_push₂ (x : X) (y : Y) (k : K)
  : k • g x y = g (k • x) (k • y) := 
by 
  have h := hg.map_smul k (x,y) 
  simp at h; rw[h]

theorem _root_.IsLinearMap.smul_pull₂ (x : X) (y : Y) (k : K)
  : g (k • x) (k • y) = k • g x y  := 
by 
  have h := hg.map_smul k (x,y) 
  simp at h; rw[h]

theorem _root_.IsLinearMap.neg_push₂ (x : X) (y : Y)
  : - g x y = g (- x) (- y) := 
by
  have h := hg.map_neg (x,y) 
  simp at h; rw[h]

theorem _root_.IsLinearMap.neg_pull₂ (x : X) (y : Y)
  : g (- x) (- y) = - g x y := 
by
  have h := hg.map_neg (x,y) 
  simp at h; rw[h]

theorem _root_.IsLinearMap.app_zero₂
  : g 0 0 = 0 := 
by
  have h := hg.map_zero 
  simp at h; rw[h]
  

end HelperTheorems 


open Lean Meta
def generateLinearMapSimp 
  (ctx : Array Expr) (isLinearMap : Expr) 
  (thrmName : Name) (isSimpAttr : Bool := true) (makeSimp : Bool := false) : MetaM Unit := do

  let f := (← inferType isLinearMap).getArg! 8
  let data ← analyzeConstLambda f

  if data.mainArgs.size > 2 then
    throwError s!"generating simp theorems for linear functions in {data.mainArgs.size} arguments is not supported"

  let mut fullThrmName := (``IsLinearMap).append thrmName
  if data.mainArgs.size = 2 then
    fullThrmName := fullThrmName.appendAfter "₂"
  
  let proof ← mkAppM fullThrmName #[isLinearMap]
  let proof ← mkLambdaFVars ctx proof
  let statement ← inferType proof

  let thrmVal : TheoremVal := 
  {
    name  := data.constName |>.append data.declSuffix |>.append thrmName
    type  := statement
    value := proof
    levelParams := (collectLevelParams {} statement).params.toList
  }

  addDecl (.thmDecl thrmVal)

  if isSimpAttr then
    let .some ext := (← simpExtensionMapRef.get)[thrmName]
      | throwError s!"{thrmName} is not a simp attribute"
    addSimpTheorem ext thrmVal.name false false .global (eval_prio default)

  if makeSimp then
    let .some ext := (← simpExtensionMapRef.get)[`simp]
      | throwError s!"simp is not a simp attribute"
    addSimpTheorem ext thrmVal.name false false .global (eval_prio default)

    let .some ext := (← simpExtensionMapRef.get)[`ftrans_simp]
      | throwError s!"ftrans_simp is not a simp attribute"
    addSimpTheorem ext thrmVal.name false false .global (eval_prio default)


open Lean Meta
/-- Generates bunch of simp theorems given a proof that function is linear.

The provided theorem should be in the simple form `IsLinearMap K (fun x => foo x)` 
Not in the composition form `IsLinearMap K (fun x => foo (f x))`
-/
def generateLinearMapSimps (isLinearMapTheorem : Name) : MetaM Unit := do

  let info ← getConstInfo isLinearMapTheorem

  lambdaTelescope info.value! fun ctx isLinearMap => do
    
    let pullpush := [`add_pull,`add_push,`sub_pull,`sub_push,`smul_pull,`smul_push,`neg_pull,`neg_push]

    for thrm in pullpush do
      generateLinearMapSimp ctx isLinearMap thrm 

    let simps := [`app_zero]

    for thrm in simps do
      generateLinearMapSimp ctx isLinearMap thrm (isSimpAttr:=false) (makeSimp:=true)

syntax (name:=genLinMapSimpsNotation) "#generate_linear_map_simps " ident : command

open Lean Elab Term Command
elab_rules : command 
| `(#generate_linear_map_simps $thrm) => do
  liftTermElabM <| generateLinearMapSimps thrm.getId
