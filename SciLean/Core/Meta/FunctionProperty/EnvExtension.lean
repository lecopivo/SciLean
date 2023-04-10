import Std.Data.RBMap.Alter

import SciLean.Lean.MergeMapDeclarationExtension
import SciLean.Lean.Meta.Basic
import SciLean.Data.ArraySet

import SciLean.Prelude

open Lean Meta Std

namespace SciLean


namespace FunctionProperty

local instance : Ord (ArraySet Nat) := ⟨ArraySet.lexOrd⟩
local instance : Ord Name := ⟨Name.quickCmp⟩


structure Theorems where
  normalTheorem : Option Name
  compTheorem : Option Name
  definition : Option Name
deriving BEq, Inhabited

/-- 
This holds a collection of property theorems for a fixed 
-/
def FProperty := Std.RBMap Name (Std.RBMap (ArraySet Nat) Theorems compare) compare

namespace FProperty

  instance : Inhabited FProperty := by unfold FProperty; infer_instance

  variable (fp : FProperty)

  def insert (property : Name) (argIds : ArraySet Nat) (thrms : Theorems) : FProperty := 
    fp.alter property (λ p? =>
      match p? with
      | some p => some (p.insert argIds thrms)
      | none => some (Std.RBMap.empty.insert argIds thrms))

  def empty : FProperty := Std.RBMap.empty

end FProperty


private def merge! (function : Name) (fp fp' : FProperty) : FProperty :=
  fp.mergeWith (t₂ := fp') λ property p q => 
    p.mergeWith (t₂ := q) λ args thrms thrms' =>
      if thrms == thrms' then 
        thrms
      else 
        panic! 
s!"Two conflicting function properties for
  function: `{function}`
  property: `{property}`
  arguments: `{args}`
  
  option 1:
  normal theorem: `{thrms.normalTheorem}`
  composition theorem: `{thrms.compTheorem}`

  option 2:
  normal theorem: `{thrms'.normalTheorem}`
  composition theorem: `{thrms'.compTheorem}`

  Keep only one and remove the other."


initialize FunctionPropertyExt : MergeMapDeclarationExtension FProperty 
  ← mkMergeMapDeclarationExtension ⟨merge!, sorry_proof⟩

variable {m} [Monad m] [MonadEnv m] [MonadError m]

/--
The calling convention for composition theorem is that if we have a fucntion with 
`n` explicit arguments, i.e. `function x₁ .. xₙ`, then `compTheorem y₁ .. yₙ` where
the type of `yᵢ` is `T → Xᵢ` for `i ∈ argIds` and `Xᵢ` for `i ∉ argIds`
-/
def checkCompTheoremCallingConvention 
  (function : Name) (argIds : ArraySet Nat) (compTheorem : Name) : m Unit := do
  let fArgIds ← getConstExplicitArgIds function
  let tArgIds ← getConstExplicitArgIds compTheorem

  if fArgIds.size ≠ tArgIds.size then 
    throwError s!"Failed checking composition theorem calling convention!\nComposition theorem `{compTheorem}` has to have the same number of explicit arguments as the function `{function}`!"

  if ¬(argIds ⊆ fArgIds.toArraySet) then
    throwError s!"Failed checking composition theorem calling convention!\nSpecified argument ids `{argIds}` have to be a subset of explicit argument ids `{fArgIds}`!"

  -- TODO: Check that specified arguments have the correct types

  -- let T : Expr := .. somehow find out what `T` is

  -- for i in [0:fArgIds.size] do
  
  --   let fi := fArgIds[i]!
  --   let ti := fArgIds[i]!

  --   let Xᵢ ← inferType xᵢ
  --   let Yᵢ ← inferType yᵢ

  --   if fi ∈ argIds then 
  --     if Xᵢ ≠ mkArrow T Yᵢ then
  --       throwError ".."
  --   else
  --     if Xᵢ ≠ Yᵢ then
  --       throwError ".."

  pure ()

def addFunctionProperty (function property : Name) (argIds : ArraySet Nat) 
  (normalTheorem compTheorem definition : Option Name) : m Unit := do

  if let .some thrm := compTheorem then
    checkCompTheoremCallingConvention function argIds thrm

  FunctionPropertyExt.insert function 
    (FProperty.empty.insert property argIds ⟨normalTheorem, compTheorem, definition⟩)

def getFunctionProperty (function property : Name) 
  : m (Option (Std.RBMap (ArraySet Nat) Theorems compare)) := 
do
  let some properties ← FunctionPropertyExt.find? function
    | return none

  let some propMap := properties.find? property
    | return none

  return propMap
  


def printFunctionProperties (function : Name) : CoreM Unit := do
  if let .some fp ← FunctionPropertyExt.find? function then
    IO.println s!"Function properties of `{function}`"
    fp.forM λ property p => do
      IO.println s!"  Property `{property}` holds in arguments:"
      p.forM λ argIds ⟨nt,ct,d?⟩ => do
        match d? with
        | some d => IO.println s!"    {argIds}: `{nt}` `{ct}` `{d}`"
        | none =>   IO.println s!"    {argIds}: `{nt}` `{ct}`"
  else
    IO.println s!"No function properties found for `{function}`."

end  FunctionProperty

export FunctionProperty (FunctionPropertyExt addFunctionProperty getFunctionProperty printFunctionProperties)

