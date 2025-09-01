import Batteries.Data.RBMap.Alter
import Lean
import SciLean.Lean.Array

open Lean

namespace Lean

structure MergeMapDeclarationExtension.Merge (α) where
  merge : Name → α → α → α
  is_valid : ∀ n a b c, merge n (merge n a b) c = merge n a (merge n b c)
             ∧
             ∀ n a b, merge n a b = merge n b a

open MergeMapDeclarationExtension in
/--
Similar to `MapDeclarationExtension` but it allows you have insert declarations that were not declared in the same file.
However, you have to provide how to merge the values and to guarantee consistency i.e. merging should be associative and commutative.
-/
def MergeMapDeclarationExtension (α)
  := PersistentEnvExtension (Name × α) (Name × α) (Batteries.RBMap Name α Name.quickCmp)

open MergeMapDeclarationExtension in
def mkMergeMapDeclarationExtension [Inhabited α] (merge : Merge α) (name : Name := by exact decl_name%)
  : IO (MergeMapDeclarationExtension α) :=
  registerPersistentEnvExtension {
    name          := name
    mkInitial     := pure default
    addImportedFn := fun s =>
      let m := (s.map λ s' => .ofArray s' _) |>.joinl id λ a b => .mergeWith merge.1 a b
      pure m
    addEntryFn    := fun s (n,val') => (s.alter n (λ val? => match val? with | .some val => merge.1 n val val' | none => val'))
    exportEntriesFn := fun s => s.toList.toArray
  }


namespace MergeMapDeclarationExtension


instance : Inhabited (MergeMapDeclarationExtension α) :=
  inferInstanceAs (Inhabited (PersistentEnvExtension ..))

variable {m} [Monad m] [MonadEnv m]

def insert (ext : MergeMapDeclarationExtension α) (declName : Name) (val : α) : m Unit :=
  modifyEnv (λ env => ext.addEntry env (declName, val))

def find? [Inhabited α] (ext : MergeMapDeclarationExtension α) (declName : Name) : m (Option α) := do
  return (ext.getState (← getEnv)).find? declName

def contains [Inhabited α] (ext : MergeMapDeclarationExtension α) (declName : Name) : m Bool := do
  return (ext.getState (← getEnv)).contains declName

end MergeMapDeclarationExtension
