
import Std.Data.RBMap.Alter
import SciLean.Lean.Array

open Lean 

namespace Lean

structure MergeMapDeclarationExtension.ValidMerge (merge : α → α → α) : Prop where
  assoc : ∀ a b c, merge (merge a b) c = merge a (merge b c)
  comm  : ∀ a b, merge a b = merge b a

open MergeMapDeclarationExtension in
/--
Similar to `MapDeclarationExtension` but it allows you have insert declarations that were not declared in the same file. 
However, you have to provide how to merge the values and to guarantee consistency i.e. merging should be associative and commutative.
-/
def MergeMapDeclarationExtension (α : Type) (merge : Name → α → α → α) (h : ∀ n, ValidMerge (merge n)) 
  := SimplePersistentEnvExtension (Name × α) (Std.RBMap Name α Name.quickCmp)


open MergeMapDeclarationExtension in
def mkMergeMapDeclarationExtension [Inhabited α] (merge : Name → α → α → α) 
  (h : ∀ n, ValidMerge (merge n)) (name : Name := by exact decl_name%)
  : IO (MergeMapDeclarationExtension α merge h) :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun s => (s.map λ s' => .ofArray s' _) |>.joinl id λ a b => a.mergeWith merge b,
    addEntryFn    := fun s (n,val') => s.alter n (λ val? => match val? with | .some val => merge n val val' | none => val'),
    toArrayFn     := fun s => s.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  }

namespace MergeMapDeclarationExtension

variable {α : Type} {merge : Name → α → α → α} {h : ∀ n, ValidMerge (merge n)}

instance : Inhabited (MergeMapDeclarationExtension α merge h) :=
  inferInstanceAs (Inhabited (SimplePersistentEnvExtension ..))

def insert (ext : MergeMapDeclarationExtension α merge h) (env : Environment) (declName : Name) (val : α) : Environment :=
  have : Inhabited Environment := ⟨env⟩
  ext.addEntry env (declName, val)

def find? [Inhabited α] (ext : MergeMapDeclarationExtension α merge h) (env : Environment) (declName : Name) : Option α :=
  match env.getModuleIdxFor? declName with
  | some modIdx =>
    match (ext.getModuleEntries env modIdx).binSearch (declName, default) (fun a b => Name.quickLt a.1 b.1) with
    | some e => some e.2
    | none   => none
  | none => (ext.getState env).find? declName

def contains [Inhabited α] (ext : MergeMapDeclarationExtension α merge h) (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | some modIdx => (ext.getModuleEntries env modIdx).binSearchContains (declName, default) (fun a b => Name.quickLt a.1 b.1)
  | none        => (ext.getState env).contains declName

end MergeMapDeclarationExtension

