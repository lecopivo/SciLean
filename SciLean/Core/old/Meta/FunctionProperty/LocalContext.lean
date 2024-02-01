import Std.Data.RBMap.Alter
import Std.Data.HashMap

import SciLean.Lean.Meta.Basic
import SciLean.Data.ArraySet

open Lean Meta
open Std

namespace SciLean
namespace FunctionProperty

local instance : Ord (ArraySet Nat) := ⟨ArraySet.lexOrd⟩
local instance : Ord Name := ⟨Name.quickCmp⟩

/--
Function property is either proposition or transformation.
-/
inductive FPType | trans | prop
deriving Ord, BEq, Hashable

structure FProperty where
  name : Name
  type : FPType
deriving Ord, BEq, Hashable

/--
Theorems corresponding to a particular function, arguments and property
-/
structure FPropertyTheorems where
  normalTheorem : Option Expr
  compTheorem : Option Expr
  definition : Option Expr
deriving BEq, Inhabited

/--
This holds properties of a function
-/
def FProperties := Std.RBMap FProperty (Std.RBMap (ArraySet Nat) FPropertyTheorems compare) compare

/--
Function properties about functions in the local context
-/
structure FPropertiesMap where
  properties : Std.HashMap Expr FProperties


def analyzeLCtx (lctx : LocalContext) (localInsts : LocalInstances) : MetaM FPropertiesMap :=
  withLCtx lctx localInsts do
    let mut fprops : FPropertiesMap := ⟨{}⟩
    for decl in lctx do
      -- To understand this code let's work with two examples:
      -- The type of `decl` is:
      -- simple case:  IsSmooth f
      -- complex case: ∀ z, IsSmooth (λ (x,y) => f 0 x y z)

      let F := decl.type.getAppFn
      if let some (propertyName,_) := F.const? then
        let lambda := decl.type.appArg!
        lambdaTelescope lambda λ xs b =>



      sorry
    sorry
