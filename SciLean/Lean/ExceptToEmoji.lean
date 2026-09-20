import Lean

namespace Lean

class ExceptToEmoji (ε : Type) (α : Type) where
  toEmoji : Except ε α → String

export ExceptToEmoji (toEmoji)

instance (priority := low) {ε α} : ExceptToEmoji ε α where
  toEmoji := fun
    | .ok _ => checkEmoji
    | .error _ => bombEmoji

instance (priority := low + 10) {ε α} : ExceptToEmoji ε (Option α) where
  toEmoji := fun
    | .ok (.some _) => checkEmoji
    | .ok .none => crossEmoji
    | .error _ => bombEmoji

end Lean
