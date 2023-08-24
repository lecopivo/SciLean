namespace SciLean

structure ExactSolution {α} (p : α → Prop) where
  val : α
  property : p val


def Impl {α} (a : α) := ExactSolution (fun x => x = a)
def Impl.val {α} {a : α} (impl : Impl a) : α := ExactSolution.val impl
def Impl.property {α} {a : α} (impl : Impl a) : impl.val = a := ExactSolution.property impl
def Impl.exact {α} {a : α} : Impl a := ExactSolution.mk a (by rfl)


instance {α} (a : α) : CoeHead (Impl a) α := ⟨fun impl => impl.val⟩
instance {α β} (f : α → β) : CoeFun (Impl f) (fun _ => α → β) := ⟨fun impl => impl.val⟩
