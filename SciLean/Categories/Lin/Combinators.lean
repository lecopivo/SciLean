import SciLean.Std.Function
import SciLean.Categories.Lin.Core

open Function
namespace SciLean.Lin

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

-- id
instance : IsLin (id : X → X) := by simp[id]; infer_instance; done

-- set_option synthInstance.maxHeartbeats 50000
-- const
instance : IsLin (const β : X → β → X) := by simp[const]; infer_instance; done
instance : IsLin (const Y (0 : X) : Y → X) := by simp[const]; infer_instance; done

-- swap
-- instance : IsLin (swap : (α → β → Z) → (β → α → Z)) := by simp[swap] infer_instance done
instance (priority := low) (f : α → Y → Z) [∀ a, IsLin (f a)] : IsLin (swap f) := by simp[swap] infer_instance done
instance (priority := low) (f : X → β → Z) (b : β) [IsLin f] : IsLin (swap f b) := by simp[swap] infer_instance done

-- comp
instance : IsLin (@comp α β Z) := by simp[comp] infer_instance done
instance (f : Y → Z) [IsLin f] : IsLin (@comp α _ _ f) := by simp[comp] infer_instance done
instance (f : Y → Z) (g : X → Y) [IsLin f] [IsLin g] : IsLin (comp f g) := by simp[comp] infer_instance done



