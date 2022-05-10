import SciLean.Prelude
import SciLean.Mathlib.Data.Pi


namespace SciLean

example {α β : Type u} [Add β] : Add (α → β) := by infer_instance


variable {α : Type u} {β : Type v} {γ : Type w}

@[lambdaPush]
theorem lambda_of_add_push [Add β] (f g : α → β) : (λ x => f x + g x) = (λ x => f x) + (λ x => g x) := by funext a; simp; done

@[lambdaPull]
theorem lambda_of_add_pull [Add β] (f g : α → β) : (λ x => f x) + (λ x => g x) = (λ x => f x + g x)  := by funext a; simp; done

@[lambdaPush]
theorem lambda_of_sub [Sub β] (f g : α → β) : (λ x => f x - g x) = (λ x => f x) - (λ x => g x) := by funext a; simp; done

@[lambdaPull]
theorem lambda_of_sub_pull [Sub β] (f g : α → β) : (λ x => f x) - (λ x => g x) = (λ x => f x - g x)  := by funext a; simp; done

@[lambdaPush]
theorem lambda_of_mul [Mul β] (f g : α → β) : (λ x => f x * g x) = (λ x => f x) * (λ x => g x) := by funext a; simp; done

@[lambdaPush]
theorem lambda_of_div [Div β] (f g : α → β) : (λ x => f x / g x) = (λ x => f x) / (λ x => g x) := by funext a; simp; done

-- @[lambdaPush]
-- theorem lambda_of_smul {α β γ : Type} [HMul β γ γ] (f : α → β) (g : α → γ) : (λ x => f x * g x) = (λ x => f x) * (λ x => g x) := by funext a; simp; done
