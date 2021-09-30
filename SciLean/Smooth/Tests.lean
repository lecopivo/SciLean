import SciLean.Linear
import SciLean.Smooth

import SciLean.Meta

variable {α β γ : Type} 
variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {U : Type} {V : Type} {W : Type} [Hilbert U] [Hilbert V] [Hilbert W]


section 
variable (c d : ℝ) (x dx : X) (y z : X)
def dtest1 : IsDiff ((subs (comp HAdd.hAdd (swap HAdd.hAdd y)) id) : X → X) := by infer_instance; done
def dtest2 : IsDiff ((subs (comp HAdd.hAdd (HAdd.hAdd y)) id) : X → X) := by infer_instance; done
def dtest3 : IsDiff ((subs HMul.hMul id) : ℝ → ℝ) := by infer_instance; done
def dtest4 : IsDiff ((HMul.hMul c) : ℝ → ℝ) := by infer_instance; done
end

section
variable (c d : ℝ) (x dx : X) (y z : X)
def xtest1 : δ (λ x : X => x) x dx = dx := by rmlamlet; simp; done
def xtest2 : δ (λ x : X => c * x) x dx = c * dx := by rmlamlet; simp; done
def xtest3 : δ (λ x : X => x + y) x dx = dx := by rmlamlet; simp; done 
def xtest4 : δ (λ x : X => x + x) x dx = dx + dx := by rmlamlet; simp; done
def xtest5 : δ (λ x : X => c * x + d * x + y) x dx = c * dx + d * dx := by rmlamlet; simp; done
def xtest6 : δ (λ x : X => c * x + y + d * x) x dx = c * dx + d * dx := by rmlamlet; simp; done
def xtest7 : δ (λ x : X => y + c * x + d * x) x dx = c * dx + d * dx := by rmlamlet; simp; done
end

section
variable (c x dx : ℝ)
def rtest1 : δ (λ x : ℝ => c * x) x dx = c * dx := by rmlamlet; simp; done
def rtest2 : δ (λ x : ℝ => x * x) x dx = dx * x + x * dx := by rmlamlet; simp; done
def rtest3 : δ (λ x : ℝ => x * x * x) x dx = (dx * x + x * dx) * x + x * x * dx := by rmlamlet; simp; done
def rtest4 : δ (λ x : ℝ => x * (x * x) * x) x dx = (dx * (x * x) + x * (dx * x + x * dx)) * x + x * (x * x) * dx := by rmlamlet; simp; done
end

section 
variable (f : X → X) (c : ℝ → X) [IsDiff f] [IsDiff c]
variable (t : ℝ) 
def ddtest1 : ⅆ (comp f c) t = δ f (c t) (ⅆ c t) := by simp; done
def ddtest2 : ⅆ (comp f (comp f c)) t = δ f (f (c t)) (δ f (c t) (ⅆ c t)) := by simp; done
def ddtest3 : ⅆ (comp (comp f f) c) t = δ f (f (c t)) (δ f (c t) (ⅆ c t)) := by simp; done
end


section 
variable (x dx y : U)
def htest1 : δ (λ x => ⟨x, y⟩) x dx = ⟨dx, y⟩ := by rmlamlet; simp; done
def htest2 : δ (λ x => ⟨x, x⟩) x dx = ⟨dx, x⟩ + ⟨x, dx⟩ := by rmlamlet; simp; done
def htest3 : δ (λ x => ⟨x, ⟨x,x⟩*x⟩) x dx = ⟨dx, ⟨x,x⟩*x⟩ + ⟨x, dx⟩ := by rmlamlet; simp; done

end
