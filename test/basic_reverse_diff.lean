import SciLean.Basic
import SciLean.Tactic
import SciLean.Operators.Calculus.RevCore

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Hilbert X] [Hilbert Y] [Hilbert Z]
variable {ι κ : Type} [Enumtype ι] [Enumtype κ]

variable {n : Nat} [NonZero n]

-- set_option trace.Meta.Tactic.simp true in
example
  : 𝓑 (λ x : Fin n → Fin 3 → ℝ => ∑ i j, ∥x i - x j∥²)
    = 
    0 := 
by
  simp
  simp
  admit


instance (x y : X) : HasAdjoint λ dx => δ (λ x y : X => x - y) x dx y := 
by 
  simp infer_instance done

instance (x y : X) : HasAdjoint λ dy => δ (λ y : X => x - y) y dy := 
by 
  simp
  infer_instance done


variable (f : (α → (β×(β→α))))

@[simp]
theorem reverse_comp_id {α β : Type} (f : (α → (β×(β→α)))) 
  : f • (λ x => (x, λ dx => dx)) = f := 
by     
  funext x; simp[reverse_comp]
  conv => lhs; enter [2,x]; simp
  done

@[simp]
theorem reverse_id_comp {α β : Type} (f : (α → (β×(β→α)))) 
  : (λ x => (x, λ dx => dx)) • f = f :=
by     
  funext x; simp[reverse_comp]
  conv => lhs; enter [2,x]; simp
  done



example (i j : Fin n) 
  : (𝓑 fun (x : Fin n → X) => x i - x j)
    =
    (fun x : X×X => (x.1 - x.2, fun dx : X => (dx, -dx))) •
      ReverseDiff.reverse_lmap 
        (fun fx : Fin n → X => (fx i, fun (dv : X) k => kron i k * dv)) 
        (fun fx : Fin n → X => (fx j, fun (dv : X) k => kron j k * dv))
   :=
by
  simp
  simp[reverse_diff, Function.uncurry]
  done


-- These collect what needs to be defined for atomic functions


section NN
  variable {X₀ X₁ X₂ X₃ : Type} [Hilbert X₀] [Hilbert X₁] [Hilbert X₂] [Hilbert X₃]
  variable {W₁ W₂ : Type} [Hilbert W₁] [Hilbert W₂] [Hilbert W₃]
  variable (f₁ : W₁ → X₀ → X₁) [IsSmooth f₁] [∀ w, IsSmooth (f₁ w)]
     [∀ w x, HasAdjoint λ dw => δ f₁ w dw x]
     [∀ w x, HasAdjoint λ dx => δ (f₁ w) x dx]
  variable (f₂ : W₂ → X₁ → X₂) [IsSmooth f₂] [∀ w, IsSmooth (f₂ w)]
     [∀ w x, HasAdjoint λ dw => δ f₂ w dw x]
     [∀ w x, HasAdjoint λ dx => δ (f₂ w) x dx]
  variable (f₃ : W₃ → X₂ → X₃) [IsSmooth f₃] [∀ w, IsSmooth (f₃ w)]
     [∀ w x, HasAdjoint λ dw => δ f₃ w dw x]
     [∀ w x, HasAdjoint λ dx => δ (f₃ w) x dx]

     -- [∀ x₀ (x : W₁ × W₂), SciLean.HasAdjoint (SciLean.differential (fun x => f₁ x.1 x₀) x)]
     -- [∀ (x₀ : X₀) (x : W₁ × W₂), SciLean.HasAdjoint (SciLean.differential (fun x => x₀) x)]

  instance (x : W₁ × W₂) : SciLean.HasAdjoint (δ (fun x => x.1) x) := sorry
  instance (x : W₁ × W₂) : SciLean.HasAdjoint (δ (fun x => x.2) x) := sorry


  instance (f : X → W₁×W₂) [IsSmooth f] [HasAdjoint (δ f x)] : SciLean.HasAdjoint (δ (fun x => (f x).1) x) := by simp admit
  instance (f : X → W₁×W₂) [IsSmooth f] [HasAdjoint (δ f x)] : SciLean.HasAdjoint (δ (fun x => (f x).2) x) := by simp admit


  -- instance : ∀ (x : W₁ × W₂ × W₃), SciLean.HasAdjoint (SciLean.differential (fun x => x.2.2) x) := by infer_instance done

  -- set_option trace.Meta.synthInstance true in
  -- instance : IsSmooth (λ ((w₁,w₂,w₃) : W₁ × W₂ × W₃) => w₃) := by  infer_instance 

  @[simp]
  theorem reverse_diff_of_id
    : 𝓑 (λ x : X => x) = λ x => (x, λ dx => dx) := by simp[reverse_diff] done

  @[simp]
  theorem reverse_diff_of_const (y : Y)
    : 𝓑 (λ x : X => y) = λ x => (y, λ dy : Y => (0:X)) := by simp[reverse_diff] done

  @[simp]
  theorem reverse_diff_of_fst
    : 𝓑 (λ xy : X×Y => xy.1) = λ xy => (xy.1, λ dx => (dx, (0:Y))) := by simp[reverse_diff] done

  @[simp]
  theorem reverse_diff_of_snd
    : 𝓑 (λ xy : X×Y => xy.2) = λ xy => (xy.2, λ dy => ((0:X), dy)) := by simp[reverse_diff] done

  @[simp]
  theorem reverse_diff_of_fst_comp (f : X → Y×Z) [IsSmooth f] [∀ x, HasAdjoint (δ f x)]
    : 𝓑 (λ x : X => (f x).1) = (λ yz => (yz.1, λ dy => (dy, (0:Z)))) • 𝓑 f := 
  by 
    funext x; simp[reverse_diff,reverse_comp]
    funext dy; simp
    admit

  @[simp]
  theorem reverse_diff_of_snd_comp (f : X → Y×Z) [IsSmooth f] [∀ x, HasAdjoint (δ f x)]
    : 𝓑 (λ x : X => (f x).2) = (λ yz => (yz.2, λ dz => ((0:Y), dz))) • 𝓑 f :=
  by 
    funext x; simp[reverse_diff,reverse_comp]
    funext dy; simp
    admit

  -- instance : SciLean.IsSmooth fun x => f₂ x.2.1 (f₁ x.1 x₀)
  -- set_option trace.Meta.synthInstance true in
  -- set_option maxHeartbeats 1000000 in
  -- set_option synthInstance.maxHeartbeats 500000 in
  set_option synthInstance.maxSize 20480 in
  -- set_option trace.Meta.Tactic.simp.discharge true in
  example (x₀ : X₀)
    -- : 𝓑 (λ (w₁,w₂,w₃) => x₀ |> f₁ w₁ |> f₂ w₂ |> f₃ w₃) = 0 :=
    : 𝓑 (λ (w₁,w₂,w₃) => x₀ |> f₁ w₁ |> f₂ w₂ |> f₃ w₃) = 0 :=
  by
    simp
    conv =>
      lhs
      conv =>
        enter [2,1]
        simp [reverse_comp, Function.comp]
      conv =>
        enter [2,2,2,1]
        simp [reverse_comp, Function.comp]
      conv =>
        enter [2,2,2,2,2]
        simp [reverse_comp, Function.comp, ReverseDiff.reverse_lmap]
    . 
    -- simp (config := {singlePass := true})

    -- simp[reverse_diff,Function.uncurry]
    -- -- unfold hold
    -- unfold_atomic
    -- simp[AtomicAdjointFun.adj,ReverseDiff.reverse_lmap]
    -- unfold hold

    unfold hold
    admit

end NN

#check Sigma

structure HArray (Ts : List Type) where
  data : Array (Sigma (λ T : Type => T))
  h_len : Ts.length = data.size
  typed : ∀ i : Fin Ts.length, (data.get (h_len ▸ i)).1 = Ts.get i

namespace HArray

  variable {n} {Ts : List Type}

  def get (u : HArray Ts) (i : Fin Ts.length) : Ts.get i
    := u.typed i ▸ (u.data.get (u.h_len ▸ i)).2

  def getOp (self : HArray Ts) (idx : Fin Ts.length) : Ts.get idx
    := self.typed idx ▸ (self.data.get (self.h_len ▸ idx)).2

  def set (u : HArray Ts) (i : Fin Ts.length) (x : Ts.get i) : HArray Ts
    := ⟨u.data.set (u.h_len ▸ i) (⟨_, x⟩), sorry, sorry⟩

end HArray

class HCurryType (n : Nat) (F : Type) where
  Xs : List Type
  Y  : Type

attribute [reducible] HCurryType.Xs HCurryType.Y

@[reducible]
instance : HCurryType 0 Y where
  Xs := []
  Y := Y

@[reducible]
instance [t : HCurryType n Y] : HCurryType (n + 1) (X → Y) where
  Xs := X::t.Xs
  Y := t.Y

class HCurryImpl (i : Nat) (Xs' Xs : List Type) (Y : Type) where
  index_valid : Xs'.length + i = Xs.length
  types_valid : ∀ j, i + j < Xs.length → Xs'.get ⟨j, sorry⟩ = Xs.get ⟨i + j, sorry⟩
  G : Type
  uncurry : G → (HArray Xs → Y)

attribute [reducible] HCurryImpl.G HCurryImpl.uncurry

@[reducible]
instance (Xs : List Type) (Y : Type) : HCurryImpl n [] Xs Y where
  index_valid := sorry
  types_valid := sorry
  G := Y
  uncurry := λ y xs => y

@[reducible]
instance [c : HCurryImpl (i+1) (Xs') Xs Y] : HCurryImpl (i) (X'::Xs') Xs Y where
  index_valid := sorry
  types_valid := sorry
  G := X' → c.G
  uncurry := λ f xs => 
    let h : (Xs.get ⟨i,sorry⟩ = X') := sorry
    let xi : X' := (h ▸ xs[⟨i,sorry⟩])
    c.uncurry (f xi) xs

def huncurry (n : Nat) {F : Type} [HCurryType n F] 
  [ci : HCurryImpl 0 (HCurryType.Xs n F) (HCurryType.Xs n F) (HCurryType.Y n F)] 
  (f : F) := 
    let h : F = ci.G := sorry
    ci.uncurry (h ▸ f)

example : huncurry 3 (λ (i j k : Nat) => i + j) 
          = 
          λ xs => xs[⟨0, by decide⟩] + xs[⟨1, by decide⟩] := by simp[huncurry]

