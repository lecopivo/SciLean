import SciLean.Linear.Basic
import SciLean.Linear.Combinators
import SciLean.Invert


-- -- set_option trace.Meta.synthInstance true
-- -- set_option synthInstance.maxHeartbeats 500

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {U V W : Type} [Hilbert U] [Hilbert V] [Hilbert W]

instance (f : X → Y) [IsLin f] : IsLin (f†) := sorry

@[simp] def adjoint_inner_1 (f : U → V) [IsLin f] (u : U) (v : V) : ⟨f† v, u⟩ = ⟨v, f u⟩ := sorry
@[simp] def adjoint_inner_2 (f : U → V) [IsLin f] (u : U) (v : V) : ⟨u, f† v⟩ = ⟨f u, v⟩ := sorry

@[simp] def diag_adjoint {n} (f : Fin n → X) : adjoint diag f = λ i j => if (i==j) then f i else 0 := sorry

@[simp] def dual_of_zero {X} [Vec X] : dual (const X 0) = 0 := sorry

@[simp] def dual_on_reals (f : ℝ → ℝ) [IsLin f] : dual f = f 1 := sorry

@[simp] def innefr_of_dualla (f : X → ℝ) (x : X) [IsLin f] : ⟨dual f, x⟩ = f x := sorry

@[simp] def hmul_adjoint (c : ℝ) : †(HMul.hMul c) = HMul.hMul c := by funext w; apply inner.ext; intro w; simp; admit --almost done

@[simp] def hmul_adjoint_2 (c : ℝ) : †(swap HMul.hMul c) = HMul.hMul c := by funext w; apply inner.ext; intro w; simp; admit --almost done

@[simp] def comp_dual (f : Y → ℝ) (g : X → Y) [IsLin f] [IsLin g] : dual (comp f g) = †g (dual f) := sorry 
@[simp] def comp_adjoint (f : Y → Z) (g : X → Y) [IsLin f] [IsLin g] : †(comp f g) = comp †g †f := by funext w; apply inner.ext; intro; simp 
@[simp] def comp_adjoint_on_snd_arg (f : X → Y → Z) (g : U → X) (y : Y) [IsLin g] [IsLin f] [IsLin (swap f y)] : †(swap (comp f g) y) = comp (†g) (†(swap f y)) := 
by funext w; apply inner.ext; intro; simp 
@[simp] def comp_dual_on_snd_arg (f : X → Y → ℝ) (g : U → X) (y : Y) [IsLin g] [IsLin f] [IsLin (swap f y)] : dual (swap (comp f g) y) = †g (dual (swap f y)) := 
by apply inner.ext; intro; simp; done

-- @[simp] def comp_adjoint_on_snd_arg (f : ℝ → Z → Y) (g : X → ℝ) (z : Z) [IsLin g] [IsLin f] [IsLin (swap f z)] : †(swap (comp f g) z) = (swap (comp HMul.hMul †(swap f z)) (dual g)) := 
-- by admit


@[simp] def adjoint_of_sum (f g : X → Y) [IsLin f] [IsLin g] : †(subs (comp HAdd.hAdd f) g) = (subs (comp HAdd.hAdd (†f)) (†g)) := 
by funext w; apply inner.ext; intro; simp; admit -- almost ther

@[simp] def dual_of_sum (f g : U → ℝ) [IsLin f] [IsLin g] : dual (subs (comp HAdd.hAdd f) g) = (dual f) + (dual g) := by apply inner.ext; intro; simp; admit


@[simp] def inner.adjoint_1 (x : X) (c : ℝ) : †(Inner.inner x) c = c * x := sorry
@[simp] def inner.adjoint_2 (x : X) (c : ℝ) : †(swap Inner.inner x) c = c * x := sorry

@[simp] def Prod.fst.adjoint : †(Prod.fst : X×Y → X) = (swap Prod.mk) (0 : Y) := sorry
@[simp] def Prod.snd.adjoint : †(Prod.snd : X×Y → Y) = Prod.mk (0 : X) := sorry


 -- (dual
 --                (swap
 --                  (comp HMul.hMul
 --                    (comp (HMul.hMul (k / 2))
 --                      (subs (comp HAdd.hAdd (swap (comp Inner.inner Prod.fst) x.fst))
 --                        (comp (Inner.inner x.fst) Prod.fst))))



-- variable (f : ℝ → Z → Y) (g : X → ℝ) (x : X) (z : Z) (y : Y)



-- #check (†(swap f z) y) * (dual g)


-- def foo  (f : ℝ → Z → Y) (g : X → ℝ) (z : Z):  †(swap (comp f g) z) = (swap (comp HMul.hMul †(swap f z)) (dual g)) := by admit

-- def hihi : (λ y : Y => (†(swap f z) y) * (dual g) )= (λ y => (0 :X))  :=
-- by
--   rmlamlet
  



-- #check  (comp HMul.hMul †(swap f z))

-- #check (†(swap f z) (1 : ℝ)) * (dual g)


-- #check comp †g †(swap f y) 

-- def adjoint {U V} : (U → V) → (V → U) := sorry

-- prefix:120 "†" => adjoint

-- namespace adjoint

-- variable {U V W} [Hilbert U] [Hilbert V] [Hilbert W] -- [Vec U] [Vec V] [Vec W] [Inner U] [Inner V] [Inner W]

-- @[simp] def definition (f : U → V) (u : U) (v : V) [IsLin f] : ⟨adjoint f v, u⟩ = ⟨v, f u⟩ := sorry

-- @[simp] def comp (f : V → W) (g : U → V) [IsLin f] [IsLin g] : †(comp f g) = comp (†g) (†f) := 
-- by 
--   funext u; apply inner.ext; intros; simp

-- @[simp] def inner (u : U) (c : ℝ) : adjoint (Inner.inner u : U → ℝ) c = c * u := 
-- by
--   apply inner.ext; intros; simp; rw [← inner.mul]

-- end adjoint


