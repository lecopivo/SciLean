import SciLean.Analysis.Calculus.ContDiff

namespace SciLean.Diffeology.Util

@[simp]
theorem cast_apply {β β' : α → Type u} (f : (a : α) → β a) (a : α) (h' : ((a : α) → β a) = ((a : α) → β' a)) (h : β = β' := by simp_all) :
  (cast h' f) a = cast (by simp[h]) (f a) := by subst h; simp

@[simp]
theorem cast_smul_cast {α} {X : α → Type u} [∀ a, SMul R (X a)] (a a') (r : R) (x : X a) (h : a = a' := by simp_all) :
  cast (show X a' = X a by simp_all) (r • cast (by simp_all) x) = r • x := by subst h; simp

@[simp]
theorem cast_smul {α} {X : α → Type u} [∀ a, SMul R (X a)] (a a') (r : R) (x : X a) (h : a = a' := by simp_all) :
  cast (show X a = X a' by simp_all) (r • x) = r • cast (by simp_all) x := by subst h; simp


@[simp]
theorem cast_add {α} {X : α → Type u} [∀ a, Add (X a)] (a a') (x y : X a) (h : a = a' := by simp_all) :
  cast (show X a = X a' by simp_all) (x + y) = cast (by simp_all) x + cast (by simp_all) y := by subst h; simp

@[simp]
theorem fst_cast {α α' β β'} (xy : α×β) (h : α = α' := by simp_all) (h' : β = β' := by simp_all) :
    (cast (show (α×β) = (α'×β') from by simp_all) xy).1 = cast (by simp_all) xy.1 := by
  subst h; subst h'; simp

@[simp]
theorem snd_cast {α α' β β'} (xy : α×β) (h : α = α' := by simp_all) (h' : β = β' := by simp_all) :
    (cast (show (α×β) = (α'×β') from by simp_all) xy).2 = cast (by simp_all) xy.2 := by
  subst h; subst h'; simp


def FinAdd.fst (x : Fin (n + m) → ℝ) : Fin n → ℝ := fun i => x ⟨i.1, by omega⟩
def FinAdd.snd (x : Fin (n + m) → ℝ) : Fin m → ℝ := fun i => x ⟨i.1 + n, by omega⟩
def FinAdd.mk (x : Fin n → ℝ) (y : Fin m → ℝ) : Fin (n + m) → ℝ :=
  fun i => if h : i < n then x ⟨i.1, by omega⟩ else y ⟨i.1 - n, by omega⟩

@[simp]
theorem FinAdd.fst_mk (x : Fin n → ℝ) (y : Fin m → ℝ) : fst (mk x y) = x := by
  simp (config:={unfoldPartialApp:=true}) [fst,mk]

@[simp]
theorem FinAdd.snd_mk (x : Fin n → ℝ) (y : Fin m → ℝ) : snd (mk x y) = y := by
  simp (config:={unfoldPartialApp:=true}) [snd,mk]

@[simp]
theorem FinAdd.mk_fst_snd (x : Fin (n + m) → ℝ) : mk (fst x) (snd x) = x := by
  funext i
  simp (config:={unfoldPartialApp:=true}) [fst,snd,mk]
  intro h; congr; omega

-- TODO: move this
@[fun_prop]
theorem dite.arg_te.Differentiable_rule
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (c : Prop) [Decidable c]
    (f : c → X → Y)  (hf : ∀ h, Differentiable ℝ (f h))
    (g : ¬c → X → Y) (hg : ∀ h, Differentiable ℝ (g h)) :
    Differentiable ℝ (fun x => if h : c then f h x else g h x) := by
  split_ifs <;> aesop


-- def_fun_prop FinAdd.fst in x with_transitive : ContDiff ℝ ⊤
-- def_fun_prop FinAdd.snd in x with_transitive : ContDiff ℝ ⊤
-- def_fun_prop FinAdd.mk in x y with_transitive : ContDiff ℝ ⊤
