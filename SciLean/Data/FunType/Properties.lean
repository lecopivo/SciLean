import SciLean.Data.FunType.Algebra

namespace SciLean.FunType

variable {T X Y : Type} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] 

-- There are some issues working with `getElem : (x : Cont) → (i : Idx) → Dom x i → Elem`
-- bacause it has inherently dependent types plus `Dom x i : Prop` and 
-- we do not have `Vec (P → X)` for `P : Prop` and `X : Type`

instance getElem.arg_f.isLin [Vec Y]
  : IsLin (λ (f : T) (x : X) => f[x]) := sorry
instance getElem.arg_f.isLin_alt [Vec Y] (x : X)
  : IsLin (λ (f : T) => f[x]) := sorry

instance getElem.arg_f.isSmooth [Vec Y]
  : IsSmooth (λ (f : T) (x : X) => f[x]) := linear_is_smooth _
instance getElem.arg_f.isSmooth_alt [Vec Y] (x : X)  
  : IsSmooth (λ (f : T) => f[x]) := linear_is_smooth _

@[simp ↓] theorem getElem.arg_f.diff_simp [Vec Y]
  : ∂ (λ (f : T) (x : X) => f[x]) = λ f df x => df[x]
  := diff_of_linear _
@[simp ↓] theorem getElem.arg_f.diff_simp_alt [Vec Y] (x : X)
  : ∂ (λ (f : T) => f[x]) = λ f df => df[x]
  := diff_of_linear _


instance getElem.arg_f.hasAdjoint [SemiHilbert Y] (x : X)
  : HasAdjoint (λ (f : T) => f[x]) := sorry
@[simp ↓] theorem getElem.arg_f.adj_simp [SemiHilbert Y] (x : X)
  : (λ (f : T) => f[x])† = λ f' => setElem 0 x f' := sorry

instance getElem.arg_f.hasAdjDiff [SemiHilbert Y] (x : X)
  : HasAdjDiff (λ (f : T) => getElem f x True.intro) := by constructor; infer_instance; simp; infer_instance done
@[simp ↓] theorem getElem.arg_f.adjDiff_simp [SemiHilbert Y] (x : X)
  : ∂† (λ (f : T) => f[x]) = λ _ df' => setElem (0 : T) x df' := by simp[adjointDifferential]; done


-- This unfortunatelly does not solve automatically :( the unification fails
example (x : X) (f : ℝ → T) [Vec Y] [IsSmooth f] 
  : ∂ (λ (s : ℝ) => (f s)[x]) = λ s ds => (∂ f s ds)[x] := 
by 
  rw[diff_of_comp (λ g => getElem g x True.intro) f]; 
  simp; 
  done

---

-- instance setElem.arg_f.isSmooth [Vec Y]
--   : IsSmooth (λ (f : T) (x : X) (y : Y) => setElem f x y) := sorry

-- TODO: for some reason specifying [Vec Y] and [SemiHilbert Y] does not work 
--       after `argument _`

function_properties setElem [Vec Y] (f : T) (x : X) (y : Y) : T
argument f 
  isSmooth := sorry, 
  diff_simp := setElem df x 0 by sorry,
  fwdDiff_simp by (enter [f]; simp [SciLean.fwdDiff])
argument y
  isSmooth := sorry,
  diff_simp := setElem 0 x dy by sorry,
  fwdDiff by (enter[x]; simp [SciLean.fwdDiff])

function_properties setElem [SemiHilbert Y] (f : T) (x : X) (y : Y) : T
argument f 
  hasAdjoint [Fact (y=0)] := sorry,
  adj_simp [Fact (y=0)] := setElem f' x 0 by sorry,
  hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
  adjDiff_simp := setElem df' x 0 by simp[adjointDifferential]; unfold hold; simp done
argument y
  hasAdjoint [Fact (f=0)] := sorry,
  adj_simp [Fact (f=0)] := y'[x] by sorry,
  hasAdjDiff   := by constructor; infer_instance; simp; infer_instance done,
  adjDiff_simp := dy'[x] by simp[adjointDifferential]; done

---

-- This does not work properly. The return type T can't be infered automatically.
-- In the following hand written instanced we have to inscribe `(_ : T)` manually
-- function_properties intro {T X Y : Type} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] (f : X → Y) : T
-- argument f [Vec Y]
--   isLin := sorry

instance intro.arg_f.isLin [Vec Y] 
  : IsLin λ (f : X → Y) => (intro T f) := sorry

instance intro.arg_f.isSmooth [Vec Y] 
  : IsSmooth λ (f : X → Y) => (intro T f) := linear_is_smooth _

@[simp ↓]
theorem intro.arg_f.diff_simp [Vec Y] 
  : (∂ λ (f : X → Y) => (intro T f)) = λ f df => intro T df := diff_of_linear _

@[simp ↓]
theorem intro.arg_f.fwdDiff_simp [Vec Y] 
  : (fwdDiff λ (f : X → Y) => (intro T f)) 
    = 
    λ f => (intro T f, λ df => intro T df) 
  := fwdDiff_of_linear _

instance intro.arg_f.hasAdjoint [SemiHilbert Y] 
  : HasAdjoint λ (f : X → Y) => (intro T f) := sorry

@[simp ↓]
theorem intro.arg_f.adj_simp [SemiHilbert Y] 
  : (λ (f : X → Y) => (intro T f))† = λ f' x => f'[x] := sorry


instance intro.arg_f.hasAdjDiff [SemiHilbert Y] 
  : HasAdjDiff λ (f : X → Y) => (intro T f) := 
by 
  constructor; infer_instance; simp; infer_instance done

@[simp ↓] 
theorem intro.arg_f.adjDiff_simp [SemiHilbert Y] 
  : (∂† λ (f : X → Y) => (intro T f)) = λ f df' x => df'[x] := by simp[adjointDifferential] done

---



-- TODO: modify, mapIdx, map

