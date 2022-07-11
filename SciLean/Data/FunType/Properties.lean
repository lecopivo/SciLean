import SciLean.Data.FunType.Algebra
import SciLean.Core.Functions

namespace SciLean.FunType

function_properties toFun {T X Y : Type} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] (f : T) (x : X) : Y
argument f [Vec Y]
  isLin := sorry,
  isSmooth, diff_simp
argument f [SemiHilbert Y]
  hasAdjoint := sorry,
  adj_simp := set (0 : T) x f' by sorry,
  hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
  adjDiff_simp := set (0 : T) x df' by simp[adjDiff]; unfold hold; simp done

---

function_properties set {T X Y : Type} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] (f : T) (x : X) (y : Y) : T
argument f [Vec Y]
  isSmooth := sorry, 
  diff_simp := set df x 0 by sorry
argument f [SemiHilbert Y]
  hasAdjoint [Fact (y=0)] := sorry,
  adj_simp [Fact (y=0)] := set f' x 0 by sorry,
  hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
  adjDiff_simp := set df' x 0 by simp[adjDiff]; unfold hold; simp done

argument y [Vec Y]
  isSmooth := sorry,
  diff_simp := set 0 x dy by sorry
argument y [SemiHilbert Y]
  hasAdjoint [Fact (f=0)] := sorry,
  adj_simp [Fact (f=0)] := toFun y' x by sorry,
  hasAdjDiff   := by constructor; infer_instance; simp; infer_instance done,
  adjDiff_simp := toFun dy' x by simp[adjDiff]; done

---

-- This does not work properly. The return type T can't be infered automatically.
-- In the following hand written instanced we have to inscribe `(_ : T)` manually
-- function_properties intro {T X Y : Type} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] (f : X → Y) : T
-- argument f [Vec Y]
--   isLin := sorry

instance intro.arg_f.isLin {T X Y : Type} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] [Vec Y] 
  : IsLin λ (f : X → Y) => (intro f : T) := sorry

instance intro.arg_f.isSmooth {T X Y : Type} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] [Vec Y] 
  : IsSmooth λ (f : X → Y) => (intro f : T) := linear_is_smooth _

@[simp ↓]
theorem intro.arg_f.diff_simp {T X Y : Type} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] [Vec Y] 
  : (δ λ (f : X → Y) => (intro f : T)) = λ f df => intro df := diff_of_linear _

instance intro.arg_f.hasAdjoint {T X Y : Type} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] [SemiHilbert Y] 
  : HasAdjoint λ (f : X → Y) => (intro f : T) := sorry

@[simp ↓]
theorem intro.arg_f.adj_simp {T X Y : Type} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] [SemiHilbert Y] 
  : (λ (f : X → Y) => (intro f : T))† = λ f' x => toFun f' x := sorry

instance {T X Y : Type} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] [SemiHilbert Y] 
  : HasAdjoint λ (f : X → Y) => (intro f : T) := sorry

instance {T X Y : Type} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] [SemiHilbert Y] 
  : HasAdjDiff λ (f : X → Y) => (intro f : T) := 
by 
  constructor; infer_instance; simp; infer_instance done

@[simp ↓] 
theorem intro.arg_f.adjDiff_simp {T X Y : Type} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] [SemiHilbert Y] 
  : (δ† λ (f : X → Y) => (intro f : T)) = λ f df' x => toFun df' x := by simp[adjDiff] done

---



-- TODO: modify, mapIdx, map
