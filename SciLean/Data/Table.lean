import SciLean.Mathlib.Data.Table

import SciLean.Categories
import SciLean.Operators

namespace SciLean.Table

open Table


@[simp]
theorem sum_intro {C ι κ α}
  (f : ι → κ → α) [Table C κ α] [Table.Intro C] [Vec α] [Enumtype ι]
  : (∑ i, (Table.intro (f i) : C)) = (Table.intro (∑ i, f i) : C)
  := 
by
  admit

@[simp]
theorem add_intro {C ι α} [Table C ι α]
  (f g : ι → α) [Table.Intro C] [Vec α] 
  : 
    HAdd.hAdd (self := instHAdd) (Table.intro λ i : ι => f i : C) 
                                 (Table.intro λ i : ι => g i : C) 
    = 
    (Table.intro λ i => f i + g i : C)
  := 
by
  admit


-- section VectorSpace
-- variable {C : Type u} [Trait C] [Table C (Index C) (Value C)] [Intro C]

-- Vector Space
-- instance [AddSemigroup (Value C)] : AddSemigroup C := AddSemigroup.mk sorry
-- instance [AddMonoid (Value C)]    : AddMonoid C    := AddMonoid.mk sorry sorry nsmul_rec sorry sorry
-- instance [AddCommMonoid (Value C)] : AddCommMonoid C := AddCommMonoid.mk sorry
-- instance [SubNegMonoid (Value C)] : SubNegMonoid C := SubNegMonoid.mk sorry gsmul_rec sorry sorry sorry
-- instance [AddGroup (Value C)]     : AddGroup C     := AddGroup.mk sorry
-- instance [AddCommGroup (Value C)] : AddCommGroup C := AddCommGroup.mk sorry

-- instance [Monoid β] [MulAction β (Value C)] : MulAction β C := MulAction.mk sorry sorry
-- instance {M} [AddMonoid (Value C)] [Monoid M] [DistribMulAction M (Value C)] : DistribMulAction M C := DistribMulAction.mk sorry sorry
-- instance {R} [AddCommGroup (Value C)] [Semiring R] [Module R (Value C)] : Module R C := Module.mk sorry sorry

-- set_option synthInstance.maxHeartbeats 3000 in
-- instance [Vec (Value C)] : Vec C := Vec.mk

-- end VectorSpace

----------------------------------------------------------------------

--  {R : outParam $ Type u} {D : outParam $ Type v} {e : outParam $ R → D → ℝ}
-- instance {C R D e} [Trait C] 
--   [Table C (Index C) (Value C)] 
--   [SemiInner (Value C) R D e] 
--   [Zero R] [Add R] [Enumtype (Index C)] 
--   : SemiInner C R D e :=
-- {
--   semiInner := λ x y => (∑ i, ⟪x[i], y[i]⟫)
--   testFunction := λ _ _ => True
-- }

-- instance {C R D e} [Trait C]
--   [Table C (Index C) (Value C)] [Intro C]
--   [SemiInner.Trait (Value C)] [Vec R] [SemiHilbert (Value C) R D e]
--   [Enumtype (Index C)] 
--   : SemiHilbert C R D e :=
-- {
--   semi_inner_add := sorry
--   semi_inner_mul := sorry
--   semi_inner_sym := sorry
--   semi_inner_pos := sorry
--   semi_inner_ext := sorry
-- }


-- instance {C} [Trait C] 
--   [Table C (Index C) (Value C)] 
--   [SemiInner (Value C) ℝ Unit (λ r _ => r)] 
--   [Enumtype (Index C)] 
--   : SemiInner C ℝ Unit (λ r _ => r) :=
-- {
--   semiInner := λ x y => (∑ i, ⟪x[i], y[i]⟫)
--   testFunction := λ _ _ => True
-- }


-- instance {C} [Trait C]
--   [Table C (Index C) (Value C)] [Intro C]
--   [SemiInner.Trait (Value C)] [Hilbert (Value C)]
--   [Enumtype (Index C)] 
--   : Hilbert C :=
-- {
--   semi_inner_add := sorry
--   semi_inner_mul := sorry
--   semi_inner_sym := sorry
--   semi_inner_pos := sorry
--   semi_inner_ext := sorry
-- }

-- #check SciLean.instSemiInner
-- #check SciLean.instSemiHilbert
-- #check SciLean.SemiHilbert.instSemiHilbertArrow

-- example {C} [Trait C] [Table C (Index C) (Value C)] [Enumtype (Index C)] [Intro C]
--   [Hilbert (Value C)]
--   : SemiInner C ℝ Unit (λ r _ => r) := by infer_instance

-- example {C} 
--   [Trait C] [Table C (Index C) (Value C)] [Intro C] [Enumtype (Index C)]
--   [Hilbert (Value C)]
--   : Hilbert C := by infer_instance
 
-- ---------------------------------------------------------------------


-- variable {C} [Trait C] [Table C (Index C) (Value C)] [Table.Intro C]

-- instance (i : (Index C)) [Vec ( Value C)] : IsLin (λ c : C => c[i]) := sorry
-- instance [Vec (Value C)] : IsLin (λ (c : C) (i : (Index C))  => c[i]) := sorry

-- instance (i : (Index C))[Hilbert (Value C)] [Enumtype (Index C)] 
--   : HasAdjoint (λ c : C => c[i]) := sorry

-- example (i : (Index C)) [Hilbert (Value C)] [Enumtype (Index C)] 
--   : HasAdjoint ((λ c : C => c[i])†) := by infer_instance
-- example (i : (Index C)) [Hilbert (Value C)] [Enumtype (Index C)] 
--   : HasAdjoint ((λ c : C => c[i])††) := by infer_instance


--   -- apply Adjoint.instHasAdjointAdjoint



-- set_option trace.Meta.synthInstance true in
-- @[simp]
-- theorem adjoint_of_table_get
--   (i : (Index C)) 
--   [Hilbert (Value C)] 
--   [Enumtype (Index C)] 
--   : (λ (c : C) (i : Index C) => c[i])† = intro :=
-- by 
--   apply Adjoint.inner_ext



-- example : Vec (ℝ × _) := by infer_instance

-- set_option trace.Meta.Tactic.simp true in
-- @[simp]
-- theorem adjoint_of_table_get_at_i {R D e} (i : (Index C)) [Vec R] [SemiHilbert (Value C) R D e] [Enumtype (Index C)]
--   (f : C → Value C) [HasAdjoint f]
--   : f† = 0 :=  -- (λ c : C => c[i])† = λ a => intro (λ j => (kron i j) * a) :=
-- by
--   funext a
--   inner_ext ϕ D h;
--   simp (discharger := assumption)
--   rw[(SciLean.Adjoint.inner_adjoint_fst_left_test _ a ϕ D h)]
--   simp
--   simp
--   simp

