import SciLean.Data.IndexType.Basic

namespace SciLean

open IndexType

/--
`IndexEquiv I J` is and equivalence between two index types that preserves the linear index.
In other works, for `i : I` the linear index `toFin i`/`toIdx i` is equal to the linear index of
`f i` for `f : IndexEquiv I J`.
-/
structure IndexEquiv (I J : Type*) {n} [IndexType I n] [IndexType J n]
  extends I ≃ J
  where
  toFin_toFun : ∀ i, (toFin (toFun i)).1 = (toFin i).1

namespace IndexEquiv

variable {I J : Type*} {n} [IndexType I n] [IndexType J n]

section coe

instance : EquivLike (IndexEquiv I J) I J where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    apply Equiv.coe_fn_injective h₁

instance : CoeFun (IndexEquiv I J) fun _ ↦ I → J where
  coe f := f

@[ext]
theorem ext {f g : IndexEquiv I J} (h : ∀ i, f i = g i) : f = g :=
  DFunLike.ext f g h

protected theorem congr_arg {f : IndexEquiv I J} {i i' : I} : i = i' → f i = f i' :=
  DFunLike.congr_arg f

protected theorem congr_fun {f g : IndexEquiv I J} (h : f = g) (i : I) : f i  = g i :=
  DFunLike.congr_fun h i

@[simp]
theorem coe_mk (f : I ≃ J) (hf : ∀ i, (toFin (f i)).1 = (toFin i).1) : (mk f hf : I → J) = f := rfl

@[simp]
theorem mk_coe (e : IndexEquiv I J) (e' h₁ h₂ h₃) : (⟨⟨e, e', h₁, h₂⟩, h₃⟩ : IndexEquiv I J) = e :=
  ext fun _ => rfl

@[simp]
theorem toEquiv_eq_coe (f : IndexEquiv I J) : f.toEquiv = f :=
  rfl

@[simp]
theorem coe_toEquiv (f : IndexEquiv I J) : ⇑(f : I ≃ J) = f := rfl

end coe

section bijective

protected theorem bijective (e : IndexEquiv I J) : Function.Bijective e :=
  EquivLike.bijective e

protected theorem injective (e : IndexEquiv I J) : Function.Injective e :=
  EquivLike.injective e

protected theorem surjective (e : IndexEquiv I J) : Function.Surjective e :=
  EquivLike.surjective e

theorem apply_eq_iff_eq (e : IndexEquiv I J) {x y : I} : e x = e y ↔ x = y :=
  e.injective.eq_iff

end bijective

section refl

/-- The identity map is a multiplicative isomorphism. -/
@[refl]
def refl (I : Type*) [IndexType I n] : IndexEquiv I I :=
  { Equiv.refl _ with toFin_toFun := by simp }

instance : Inhabited (IndexEquiv I I) := ⟨refl I⟩

@[simp]
theorem coe_refl : ↑(refl I) = id := rfl

@[simp]
theorem refl_apply (i : I) : refl I i = i := rfl

end refl

section symm

@[symm]
def symm (h : IndexEquiv I J) : IndexEquiv J I :=
  ⟨h.toEquiv.symm, by
   let p := fun (j : J) => (toFin (h.toEquiv.symm.toFun j)).1 = (toFin j).1
   have hh := (Function.Surjective.forall h.surjective (p:=p)).2
   simp [p] at hh
   apply hh
   intro i; exact (h.toFin_toFun i).symm⟩

theorem invFun_eq_symm {f : IndexEquiv I J} : f.invFun = f.symm := rfl

@[simp]
theorem coe_toEquiv_symm (f : IndexEquiv I J) : ((f : I ≃ J).symm : J → I) = f.symm := rfl

@[simp]
theorem equivLike_inv_eq_symm (f : IndexEquiv I J) : EquivLike.inv f = f.symm := rfl

@[simp]
theorem toEquiv_symm (f : IndexEquiv I J) : (f.symm : J ≃ I) = (f : I ≃ J).symm := rfl

@[simp]
theorem symm_symm (f : IndexEquiv I J) : f.symm.symm = f := rfl

theorem symm_bijective : Function.Bijective (symm : (IndexEquiv I J) → IndexEquiv J I) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem mk_coe' (e : IndexEquiv I J) (f h₁ h₂ h₃) : (IndexEquiv.mk ⟨f, e, h₁, h₂⟩ h₃ : IndexEquiv J I) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl

@[simp]
theorem refl_symm : (refl I).symm = refl I := rfl

@[simp]
theorem apply_symm_apply (e : IndexEquiv I J) (j : J) : e (e.symm j) = j :=
  e.toEquiv.apply_symm_apply j

@[simp]
theorem symm_apply_apply (e : IndexEquiv I J) (i : I) : e.symm (e i) = i :=
  e.toEquiv.symm_apply_apply i

@[simp]
theorem symm_comp_self (e : IndexEquiv I J) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[simp]
theorem self_comp_symm (e : IndexEquiv I J) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

theorem apply_eq_iff_symm_apply (e : IndexEquiv I J) {i : I} {j : J} : e i = j ↔ i = e.symm j :=
  e.toEquiv.apply_eq_iff_eq_symm_apply

theorem symm_apply_eq (e : IndexEquiv I J) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

theorem eq_symm_apply (e : IndexEquiv I J) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

theorem eq_comp_symm {α : Type*} (e : IndexEquiv I J) (f : J → α) (g : I → α) :
    f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

theorem comp_symm_eq {α : Type*} (e : IndexEquiv I J) (f : J → α) (g : I → α) :
    g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g

theorem eq_symm_comp {α : Type*} (e : IndexEquiv I J) (f : α → I) (g : α → J) :
    f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g

theorem symm_comp_eq {α : Type*} (e : IndexEquiv I J) (f : α → I) (g : α → J) :
    e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g

end symm
