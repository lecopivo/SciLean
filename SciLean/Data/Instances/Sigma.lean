module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Tactic.ProxyType

public import SciLean.Analysis.AdjointSpace.Basic

public import SciLean.Util.SorryProof
public import SciLean.Util.RewriteBy

@[expose] public section


set_option linter.unusedVariables false

----------------------------------------------------------------------------------------------------
-- Operations --------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance {X Y : Type*} [Add X] [Add Y] : Add ((_ : X) × Y) where
  add | ⟨x1, y1⟩, ⟨x2, y2⟩ => ⟨x1 + x2, y1 + y2⟩

instance {X Y : Type*} [Sub X] [Sub Y] : Sub ((_ : X) × Y) where
  sub | ⟨x1, y1⟩, ⟨x2, y2⟩ => ⟨x1 - x2, y1 - y2⟩

instance {X Y : Type*} [Mul X] [Mul Y] : Mul ((_ : X) × Y) where
  mul | ⟨x1, y1⟩, ⟨x2, y2⟩ => ⟨x1 * x2, y1 * y2⟩

instance {X Y : Type*} [Div X] [Div Y] : Div ((_ : X) × Y) where
  div | ⟨x1, y1⟩, ⟨x2, y2⟩ => ⟨x1 / x2, y1 / y2⟩

instance {X Y : Type*} [Neg X] [Neg Y] : Neg ((_ : X) × Y) where
  neg | ⟨x, y⟩ => ⟨-x, -y⟩

instance {X Y : Type*} [Inv X] [Inv Y] : Inv ((_ : X) × Y) where
  inv | ⟨x, y⟩ => ⟨x⁻¹, y⁻¹⟩

instance {X Y : Type*} [Zero X] [Zero Y] : Zero ((_ : X) × Y) where
  zero := ⟨0, 0⟩

instance {X Y : Type*} [One X] [One Y] : One ((_ : X) × Y) where
  one := ⟨1, 1⟩

instance {R X Y : Type*} [SMul R X] [SMul R Y] : SMul R ((_ : X) × Y) where
  smul r | ⟨x, y⟩ => ⟨r • x, r • y⟩

instance {X Y : Type*} [Norm X] [Norm Y] : Norm ((_ : X) × Y) where
  norm := fun ⟨a,b⟩ => ‖a‖ ⊔ ‖b‖

instance {R X Y : Type*} [Add R] [Inner R X] [Inner R Y] : Inner R ((_ : X) × Y) where
  inner := fun ⟨a,b⟩ ⟨c,d⟩ => Inner.inner (𝕜:=R) a c + Inner.inner (𝕜:=R) b d


@[instance_reducible]
def Add.ofEquiv {X Y : Type*} [Add X] (f : X ≃ Y) : Add Y where
  add a b := f (f.symm a + f.symm b)

@[instance_reducible]
def Sub.ofEquiv {X Y : Type*} [Sub X] (f : X ≃ Y) : Sub Y where
  sub a b := f (f.symm a - f.symm b)

@[instance_reducible]
def Mul.ofEquiv {X Y : Type*} [Mul X] (f : X ≃ Y) : Mul Y where
  mul a b := f (f.symm a * f.symm b)

@[instance_reducible]
def Div.ofEquiv {X Y : Type*} [Div X] (f : X ≃ Y) : Div Y where
  div a b := f (f.symm a / f.symm b)

@[instance_reducible]
def Neg.ofEquiv {X Y : Type*} [Neg X] (f : X ≃ Y) : Neg Y where
  neg a := f (- f.symm a)

@[instance_reducible]
def Inv.ofEquiv {X Y : Type*} [Inv X] (f : X ≃ Y) : Inv Y where
  inv a := f (f.symm a)⁻¹

@[instance_reducible]
def Zero.ofEquiv {X Y : Type*} [Zero X] (f : X ≃ Y) : Zero Y where
  zero := f 0

@[instance_reducible]
def One.ofEquiv {X Y : Type*} [One X] (f : X ≃ Y) : One Y where
  one := f 1

@[instance_reducible]
def SMul.ofEquiv (R : Type*) {X Y : Type*} [SMul R X] (f : X ≃ Y) : SMul R Y where
  smul r a := f (r • f.symm a)

@[instance_reducible]
def Norm.ofEquiv {X Y : Type*} [Norm X] (f : X ≃ Y) : Norm Y where
  norm := fun y => ‖f.symm y‖

@[instance_reducible]
def Inner.ofEquiv {R X Y : Type*} [Inner R X] (f : X ≃ Y) : Inner R Y where
  inner := fun y y' => Inner.inner (𝕜:=R) (f.symm y) (f.symm y')


----------------------------------------------------------------------------------------------------
-- Algebra -----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Two elements of `(_ : X) × Y` are equal if their components are. -/
private theorem sigma_mk_eq {X Y : Type*} {x x' : X} {y y' : Y} (hx : x = x') (hy : y = y') :
    (⟨x,y⟩ : (_ : X) × Y) = ⟨x',y'⟩ := by rw [hx, hy]

-- todo: split this into more class instances
instance {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] : AddCommGroup ((_ : X) × Y) where
  add_assoc := by rintro ⟨_,_⟩ ⟨_,_⟩ ⟨_,_⟩; exact sigma_mk_eq (add_assoc ..) (add_assoc ..)
  zero_add := by rintro ⟨_,_⟩; exact sigma_mk_eq (zero_add ..) (zero_add ..)
  add_zero := by rintro ⟨_,_⟩; exact sigma_mk_eq (add_zero ..) (add_zero ..)
  sub := fun ⟨a,b⟩ ⟨c,d⟩ => ⟨a-c,b-d⟩
  sub_eq_add_neg := by
    rintro ⟨_,_⟩ ⟨_,_⟩; exact sigma_mk_eq (sub_eq_add_neg ..) (sub_eq_add_neg ..)
  nsmul := fun n ⟨x,y⟩ => ⟨n•x, n•y⟩
  nsmul_zero := by rintro ⟨_,_⟩; exact sigma_mk_eq (zero_nsmul ..) (zero_nsmul ..)
  nsmul_succ := by rintro _ ⟨_,_⟩; exact sigma_mk_eq (succ_nsmul ..) (succ_nsmul ..)
  zsmul := fun i ⟨x,y⟩ => ⟨i•x, i•y⟩
  zsmul_zero' := by rintro ⟨_,_⟩; exact sigma_mk_eq (zero_zsmul ..) (zero_zsmul ..)
  zsmul_succ' := by rintro _ ⟨_,_⟩; exact sigma_mk_eq (by simp [add_zsmul]) (by simp [add_zsmul])
  zsmul_neg' := by rintro _ ⟨_,_⟩; exact sigma_mk_eq (SubNegMonoid.zsmul_neg' ..) (SubNegMonoid.zsmul_neg' ..)
  neg_add_cancel := by rintro ⟨_,_⟩; exact sigma_mk_eq (neg_add_cancel ..) (neg_add_cancel ..)
  add_comm := by rintro ⟨_,_⟩ ⟨_,_⟩; exact sigma_mk_eq (add_comm ..) (add_comm ..)

-- todo: split this into more class instances
instance {R X Y : Type*} [Semiring R] [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y] :
    Module R ((_ : X) × Y) where
  one_smul := by rintro ⟨_,_⟩; exact sigma_mk_eq (one_smul ..) (one_smul ..)
  mul_smul := by rintro _ _ ⟨_,_⟩; exact sigma_mk_eq (mul_smul ..) (mul_smul ..)
  smul_zero := by intro _; exact sigma_mk_eq (smul_zero ..) (smul_zero ..)
  smul_add := by rintro _ ⟨_,_⟩ ⟨_,_⟩; exact sigma_mk_eq (smul_add ..) (smul_add ..)
  add_smul := by rintro _ _ ⟨_,_⟩; exact sigma_mk_eq (add_smul ..) (add_smul ..)
  zero_smul := by rintro ⟨_,_⟩; exact sigma_mk_eq (zero_smul ..) (zero_smul ..)

@[instance_reducible]
def AddCommGroup.ofEquiv {X Y : Type*} [AddCommGroup X] (f : X ≃ Y) : AddCommGroup Y where
  add := fun y y' => f (f.symm y + f.symm y')
  zero := f 0
  neg := fun y => f (- f.symm y)
  add_assoc := by
    intro a b c
    show f (f.symm (f (f.symm a + f.symm b)) + f.symm c)
       = f (f.symm a + f.symm (f (f.symm b + f.symm c)))
    simp [add_assoc]
  zero_add := by intro a; show f (f.symm (f 0) + f.symm a) = a; simp
  add_zero := by intro a; show f (f.symm a + f.symm (f 0)) = a; simp
  sub := fun y y' => f (f.symm y - f.symm y')
  sub_eq_add_neg := by
    intro a b
    show f (f.symm a - f.symm b) = f (f.symm a + f.symm (f (-f.symm b)))
    simp [sub_eq_add_neg]
  nsmul := fun n y => f (n•f.symm y)
  nsmul_zero := by intro a; show f ((0:ℕ) • f.symm a) = f 0; simp
  nsmul_succ := by
    intro n a
    show f ((n+1) • f.symm a) = f (f.symm (f (n • f.symm a)) + f.symm a)
    simp [succ_nsmul]
  zsmul := fun i y => f (i•f.symm y)
  zsmul_zero' := by intro a; show f ((0:ℤ) • f.symm a) = f 0; simp
  zsmul_succ' := by
    intro n a
    show f ((n.succ : ℤ) • f.symm a) = f (f.symm (f ((n : ℤ) • f.symm a)) + f.symm a)
    rw [Int.natCast_succ, add_zsmul, one_zsmul, Equiv.symm_apply_apply]
  zsmul_neg' := by
    intro n a
    show f (Int.negSucc n • f.symm a) = f (-f.symm (f ((n.succ : ℤ) • f.symm a)))
    rw [Equiv.symm_apply_apply, SubNegMonoid.zsmul_neg']
  neg_add_cancel := by intro a; show f (f.symm (f (-f.symm a)) + f.symm a) = f 0; simp
  add_comm := by intro a b; show f (f.symm a + f.symm b) = f (f.symm b + f.symm a); simp [add_comm]

@[instance_reducible]
def Module.ofEquiv  {R X Y : Type*} [Semiring R] [AddCommGroup X] [Module R X] [AddCommGroup Y]
    (f : X ≃ Y) : Module R Y where
  smul := fun r y => f (r•f.symm y)
  one_smul := by intro a; show f ((1:R) • f.symm a) = a; simp
  mul_smul := by
    intro r s a
    show f ((r*s) • f.symm a) = f (r • f.symm (f (s • f.symm a)))
    simp [mul_smul]
  -- the remaining fields relate the transported scalar multiplication with the, completely
  -- unrelated, additive structure `[AddCommGroup Y]` hence they are not provable
  smul_zero := sorry_proof
  smul_add := sorry_proof
  add_smul := sorry_proof
  zero_smul := sorry_proof


----------------------------------------------------------------------------------------------------
-- Topology ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance {X Y : Type*} [UniformSpace X] [UniformSpace Y] : UniformSpace ((_ : X) × Y) where
  uniformity := default -- TODO: fix this!!!
  symm := by exact Filter.tendsto_bot
  comp := by
    exact Filter.lift'_le (s:=∅) (by show _ ∈ (⊥ : Filter _); simp)
                                 (by show _ ≤ (⊥ : Filter _); simp)
  nhds_eq_comap_uniformity := sorry_proof

instance {X Y : Type*} [MetricSpace X] [MetricSpace Y] : MetricSpace ((_ : X) × Y) where
  dist := fun ⟨a,b⟩ ⟨c,d⟩ => (dist a c) ⊔ (dist b d)
  dist_self := by rintro ⟨a,b⟩; show (dist a a) ⊔ (dist b b) = 0; simp
  dist_comm := by
    rintro ⟨a,b⟩ ⟨c,d⟩
    show (dist a c) ⊔ (dist b d) = (dist c a) ⊔ (dist d b)
    rw [dist_comm a c, dist_comm b d]
  dist_triangle := by
    rintro ⟨a,b⟩ ⟨c,d⟩ ⟨e,g⟩
    show (dist a e) ⊔ (dist b g) ≤ ((dist a c) ⊔ (dist b d)) + ((dist c e) ⊔ (dist d g))
    refine sup_le ?_ ?_
    · exact (dist_triangle a c e).trans (add_le_add le_sup_left le_sup_left)
    · exact (dist_triangle b d g).trans (add_le_add le_sup_right le_sup_right)
  eq_of_dist_eq_zero := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    have h' : (dist a c) ⊔ (dist b d) = 0 := h
    have h1 : dist a c = 0 := le_antisymm (by rw [← h']; exact le_sup_left) dist_nonneg
    have h2 : dist b d = 0 := le_antisymm (by rw [← h']; exact le_sup_right) dist_nonneg
    exact sigma_mk_eq (dist_eq_zero.mp h1) (dist_eq_zero.mp h2)

@[instance_reducible]
def TopologicalSpace.ofEquiv {X Y : Type*} [TopologicalSpace X] (f : X ≃ Y) :
    TopologicalSpace Y where
  IsOpen A := IsOpen (f⁻¹' A)
  isOpen_univ := by simp_all only [Set.preimage_univ, isOpen_univ]
  isOpen_inter := by
    intro s t hs ht
    show IsOpen (f ⁻¹' (s ∩ t))
    rw [Set.preimage_inter]
    exact hs.inter ht
  isOpen_sUnion := by
    intro S hS
    show IsOpen (f ⁻¹' (⋃₀ S))
    rw [Set.preimage_sUnion]
    exact isOpen_biUnion (fun s hs => hS s hs)

@[instance_reducible]
def UniformSpace.ofEquiv {X Y : Type*} [UniformSpace X] [TopologicalSpace Y] (f : X ≃ Y) :
    UniformSpace Y where
  uniformity := default -- TODO: fix this !!!!
  symm := by exact Filter.tendsto_bot
  comp := by
    exact Filter.lift'_le (s:=∅) (by show _ ∈ (⊥ : Filter _); simp)
                                 (by show _ ≤ (⊥ : Filter _); simp)
  nhds_eq_comap_uniformity := sorry_proof

@[instance_reducible]
def UniformSpace.ofEquiv' {X Y : Type*} [UniformSpace X] (f : X ≃ Y) :
    UniformSpace Y := by
  have : TopologicalSpace Y := TopologicalSpace.ofEquiv f
  apply UniformSpace.ofEquiv f

@[instance_reducible]
def MetricSpace.ofEquiv {X Y : Type*} [MetricSpace X] (f : X ≃ Y) :
    MetricSpace Y where
  dist := fun y y' => (dist (f.symm y) (f.symm y'))
  dist_self := by intro a; show dist (f.symm a) (f.symm a) = 0; simp
  dist_comm := by
    intro a b; show dist (f.symm a) (f.symm b) = dist (f.symm b) (f.symm a); exact dist_comm ..
  dist_triangle := by
    intro a b c
    show dist (f.symm a) (f.symm c) ≤ dist (f.symm a) (f.symm b) + dist (f.symm b) (f.symm c)
    exact dist_triangle ..
  eq_of_dist_eq_zero := by
    intro a b h
    exact f.symm.injective (dist_eq_zero.mp (h : dist (f.symm a) (f.symm b) = 0))


----------------------------------------------------------------------------------------------------
-- Analysis ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


instance {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] :
    NormedAddCommGroup ((_ : X) × Y) where
  dist_eq := by
    rintro ⟨a,b⟩ ⟨c,d⟩
    show (dist a c) ⊔ (dist b d) = ‖-a + c‖ ⊔ ‖-b + d‖
    simp [dist_eq_norm, neg_add_eq_sub, norm_sub_rev]

instance {R X Y : Type*} [RCLike R]
    [NormedAddCommGroup X] [NormedSpace R X]
    [NormedAddCommGroup Y] [NormedSpace R Y] :
    NormedSpace R ((_ : X) × Y) where
  smul_zero := fun r => smul_zero r
  smul_add := fun r x y => smul_add r x y
  add_smul := fun r s x => add_smul r s x
  zero_smul := fun x => zero_smul R x
  norm_smul_le := by
    rintro r ⟨a,b⟩
    show ‖r • a‖ ⊔ ‖r • b‖ ≤ ‖r‖ * (‖a‖ ⊔ ‖b‖)
    refine sup_le ?_ ?_
    · exact (norm_smul_le r a).trans (mul_le_mul_of_nonneg_left le_sup_left (norm_nonneg r))
    · exact (norm_smul_le r b).trans (mul_le_mul_of_nonneg_left le_sup_right (norm_nonneg r))

instance {R X Y : Type*} [RCLike R]
    [NormedAddCommGroup X] [AdjointSpace R X]
    [NormedAddCommGroup Y] [AdjointSpace R Y] :
    AdjointSpace R ((_ : X) × Y) where
  inner_top_equiv_norm := by
    obtain ⟨cx,dx,hcx,hdx,hx⟩ := AdjointSpace.inner_top_equiv_norm (𝕜:=R) (E:=X)
    obtain ⟨cy,dy,hcy,hdy,hy⟩ := AdjointSpace.inner_top_equiv_norm (𝕜:=R) (E:=Y)
    refine ⟨cx ⊓ cy, dx + dy, lt_min hcx hcy, by positivity, ?_⟩
    rintro ⟨x,y⟩
    have hinner : RCLike.re (inner R (⟨x,y⟩ : (_ : X) × Y) ⟨x,y⟩)
        = RCLike.re (inner R x x) + RCLike.re (inner R y y) := by
      show RCLike.re (inner R x x + inner R y y) = _
      rw [map_add]
    have hnorm : ‖(⟨x,y⟩ : (_ : X) × Y)‖ = ‖x‖ ⊔ ‖y‖ := rfl
    obtain ⟨hx1,hx2⟩ := hx x
    obtain ⟨hy1,hy2⟩ := hy y
    simp only [smul_eq_mul] at hx1 hx2 hy1 hy2 ⊢
    rw [hinner, hnorm]
    have hx0 : (0:ℝ) ≤ cx * ‖x‖^2 := by positivity
    have hy0 : (0:ℝ) ≤ cy * ‖y‖^2 := by positivity
    rcases le_total ‖x‖ ‖y‖ with h|h
    · have hsq : ‖x‖^2 ≤ ‖y‖^2 := by nlinarith [norm_nonneg x, norm_nonneg y]
      rw [sup_eq_right.mpr h]
      refine ⟨by nlinarith [min_le_right cx cy, sq_nonneg ‖y‖], by nlinarith [hsq, hdx.le]⟩
    · have hsq : ‖y‖^2 ≤ ‖x‖^2 := by nlinarith [norm_nonneg x, norm_nonneg y]
      rw [sup_eq_left.mpr h]
      refine ⟨by nlinarith [min_le_left cx cy, sq_nonneg ‖x‖], by nlinarith [hsq, hdy.le]⟩
  conj_symm := by
    rintro ⟨a,b⟩ ⟨c,d⟩
    show (starRingEnd R) (inner R c a + inner R d b) = inner R a c + inner R b d
    rw [map_add, AdjointSpace.conj_symm, AdjointSpace.conj_symm]
  add_left := by
    rintro ⟨a,b⟩ ⟨c,d⟩ ⟨e,g⟩
    show inner R (a+c) e + inner R (b+d) g
       = (inner R a e + inner R b g) + (inner R c e + inner R d g)
    rw [AdjointSpace.add_left, AdjointSpace.add_left]
    ring
  smul_left := by
    rintro ⟨a,b⟩ ⟨c,d⟩ r
    show inner R (r•a) c + inner R (r•b) d = (starRingEnd R) r * (inner R a c + inner R b d)
    rw [AdjointSpace.smul_left, AdjointSpace.smul_left, mul_add]


@[instance_reducible]
def NormedAddCommGroup.ofEquiv {X Y : Type*} [NormedAddCommGroup X]
    [Norm Y] [AddCommGroup Y] [MetricSpace Y] (f : X ≃ Y) : NormedAddCommGroup Y where
  dist_eq := sorry_proof

@[instance_reducible]
def NormedAddCommGroup.ofEquiv' {X Y : Type*} [NormedAddCommGroup X] (f : X ≃ Y) : NormedAddCommGroup Y := by
  have : Norm Y := Norm.ofEquiv f
  have : AddCommGroup Y := AddCommGroup.ofEquiv f
  have : MetricSpace Y := MetricSpace.ofEquiv f
  apply NormedAddCommGroup.ofEquiv f

@[instance_reducible]
def NormedSpace.ofEquiv {R X Y : Type*} [RCLike R] [NormedAddCommGroup X] [NormedSpace R X]
    [NormedAddCommGroup Y] [Module R Y] (f : X ≃ Y) : NormedSpace R Y where
  norm_smul_le := sorry_proof

@[instance_reducible]
def NormedSpace.ofEquiv' {R X Y : Type*} [RCLike R] [NormedAddCommGroup X] [NormedSpace R X]
    [NormedAddCommGroup Y] (f : X ≃ Y) : NormedSpace R Y := by
  have : Module R Y := Module.ofEquiv f
  apply NormedSpace.ofEquiv f

@[instance_reducible]
def AdjointSpace.ofEquiv {R X Y : Type*} [RCLike R] [NormedAddCommGroup X] [AdjointSpace R X]
    [NormedAddCommGroup Y] [Inner R Y] [NormedSpace R Y] (f : X ≃ Y) : AdjointSpace R Y where
  inner_top_equiv_norm := sorry_proof
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof

@[instance_reducible]
def AdjointSpace.ofEquiv' {R X Y : Type*} [RCLike R] [NormedAddCommGroup X] [AdjointSpace R X]
    [NormedAddCommGroup Y] (f : X ≃ Y) : AdjointSpace R Y := by
  have : NormedSpace R Y := NormedSpace.ofEquiv' f
  have : Inner R Y := Inner.ofEquiv f
  apply AdjointSpace.ofEquiv f


structure Vec3 (R : Type*) where
  (x y z : R)

instance {R : Type*} [NormedAddCommGroup R] : NormedAddCommGroup (Vec3 R) :=
  (NormedAddCommGroup.ofEquiv' (proxy_equiv% (Vec3 R)))

instance {R X : Type*} [RCLike R] [NormedAddCommGroup X] [AdjointSpace R X] :
    AdjointSpace R (Vec3 X) := (AdjointSpace.ofEquiv' (proxy_equiv% (Vec3 X)))


-- #synth NormedSpace ℝ (Vec3 ℝ)

-- deriving_instance (X) [NormeAddCommGroup X] : NormedAddCommGroup (Vec3 X)
-- deriving_instance (R) [RCLike R] : NormedSpace R (Vec3 R)
