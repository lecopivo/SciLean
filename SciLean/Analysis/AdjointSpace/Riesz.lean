module

public import SciLean.Analysis.AdjointSpace.Basic
public import SciLean.Analysis.Normed.IsContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public section

/-! # Riesz representation theorem for `AdjointSpace`

The inner product of an `AdjointSpace` induces a genuine inner product space structure whose
topology is the original one. Therefore every continuous linear functional on a complete
`AdjointSpace` is represented by the inner product with a fixed vector.
-/

open RCLike ComplexConjugate Bornology Filter Topology

namespace AdjointSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [nE : NormedAddCommGroup E] [AdjointSpace 𝕜 E]

variable (𝕜 E) in
/-- The inner product of an `AdjointSpace` satisfies the axioms of an inner product, i.e. it gives
rise to `InnerProductSpace.Core`. Note that the norm induced by this inner product is in general
not the norm of `E`, it is only equivalent to it. -/
@[instance_reducible]
noncomputable def toInnerProductSpaceCore : InnerProductSpace.Core 𝕜 E where
  inner x y := inner 𝕜 x y
  conj_inner_symm := conj_symm
  re_inner_nonneg _ := inner_self_nonneg (𝕜:=𝕜)
  add_left := add_left
  smul_left := smul_left
  definite _ h := inner_self_eq_zero (𝕜:=𝕜) |>.1 h

/-- The map `x ↦ ⟪x,x⟫` is continuous at zero. -/
theorem continuousAt_inner_self :
    ContinuousAt (fun x : E => (toInnerProductSpaceCore 𝕜 E).inner x x) 0 := by
  obtain ⟨C, _, hC⟩ := AdjointSpace.exists_norm_inner_le 𝕜 (E:=E)
  have hg : Continuous fun x : E => C * (‖x‖ * ‖x‖) := by fun_prop
  have h0 : Tendsto (fun x : E => C * (‖x‖ * ‖x‖)) (𝓝 0) (𝓝 0) := by
    simpa using hg.tendsto' 0 0 (by simp)
  have h : Tendsto (fun x : E => (inner 𝕜 x x : 𝕜)) (𝓝 0) (𝓝 0) :=
    squeeze_zero_norm (fun x => hC x x) h0
  have hz : (inner 𝕜 (0:E) (0:E) : 𝕜) = 0 := AdjointSpace.inner_zero_left (𝕜:=𝕜) 0
  show Tendsto (fun x : E => (inner 𝕜 x x : 𝕜)) (𝓝 0) (𝓝 (inner 𝕜 (0:E) (0:E)))
  rw [hz]; exact h

/-- The unit ball of the norm induced by the inner product is a bounded set. -/
theorem isVonNBounded_inner_self_lt_one :
    IsVonNBounded 𝕜 {x : E | re ((toInnerProductSpaceCore 𝕜 E).inner x x) < 1} := by
  obtain ⟨c, _, hc, _, h⟩ := AdjointSpace.inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
  rw [NormedSpace.isVonNBounded_iff, isBounded_iff_forall_norm_le]
  refine ⟨Real.sqrt (1/c), fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq] at hx
  have hx' : re (inner 𝕜 x x : 𝕜) < 1 := hx
  have h1 : c * ‖x‖^2 ≤ re (inner 𝕜 x x : 𝕜) := by simpa using (h x).1
  have h2 : ‖x‖^2 ≤ 1/c := by rw [le_div_iff₀ hc, mul_comm]; linarith
  calc ‖x‖ = Real.sqrt (‖x‖^2) := by rw [Real.sqrt_sq (norm_nonneg x)]
    _ ≤ Real.sqrt (1/c) := Real.sqrt_le_sqrt h2

/-- The inner product is continuous in its second argument. -/
theorem continuous_inner_right (y : E) : Continuous (fun x : E => (inner 𝕜 y x : 𝕜)) := by
  obtain ⟨C, _, hC⟩ := AdjointSpace.exists_norm_inner_le 𝕜 (E:=E)
  let L : E →ₗ[𝕜] 𝕜 :=
    { toFun := fun x => inner 𝕜 y x
      map_add' := fun a b => AdjointSpace.inner_add_right ..
      map_smul' := fun c a => by
        show (inner 𝕜 y (c • a) : 𝕜) = c • (inner 𝕜 y a : 𝕜)
        rw [AdjointSpace.inner_smul_right, smul_eq_mul] }
  exact (L.mkContinuous (C * ‖y‖) (fun x => by
    calc ‖(inner 𝕜 y x : 𝕜)‖ ≤ C * (‖y‖ * ‖x‖) := hC y x
      _ = C * ‖y‖ * ‖x‖ := by ring)).continuous

/-- The inner product with a fixed vector on the left is a continuous linear map. -/
@[fun_prop]
theorem isContinuousLinearMap_inner_right (y : E) :
    SciLean.IsContinuousLinearMap 𝕜 (fun x : E => (inner 𝕜 y x : 𝕜)) where
  linear := by
    constructor
    · intro a b; exact AdjointSpace.inner_add_right ..
    · intro c a
      show (inner 𝕜 y (c • a) : 𝕜) = c • (inner 𝕜 y a : 𝕜)
      rw [AdjointSpace.inner_smul_right, smul_eq_mul]
  cont := continuous_inner_right y

/-- The inner product is continuous in its first argument. -/
theorem continuous_inner_left (y : E) : Continuous (fun x : E => (inner 𝕜 x y : 𝕜)) := by
  have h : (fun x : E => (inner 𝕜 x y : 𝕜)) = fun x : E => conj (inner 𝕜 y x : 𝕜) := by
    funext x; rw [AdjointSpace.inner_conj_symm]
  rw [h]
  exact RCLike.continuous_conj.comp (continuous_inner_right y)

/-- Two uniform structures on an additive group that induce the same topology and make it a uniform
additive group are equal, hence completeness can be transferred between them. -/
theorem completeSpace_of_topology_eq {X : Type*} [AddCommGroup X] (u₁ u₂ : UniformSpace X)
    (h₁ : @IsUniformAddGroup X u₁ _) (h₂ : @IsUniformAddGroup X u₂ _)
    (htop : @UniformSpace.toTopologicalSpace X u₁ = @UniformSpace.toTopologicalSpace X u₂)
    (hc : @CompleteSpace X u₁) : @CompleteSpace X u₂ := by
  have : u₁ = u₂ :=
    @IsUniformAddGroup.ext X _ u₁ u₂ h₁ h₂ (congrArg (fun t => @nhds X t 0) htop)
  exact this ▸ hc

/-- **Riesz representation theorem** for `AdjointSpace`: every continuous linear functional on a
complete `AdjointSpace` is given by taking the inner product with a fixed vector. -/
theorem exists_inner_eq [CompleteSpace E] (f : E →L[𝕜] 𝕜) :
    ∃ v : E, ∀ x, (inner 𝕜 v x : 𝕜) = f x := by
  -- keep the original algebraic structure around, only the norm is going to be replaced
  have ctag : IsTopologicalAddGroup E := inferInstance
  have ccsm : ContinuousConstSMul 𝕜 E := inferInstance
  let acg : AddCommGroup E := inferInstance
  let mod : Module 𝕜 E := inferInstance
  let cd : InnerProductSpace.Core 𝕜 E := toInnerProductSpaceCore 𝕜 E
  have hcont := continuousAt_inner_self (𝕜:=𝕜) (E:=E)
  have hbdd := isVonNBounded_inner_self_lt_one (𝕜:=𝕜) (E:=E)
  -- the inner product induces a normed space structure with the *same* topology
  let nacg : NormedAddCommGroup E := cd.toNormedAddCommGroupOfTopology hcont hbdd
  let nsp : NormedSpace 𝕜 E := cd.toNormedSpaceOfTopology hcont hbdd
  let ips : InnerProductSpace 𝕜 E := InnerProductSpace.ofCoreOfTopology cd hcont hbdd
  -- the two uniformities agree, hence `E` is still complete
  have : CompleteSpace E := by
    refine completeSpace_of_topology_eq
      nE.toMetricSpace.toPseudoMetricSpace.toUniformSpace _
      (@SeminormedAddCommGroup.to_isUniformAddGroup E nE.toSeminormedAddCommGroup) ?_ rfl ?_ <;>
      infer_instance
  exact ⟨(InnerProductSpace.toDual 𝕜 E).symm f, fun x => InnerProductSpace.toDual_symm_apply⟩

variable {F : Type*} [NormedAddCommGroup F] [AdjointSpace 𝕜 F]

/-- Every continuous linear map between complete `AdjointSpace`s has an adjoint. -/
theorem exists_adjoint [CompleteSpace E] (A : E → F) (hA : SciLean.IsContinuousLinearMap 𝕜 A) :
    ∃ g : F → E, ∀ x y, (inner 𝕜 (A x) y : 𝕜) = inner 𝕜 x (g y) := by
  obtain ⟨C, _, hC⟩ := AdjointSpace.exists_norm_inner_le 𝕜 (E:=F)
  have key : ∀ y : F, ∃ v : E, ∀ x : E, (inner 𝕜 v x : 𝕜) = inner 𝕜 y (A x) := by
    intro y
    let B : E →L[𝕜] F := SciLean.ContinuousLinearMap.mk' 𝕜 A hA
    refine exists_inner_eq (LinearMap.mkContinuous
      { toFun := fun x => inner 𝕜 y (A x)
        map_add' := by
          intro a b
          simp only [hA.linear.map_add, AdjointSpace.inner_add_right]
        map_smul' := by
          intro r a
          simp only [hA.linear.map_smul, AdjointSpace.inner_smul_right, RingHom.id_apply,
            smul_eq_mul] } (C * ‖y‖ * ‖B‖) (fun x => ?_))
    have hAx : ‖A x‖ ≤ ‖B‖ * ‖x‖ := B.le_opNorm x
    calc ‖(inner 𝕜 y (A x) : 𝕜)‖ ≤ C * (‖y‖ * ‖A x‖) := hC y (A x)
      _ ≤ C * (‖y‖ * (‖B‖ * ‖x‖)) := by
          have hCy : (0:ℝ) ≤ C * ‖y‖ := by positivity
          nlinarith [norm_nonneg y, norm_nonneg (A x)]
      _ = C * ‖y‖ * ‖B‖ * ‖x‖ := by ring
  choose g hg using key
  refine ⟨g, fun x y => ?_⟩
  rw [← AdjointSpace.inner_conj_symm (𝕜:=𝕜) (A x) y, ← AdjointSpace.inner_conj_symm (𝕜:=𝕜) x (g y),
    hg y x]

end AdjointSpace
