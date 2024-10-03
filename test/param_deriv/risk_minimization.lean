#exit

import SciLean.Core.Transformations.HasParamDerivWithJumps.Common
import SciLean.Core.Transformations.HasParamDerivWithJumps.Functions
import SciLean.Core.Transformations.SurfaceParametrization
import SciLean.Core.Rand
import SciLean.Core.Functions.Gaussian
import SciLean.Tactic.Autodiff

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R]

set_default_scalar R



def foo4
  (l u : R)
  (θ : R × R × R) :=
 (let yzdf := θ.2;
  let μdμ := yzdf.2;
  let ada := θ.1;
  let bdb := yzdf.1;
  let m := (ada + bdb) / 2;
  let interior :=
    ∫ (x : R) in Icc l u,
      let s := gaussian μdμ 5 x;
      let ydg :=
        if x ∈ Icc θ.1 θ.2.1 then
          (s, fun dr =>
            let dx' := dr * s * (5:R) ^ (-2 :R) * (x - μdμ);
            ((0:R), (0:R), dx'))
        else (-gaussian 2 5 x, fun x => 0);
      let yzdf1 := ydg.1;
      let dw := ydg.2 (2 * yzdf1);
      dw;
  let s :=
    ∑ x ∈ {θ.1, θ.2.1},
      let y := gaussian θ.2.2 (5:R) x;
      let y_1 := -gaussian 2 (5:R) x;
      let vals := y ^ 2;
      let vals_1 := y_1 ^ 2;
      if x ∈ Icc l u then (vals - vals_1) • if x < m then ((-1:R), (0:R), (0:R)) else ((0:R), (1:R), (0:R)) else ((0:R),(0:R),(0:R))
  interior + s)
  -- assuming (hθ : θ.1 < θ.2.1)
  -- by
  --   lsimp only [Rand.integral_eq_uniform_E R,
  --               Rand.E_eq_mean_estimateE R 10]
  --   lsimp only [ftrans_simp]
  --   pull_mean

def Impl {α} (a : α) := α

def finish_impl {α} {a : α} : Impl a := a

def foo1 : Impl (let a := id 3; a + 2) := by apply finish_impl
def foo2 : Impl (foo1) := by unfold foo1 finish_impl; (conv => lsimp only []); apply finish_impl


theorem kill_integral
  {X} [MeasurableSpace X] [Zero X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (μ : Measure X)
  : ∫ x, f x ∂μ = f 0 := sorry_proof


def bar1 (l u : R) (θ : R×R×R) (hθ : θ.1 < θ.2.1) : Impl
  (fgradient (fun ((a,b,μ) : R×R×R) => ∫ x in Icc l u,
    (if x ∈ Icc a b then (1:R) else 0 - x)^2) θ) := by

    unfold fgradient
    -- have hθ : θ.1 < θ.2.1 := sorry
    rw[revFDeriv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      )
                      (hA := by assume_almost_disjoint)]

    -- conv in (∫ _, _ ∂_) =>
    --   equals 0 => sorry

    -- conv in List.foldl _ _ _ =>
    --   simp only [ftrans_simp]

    -- conv in (∫ _, _ ∂_) =>
    --   lsimp (config:={zeta:=false}) only []

    -- simp (config:={zeta:=false}) only []
    conv =>
      lautodiff (config:={zeta:=false,memoize:=false}) (disch:=first | fun_prop | gtrans (disch:=fun_prop) | assumption)

    simp (config:={zeta:=false}) only [kill_integral]

    -- Simp (config:={zeta:=false}) only [Rand.integral_eq_uniform_E R,
    --             Rand.E_eq_mean_estimateE R 10]
    -- simp (config:={zeta:=false}) [ftrans_simp]

    -- conv => enter[1]; pull_mean

    apply finish_impl


def bar2 (l u : R) (θ : R×R×R) (hθ : θ.1 < θ.2.1) : Impl
    ((let val := ∫ (x : R) in Icc l u, (if x ∈ Icc θ.1 θ.2.1 then 1 else 0 - x) ^ 2;
        (val, fun dy =>
          let interior :=
            ∫ (x : R) in Icc l u,
              (let ydg := if x ∈ Icc θ.1 θ.2.1 then revFDeriv R (fun x => 1) θ else revFDeriv R (fun x_1 => -x) θ;
                  let yzdf1 := ydg.1;
                  let zdf0 := yzdf1 ^ 2;
                  (zdf0, fun dz =>
                    let dwy := (0, 2 * yzdf1 * dz);
                    let dw := ydg.2 dwy.2;
                    dwy.1 + dw)).2
                dy;
          let density := fun x => Scalar.ofENNReal (volume.rnDeriv volume x);
          let shocks :=
            List.foldl
              (fun sum x =>
                match x with
                | { vals := df, speedGrad := s, discontinuity := Γ } =>
                  sum +
                    ∫ (x : R) in Γ ∩ Icc l u,
                      let vals := df x;
                      (⟪vals.1 - vals.2, dy⟫_R * density x) • s x ∂μH[↑(FiniteDimensional.finrank R R) - ↑1])
              0
              [({
                  vals := fun x =>
                    let y := (1, -x);
                    (y.1 ^ 2, y.2 ^ 2),
                  speedGrad := frontierGrad R (fun w => Icc w.1 w.2.1) θ, discontinuity := frontier (Icc θ.1 θ.2.1) } : DiscontinuityRevData _ _ _)];
          interior + shocks)).2
      1) := by

    conv =>
      lautodiff (config:={zeta:=false,memoize:=false}) (disch:=first | fun_prop | gtrans (disch:=fun_prop) | assumption)

    simp (config:={zeta:=false}) only [kill_integral]

    apply finish_impl


def bar3 (l u : R) (θ : R×R×R) (hθ : θ.1 < θ.2.1) : Impl (bar2 l u θ hθ) := by
    unfold bar2
    unfold finish_impl
    -- unfold id
    -- -- -- conv in (occs:=*) (∫ _ in _, _ ∂_) =>
    -- simp (config:={zeta:=false}) only [Rand.integral_eq_uniform_E R,
    --             Rand.E_eq_mean_estimateE R 10]
    -- simp (config:={zeta:=false}) [ftrans_simp]

    conv =>
      enter[1]
      simp  (config:={zeta:=false,singlePass:=true}) only [Rand.pullMean]
      -- lsimp (config:={zeta:=false}) only
    apply finish_impl


def bar5 (l u : R) (θ : R×R×R) (hθ : θ.1 < θ.2.1) : Impl (bar3 l u θ hθ) := by
  unfold bar3 finish_impl
  dsimp (config:={zeta:=false})

  conv =>
    enter[1]
    lsimp (config:={zeta:=false}) only

  apply finish_impl


#exit

set_option pp.proofs true in

set_option pp.all true in
def bar4 (l u : R) (θ : R×R×R) (hθ : θ.1 < θ.2.1) : Impl (bar3 l u θ hθ) := by
  unfold bar3
  unfold finish_impl
  unfold id

  conv in (∑ _ ∈ _, _) =>
    equals 0 => sorry

  conv in ( _ + _) =>
    simp (config:={zeta:=false})
    enter[u]
    simp

  conv =>
    enter [1,2]
    simp (config:={zeta:=false})

  conv => lsimp (config:={zeta:=false}) only
  apply finish_impl



variable (l u : R) (θ : R×R×R) (hθ : θ.1 < θ.2.1)

#check bar3.proof_2

#check (Impl
    ((bar3.proof_2 l u θ hθ).mpr
      (let ydg := if θ.1 ≤ 0 ∧ 0 ≤ θ.2.1 then (1, fun x => (0:R×R×R)) else ((0:R), fun x => 0);
      ydg.2 (2 * ydg.1))))
    rewrite_by
      lsimp (config:={zeta:=false}) only


def foo1 : Impl (let a := id 3; a + 2) := by apply finish_impl
def foo2 : Impl (foo1) := by unfold foo1 finish_impl; (conv => lsimp only []); apply finish_impl




#check (Impl <| Eq.mpr (rfl : Nat = Nat)
             <| Eq.mpr (rfl : Nat = Nat) (let a := id 3; a + 2)) rewrite_by
  lsimp only

#exit

def bar6 (l u : R) (θ : R×R×R) : Impl (bar3 l u θ) := by
  unfold bar3
  apply finish_impl

def bar7 (l u : R) (θ : R×R×R) :=
  derive_random_approx
    (bar3 l u θ)
  by
  unfold bar3 finish_impl bar1 id
  dsimp (config:={zeta:=false})
  pull_mean





def test_fwdFDeriv (l u : R) (θ dθ : R×R×R) :=
  derive_random_approx
  (fwdFDeriv R (fun ((a,b,μ) : R×R×R) => ∫ x in Icc l u,
    ‖ if x ∈ Icc a b then gaussian μ (5:R) x else 0 -  gaussian 2 (5:R) x ‖₂²) θ dθ)
  assuming (hθ : θ.1 < θ.2.1)
  by
    rw[fwdFDeriv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=first | fun_prop | gtrans (disch:=fun_prop) | assumption)

    conv in (occs:=*) (∫ _ in _, _ ∂_) =>
      . lsimp only [Rand.integral_eq_uniform_E R,
                    Rand.E_eq_mean_estimateE R 10]
        lsimp only [ftrans_simp]

    pull_mean


#eval 0

#eval 0


def test_fgradient (l u : R) (θ : R×R×R) :=
  -- derive_random_approx
  (fgradient (fun ((a,b,μ) : R×R×R) => ∫ x in Icc l u,
    (if x ∈ Icc a b then (1:R) else 0 - x)^2) θ)
  -- assuming
  rewrite_by
    unfold fgradient
    tactic => have hθ : θ.1 < θ.2.1 := sorry
    rw[revFDeriv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=first | fun_prop | gtrans (disch:=fun_prop) | assumption)

    -- conv in (occs:=*) (∫ _ in _, _ ∂_) =>
    lsimp only [Rand.integral_eq_uniform_E R,
                Rand.E_eq_mean_estimateE R 10]
    lsimp only [ftrans_simp]

    -- pull_mean


#eval 0

#eval (test_fwdFDeriv (-1.0) 1.0 (0.0,1.0,0.5) (1.0,0.0,0.0)).get
