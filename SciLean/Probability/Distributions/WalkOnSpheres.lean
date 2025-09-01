import SciLean.Probability.Rand
-- import SciLean.Core.Rand.Tactic
-- import SciLean.Core.Rand.Distributions.Uniform
-- import SciLean.Core.Rand.Distributions.Sphere

-- import SciLean.Core.FunctionTransformations
-- import SciLean.Core.Notation.CDeriv
-- import SciLean.Core.Notation.FwdDeriv

-- import SciLean.Core.FloatAsReal
-- import SciLean.Tactic.LetUtils
-- import SciLean.Tactic.LetEnter
-- import SciLean.Util.RecVal

-- import SciLean.Tactic.ConvInduction

-- import SciLean.Core.FunctionSpaces

open MeasureTheory

namespace SciLean.Rand


-- variable {Y : Type} [SemiHilbert Float Y] [Module ℝ Y] [IsScalarTower ℝ Float Y] [MeasurableSpace Y]
-- set_default_scalar Float


-- def pi' := 3.14159265359


-- open RealScalar in
-- noncomputable
-- def harmonicRec (n : ℕ) (φ : Vec3 → Float) (g : Vec3 → Y) (x : Vec3) : Y :=
--   match n with
--   | 0 => g x
--   | m+1 => (4*(pi':Float))⁻¹ • ∫' (x' : sphere (0:Vec3) (1:Float)), harmonicRec m φ g (x + φ x • x'.1)


-- def walkOnSpheres (φ : Vec3 → Float) (g : Vec3 → Y) (n : ℕ) (x : Vec3) : Rand Y := do
--   let f ←
--     derive_random_approx
--       (fun x => harmonicRec n φ g x)
--     by
--       induction n n' prev h
--         . simp[harmonicRec]
--         . simp[harmonicRec,h]
--           simp only [smul_push,cintegral.arg_f.push_lambda]
--           rw[cintegral_as_uniform_E Float]
--       rw[pull_E_nat_recOn (x₀:=_) (r:=_) (hf:=by fun_prop)]
--       simp (config:={zeta:=false})
--   return f x


-- @[fun_prop]
-- theorem harmonicRec.arg_x.CDifferentiable_rule (n : ℕ)
--     (φ : Vec3 → Float) (g : Vec3 → Y)
--     (hφ : CDifferentiable Float φ) (hg : CDifferentiable Float g) :
--     CDifferentiable Float (fun x : Vec3 => harmonicRec n φ g x) := by
--   induction n <;> (simp[harmonicRec]; fun_prop)


-- noncomputable
-- def harmonicRec_fwdDeriv (n : ℕ)
--     (φ : Vec3 → Float) (φ' : Vec3 → Vec3 → Float×Float)
--     (g : Vec3 → Y) (g' : Vec3 → Vec3 → Y×Y) : Vec3 → Vec3 → Y×Y :=
--     (∂> x, harmonicRec n φ g x)
--   rewrite_by
--     assuming (hφ' : (∂> φ) = φ') (hφ : CDifferentiable Float φ)
--              (hg' : (∂> g) = g') (hg : CDifferentiable Float g)
--     induction n n' du h
--       . simp[harmonicRec]; autodiff
--       . simp[harmonicRec];
--         simp only [smul_push]; autodiff


-- def harmonicRec.arg_x.fwdDeriv_randApprox (n : ℕ)
--     (φ : Vec3 → Float) (φ' : Vec3 → Vec3 → Float×Float)
--     (g : Vec3 → Y) (g' : Vec3 → Vec3 → Y×Y)
--     (x dx : Vec3) : Rand (Y×Y) := do
--   derive_random_approx
--     (harmonicRec_fwdDeriv n φ φ' g g' x dx)
--   by
--     unfold harmonicRec_fwdDeriv
--     conv =>
--       pattern (fun _ _ _ _ => cintegral _ _)
--       enter [n,du]
--       conv =>
--         conv => enter [x];rw[cintegral.arg_f.push_lambda]
--         rw[cintegral.arg_f.push_lambda]
--       rw[cintegral_as_uniform_E Float]
--     rw[pull_E_nat_recOn (x₀:=_) (r:=_) (hf:=by fun_prop)]
--     simp (config:={zeta:=false})


-- set_default_scalar Float


-- noncomputable
-- def harmonicRec' (n : ℕ) (φ : Vec3 ⟿FD Float) (g : Vec3 ⟿FD Y) (x : Vec3) : Y :=
--   match n with
--   | 0 => g x
--   | m+1 => (4*(pi':Float))⁻¹ • ∫' (x' : sphere (0:Vec3) (1:Float)), harmonicRec' m φ g (x + φ x • x'.1)


-- @[fun_prop]
-- theorem harmonicRec'_CDifferentiable (n : ℕ) :
--     CDifferentiable Float (fun (w : (Vec3 ⟿FD Float)×(Vec3 ⟿FD Y)×Vec3) => harmonicRec' n w.1 w.2.1 w.2.2) := by
--   induction n <;> (simp[harmonicRec']; fun_prop)


-- noncomputable
-- def harmonicRec'_fwdDeriv (n : ℕ) :=
--     (∂> (φ,g,x), harmonicRec' (Y:=Y) n φ g x)
--   rewrite_by
--     induction n n' du h
--       . simp only [harmonicRec']; autodiff
--       . simp only [harmonicRec',smul_push]; autodiff


-- def harmonicRec'_fwdDeriv_rand (n : ℕ)
--     (φ dφ : Vec3 ⟿FD Float) (g dg : Vec3 ⟿FD Y) (x dx : Vec3) : Rand (Y×Y) := do
--   derive_random_approx
--     (harmonicRec'_fwdDeriv n (φ,g,x) (dφ,dg,dx))
--   by
--     unfold harmonicRec'_fwdDeriv
--     conv =>
--       pattern (fun _ _ _ _ => cintegral _ _)
--       enter [n,du]
--       conv =>
--         conv => enter [x];rw[cintegral.arg_f.push_lambda]
--         rw[cintegral.arg_f.push_lambda]
--       rw[cintegral_as_uniform_E Float]
--     rw[pull_E_nat_recOn (x₀:=_) (r:=_) (hf:=by fun_prop)]
--     simp (config:={zeta:=false})
