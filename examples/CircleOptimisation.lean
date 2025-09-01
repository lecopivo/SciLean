/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat

Riemannian Gradient Descent on S¹.
-/

import SciLean
open Lean
open SciLean


instance : HDiv (ℝ ^{n}) ℝ (ℝ^{n}) where
  hDiv v r := ⊞ i, v[i] / r


/-- choose a particular A: (x, y) ↦ (x + y, x - y) -/
def A (x : ℝ^{2}) : ℝ^{2} :=
  ⊞ i, if i = 0 then x[0] + x[1] else x[0] - x[1]

-- We can turn on debugging logging with
--   set_option trace.Meta.Tactic.fun_trans.rewrite true in
function_properties A (x : ℝ^{2})
argument x
  IsLin, HasAdjoint, IsSmooth, HasAdjDiff,
  abbrev ∂ := λ dx => A dx by unfold A; fun_trans,
  def † :=
    λ x' => ⊞ i,
      if i = 0 then x'[0] - x'[1] else x'[0] + x'[1] by sorry,
  abbrev ∂† by unfold adjointDifferential; fun_trans; fun_trans; simp


-- Define the loss function.
def loss (x : ℝ^{2}) : ℝ := ⟪x, A x⟫

function_properties loss (x : ℝ^{2})
argument x
  IsSmooth, HasAdjDiff,
  abbrev ∂ := λ dx => (2 : ℝ) * ⟪dx, A x⟫ by {
    simp[loss];
    fun_trans; -- 'trans' makes me think of 'transitive'.
    simp;
    funext dx;
    -- ⊢ ⟪dx, A x⟫ + ⟪x, A dx⟫ = 2 * ⟪dx, A x⟫
    --   ⟪dx, A x⟫ + ⟪x, A dx⟫
    --   = ⟪dx, A x⟫ + ⟪A† x, dx⟫  -- by definition of adjoint
    --   = ⟪dx, A x⟫ + ⟪dx, A† x⟫  -- by symmetry of inner product
    --   = ⟪dx, A x⟫ + ⟪dx, A x⟫   -- by A† = A
    --   = 2 * ⟪dx, A x⟫           -- by ring
    sorry
  },
  abbrev ∂† by { unfold gradient; unfold loss; fun_trans; simp }


/-- noncomputable version of gradient of loss -/
noncomputable def gradLoss (x : ℝ^{2}) : ℝ^{2} := ∇ loss x

/-- make gradLoss computable by transforming abstract gradient defn into computable
    definition. -/
def gradLoss' (x : ℝ^{2}) : ℝ^{2} :=
  (∇ loss x) rewrite_by {
    unfold gradient; unfold loss; fun_trans
}


/-- Data at each training iteration -/
structure TrainIter where
  iteration : Nat -- iteration count.
  point : ℝ^{2} -- current point on the circle..
  loss_at_point : ℝ -- loss value at current point.
  gradAmbient : ℝ^{2} -- gradient at current point in ambient space.
  gradSubmanifold : ℝ^{2} -- gradient at current point on the tagent space.


instance : ToString TrainIter where
  toString log :=
   -- TODO: need ToString instances to show.
   s!"{log.iteration} loss[{log.loss_at_point.val}]"


/-- Normalize a vector. -/
def normalize (p : ℝ^{2}) : ℝ^{2} := p / ‖p‖

/-- Project 'v' along 'direction'. -/
def project (v : ℝ^{2}) (direction: ℝ^{2}) : ℝ^{2} :=
   ⟪v, direction⟫ • direction

/-- Project point 'x' to lie on the circle.
    This is a retraction of (ℝ^2 - origin) onto the embedded S¹. -/
def circle_project (x : ℝ^{2}) := normalize x


/-- project a vector to the tangent space at `p`
    by deleting the normal component -/
def projectToCircleTangentSpace (p : ℝ^{2}) (vec : ℝ^{2}) : ℝ^{2} :=
  vec - project (direction := p) vec


/-- Calculate gradient at current point -/
def TrainIter.calcAtPoint (i : Nat) (p : ℝ^{2}) : TrainIter where
  iteration := i
  point := p
  loss_at_point := loss p
  gradAmbient := gradLoss' p
  gradSubmanifold := projectToCircleTangentSpace (p := p) (gradLoss' p)

structure HyperParams where
  learningRate : ℝ := 0.01

def HyperParams.default : HyperParams := {}
instance : Inhabited HyperParams where default := {}

/-- Step to the next point by gradient descent -/
def TrainIter.nextPoint (hp : HyperParams) (step : TrainIter) : ℝ^{2} :=
  circle_project <| step.point - hp.learningRate • step.gradSubmanifold

/-- run the gradient descent algorithm -/
def gradientDescend (init: ℝ^{2}) (nsteps : ℕ)
  (hp : HyperParams := HyperParams.default) :
  Array TrainIter := Id.run do
    let mut cur : ℝ^{2} := circle_project init
    let mut out := #[]
    for i in List.range nsteps do
      let step := TrainIter.calcAtPoint i cur
      out := out.push <| step
      cur := step.nextPoint hp
    return out

def main : IO Unit := do
  let init : ℝ^{2} :=
    ⊞ i, if i = 0 then 1 else 0
  let losses := gradientDescend init 1000
  for loss in losses do
    IO.println s!"{loss}"
