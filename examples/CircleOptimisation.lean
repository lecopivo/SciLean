/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat

Riemannian Gradient Descent on S1.
-/

import SciLean
open Lean
open SciLean


instance : HDiv (ℝ ^{n}) ℝ (ℝ^{n}) where
  hDiv v r := ⊞ i, v[i] / r

instance : HMul ℝ (ℝ ^{n}) (ℝ^{n}) where
  hMul r v := ⊞ i, v[i] * r


/-- choose a particular A -/
-- the function (x, y) -> (x + y, x - y)
def A (x : ℝ^{2}) : ℝ^{2} :=
  ⊞ i, if i = 0 then x[0] + x[1] else x[0] - x[1]

-- set_option trace.Meta.Tactic.fun_trans.rewrite true in
function_properties A (x : ℝ^{2})
argument x
  IsLin, HasAdjoint, IsSmooth, HasAdjDiff,
  abbrev ∂ := λ dx => A dx by unfold A; fun_trans,
  def † :=
    λ x' => ⊞ i,
      if i = 0 then x'[0] - x'[1] else x'[0] + x'[1] by sorry,
  abbrev ∂† by unfold adjointDifferential; fun_trans; fun_trans; simp


set_option trace.Meta.Tactic.fun_trans.rewrite true in
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
    -- how do I prove this? The natural proof for me is to do this componentwise
    sorry
  },
  abbrev ∂† by { unfold gradient; unfold loss; fun_trans; simp }

noncomputable def grad_loss (x : ℝ^{2}) : ℝ^{2} := ∇ loss x

def grad_loss' (x : ℝ^{2}) : ℝ^{2} :=
  (∇ loss x) rewrite_by {
    unfold gradient; unfold loss; fun_trans
}


structure TrainLog where
  iteration : Nat
  point : ℝ^{2} -- current point on the circle
  loss_at_point : ℝ -- loss value at current point
  gradient_ambient : ℝ^{2} -- gradient at current point
  gradient_circle : ℝ^{2} -- gradient at current point


instance : ToString TrainLog where
  toString log :=
   -- TODO: need ToString instances to show.
   -- s!"p = {log.point} ; loss = {log.loss_at_point.val}; ∇ = {log.gradient_circle}"
   s!"{log.iteration} loss[{log.loss_at_point.val}]"


-- normalize a vector.
def normalize (p : ℝ^{2}) : ℝ^{2} := p / ‖p‖

-- project 'v' along 'direction'
def project (v : ℝ^{2}) (direction: ℝ^{2}) : ℝ^{2} :=
   ⟪v, direction⟫ * direction

-- project point 'x' to lie on the circle.
-- This is a retraction of (ℝ^2 - origin) onto the embedded S¹
def circle_project (x : ℝ^{2}) := normalize x


-- project a vector to the tangent space at 'p'
-- by deleting the normal component
def circle_tangent_space_project (p : ℝ^{2}) (vec : ℝ^{2}) : ℝ^{2} :=
  vec - project (direction := p) vec


def TrainLog.calc (i : Nat) (p : ℝ^{2}) : TrainLog where
  iteration := i
  point := p
  loss_at_point := loss p
  gradient_ambient := grad_loss' p
  gradient_circle := circle_tangent_space_project (p := p) (grad_loss' p)

structure HyperParams where
  learningRate : ℝ := 0.01

def HyperParams.default : HyperParams := {}
instance : Inhabited HyperParams where default := {}

def TrainLog.nextPoint (hp : HyperParams) (step : TrainLog) : ℝ^{2} :=
  circle_project <| step.point - hp.learningRate * step.gradient_circle

def plot_loss (init: ℝ^{2}) (nsteps : ℕ)
  (hp : HyperParams := HyperParams.default) :
  Array TrainLog := Id.run do
    let mut cur : ℝ^{2} := circle_project init
    let mut out := #[]
    for i in List.range nsteps do
      let step := TrainLog.calc i cur
      out := out.push <| step
      cur := step.nextPoint hp
    return out

def main : IO Unit := do
  let init : ℝ^{2} :=
    ⊞ i, if i = 0 then 1 else 0
  let losses := plot_loss init 20
  for loss in losses do
    IO.println s!"{loss}"
