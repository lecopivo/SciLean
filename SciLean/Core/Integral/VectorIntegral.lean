import Mathlib.MeasureTheory.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.VectorMeasure

import SciLean.Util.SorryProof

namespace SciLean

open MeasureTheory FiniteDimensional

variable
  {U V W}
  {X} [MeasurableSpace X]
  {Y} [MeasurableSpace Y]
  [AddCommGroup U] [Module ℝ U] [TopologicalSpace U]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]


-- TODO: maybe this should not depend on `L` as the integral should exist for any continuous
--       bilinear `L`
def HasVecIntegral
    (f : X → U) (μ : VectorMeasure X V) (L : U → V → W) : Prop :=

  ∃ (w : W), ∀ (w' : W →L[ℝ] ℝ), ∀ (μm : ℕ → Measure X) (μv : ℕ → V),
    (∀ A : Set X, ∑' n, (μm n A).toReal • μv n = μ A) -- this approximation of `μ` has to be refined
    →
    w' w = (∑' n, ∫ x, w' (L (f x) (μv n)) ∂(μm n))


open Classical in
/-- Weak(Pettis) integral of vector valued function w.r.t. to vector valued measure.

  The function `L` has to be a bilinear map that mixes values of of `f` and `μ` appropriately.

  Normal integral (U=W=ℝ) (V=ℝ≥0) i.e. scalar valued function and normal measure then:
  ```
  L = fun (u : ℝ) (v : ℝ≥0) => u * v
  ```

  Pettis integral (U=W) (V=ℝ≥0) i.e. vector valued function and normal measure then:
  ```
  L fun (u : U) (v : ℝ) => v • u
  ```
-/
noncomputable
def vectorIntegral {X U V W} [MeasurableSpace X]
    [AddCommGroup U] [Module ℝ U] [TopologicalSpace U]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    (f : X → U) (μ : VectorMeasure X V) (L : U → V → W) : W :=

  if h : HasVecIntegral f μ L then
    choose h
  else
    0



noncomputable
def _root_.MeasureTheory.VectorMeasure.bind
    (μ : VectorMeasure X U) (ν : X → VectorMeasure Y V) (L : U → V → W) :
    VectorMeasure Y W where

  measureOf' := fun A => vectorIntegral (fun x => ν x A) μ (fun v u => L u v)
  empty' := sorry_proof
  not_measurable' := sorry_proof
  m_iUnion' := sorry_proof
