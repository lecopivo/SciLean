/-
SciLean Documentation - Front Page
-/
import VersoBlog

open Verso Genre Blog

#doc (Page) "SciLean" =>

# Scientific Computing in Lean 4

SciLean is a framework for scientific computing in Lean 4, bringing
the power of dependent types to numerical computation.

# Type-Safe Neural Networks

SciLean uses dependent types to encode tensor shapes in type signatures,
catching dimension mismatches at compile time:

```
structure Weights where
  w1 : Float^[128, 784]   -- First layer: 128 outputs, 784 inputs
  b1 : Float^[128]        -- First layer bias
  w2 : Float^[10, 128]    -- Second layer: 10 outputs, 128 inputs
  b2 : Float^[10]         -- Second layer bias

def forward (x : Float^[784]) (w : Weights) : Float^[10] :=
  let h1 : Float^[128] := DataArrayN.contractRightAddR 1.0 w.w1 x 1.0 w.b1
  let a1 : Float^[128] := h1.mapMono gelu
  let h2 : Float^[10] := DataArrayN.contractRightAddR 1.0 w.w2 a1 1.0 w.b2
  DataArrayN.softmax h2
```

The type `Float^[784]` ensures input images are exactly 784 floats (28x28 MNIST).
If you try to pass a `Float^[100]`, you get a compile-time error.

# Features

* _Dependent types for arrays_: `Float^[n,m]` encodes shape in the type
* _Automatic differentiation_: Forward and reverse mode with `fderiv` and `revFDeriv`
* _BLAS integration_: Native matrix operations via CBLAS/Accelerate
* _GPU support_: Metal compute shaders for macOS

# MNIST Training Results

| Metric | Value |
|--------|-------|
| Architecture | 784 → 128 → 10 |
| Activation | GELU |
| Training samples | 1000 |
| Final accuracy | *96.3%* |

# Quick Start

```
lake build SimpleMNIST
./.lake/build/bin/SimpleMNIST
```

# Documentation

* {page_link nnDocs}[Neural Networks] — Type-safe neural network implementation
