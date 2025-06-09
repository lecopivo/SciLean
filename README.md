# SciLean: Scientific Computing in Lean

  Library for scientific computing such as solving differential equations, optimization or machine learning written in [Lean](http://leanprover.github.io/). This library is in an *early stage of development* and at its current stage is just a proof of concept on how Lean can be used for scientific computing.

Lean is an expressive functional programming language that allows to formalize the mathematics behind these computations. This can offer several benefits:

- Code transformation and optimization guided by formalization of underlining mathematics, like automatic differentiation, algebraic simplification, fine control of used approximations or execution scheduling.
- First class symbolic computation. Any function can be purely symbolic, functions like `gradient`, `integral` or `limit` are inherently non-computable. However, they carry meaning what the program should be doing and we provide tools to manipulate them or approximate them with actually computable function.
- Code generation based on formal specification. Many problems any scientific computing or machine learning can be stated very easily e.g. find a minimizer of a function. We then provide tools how to turn such specification into a runnable code satisfying the specification, usually in an appropriate limit of used approximations.
- Catalogization of numerical methods.

  In short, mathematics is the ultimate abstraction for numerical computing and Lean can understand mathematics. Hopefully, using Lean will allow us to create really powerful and extensible library for scientific computing.


## Documentation

### Manual
- [Scientific Computing in Lean](https://lecopivo.github.io/scientific-computing-lean/)  
  _A work-in-progress book on scientific computing in Lean._

### Presentations
- [Automatic Differentiation in Lean – Lean Together 2024 (30min)](https://www.youtube.com/watch?v=Kjx5KvB8FL8)  
  Motivation and examples of forward and reverse mode AD in Lean.

- [Scientific Computing in Lean – Lean for Scientists and Engineers 2024 (2h)](https://www.youtube.com/watch?v=X1oEV5SsFJ8)  
  Overview of SciLean, n-dimensional arrays, symbolic computation, and automatic differentiation.

- [Scientific Computing in Lean – Seminar at Cambridge University (09 May 2024)](https://www.youtube.com/watch?v=O12SZqIwYCk)  
  Covers optimization through differential equations, basic probabilistic programming, and the Walk on Spheres algorithm.


## Using SciLean

### Prerequisites

SciLean relies on **OpenBLAS** for accelerating numerical computations.  
You’ll need to have it installed on your system:

- **Ubuntu**:
  ```bash
  sudo apt-get install libopenblas-dev
  ```
- **macOS**:
  ```bash
  brew install openblas
  ```
- **Windows**: Currently not officially supported.


### Building SciLean

Clone and build the library with:

```bash
git clone https://github.com/lecopivo/SciLean.git
cd SciLean
lake exe cache get
lake build
```


### Setting Up Your Project with SciLean

To use `SciLean` in your own Lean project:

1. Add a `require` statement for `scilean`.
2. Set `moreLinkArgs` to point to your OpenBLAS library.

Here’s an example `lakefile.lean` for a project named `foo`:

```lean
import Lake
open Lake DSL System

def linkArgs :=
  if System.Platform.isWindows then
    panic! "Windows is not supported!"
  else if System.Platform.isOSX then
    #["-L/opt/homebrew/opt/openblas/lib", "-L/usr/local/opt/openblas/lib", "-lblas"]
  else -- Linux
    #["-L/usr/lib/x86_64-linux-gnu/", "-lblas", "-lm"]

package foo {
  moreLinkArgs := linkArgs
}

require scilean from git "https://github.com/lecopivo/SciLean" @ "v4.20.1"

@[default_target]
lean_lib Foo {
  roots := #[`Foo]
}
```

> **Note:** If your project uses `mathlib`, ensure compatibility with the `scilean` version. Alternatively, omit the explicit `mathlib` requirement, SciLean brings in a compatible version as a transitive dependency.

