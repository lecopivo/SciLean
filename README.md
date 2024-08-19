# SciLean: Scientific Computing in Lean

  Library for scientific computing such as solving differential equations, optimization or machine learning written in [Lean](http://leanprover.github.io/). This library is in an *early stage of development* and at its current stage is just a proof of concept on how Lean can be used for scientific computing.

Lean is an expressive functional programming language that allows to formalize the mathematics behind these computations. This can offer several benefits:

- Code transformation and optimization guided by formalization of underlining mathematics, like automatic differentiation, algebraic simplification, fine control of used approximations or execution scheduling.
- First class symbolic computation. Any function can be purely symbolic, functions like `gradient`, `integral` or `limit` are inherently non-computable. However, they carry meaning what the program should be doing and we provide tools to manipulate them or approximate them with actually computable function.
- Code generation based on formal specification. Many problems any scientific computing or machine learning can be stated very easily e.g. find a minimizer of a function. We then provide tools how to turn such specification into a runnable code satisfying the specification, usually in an appropriate limit of used approximations.
- Catalogization of numerical methods.

  In short, mathematics is the ultimate abstraction for numerical computing and Lean can understand mathematics. Hopefully, using Lean will allow us to create really powerful and extensible library for scientific computing.

  
# Installation and running examples/tests

As we are using Lean programming language, you need Lean's version manager =elan=. Follow its installation [instructions](https://github.com/leanprover/elan#installation).

Getting and building SciLean simply:
```
git clone https://github.com/lecopivo/SciLean.git
cd SciLean
lake exe cache get
lake build
```

To run examples:
```
lake build HarmonicOscillator && .lake/build/bin/HarmonicOscillator
lake build WaveEquation && .lake/build/bin/WaveEquation 
```
Other examples in =examples= directory do not currently work.


To get an idea how SciLean works have a look at explanation of the harmonic oscillator [example](https://lecopivo.github.io/scientific-computing-lean/Examples/Harmonic-Oscillator/#Scientific-Computing-in-Lean--Examples--Harmonic-Oscillator).
