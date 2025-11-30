# SciLean Development Guidelines

## Build Commands
- Build entire project: `lake build`
- Run tests: `lake test`
- Test a specific file: `lake build test.file_name` (e.g., `lake build test.calculus.revFDeriv_test`)
- Run an example: `lake build ExampleName && .lake/build/bin/ExampleName` (e.g., `lake build HarmonicOscillator && .lake/build/bin/HarmonicOscillator`)

## Code Style Guidelines
- **Indentation**: 2 spaces
- **Naming**: CamelCase for types/classes, snake_case for variables, Unicode for mathematical symbols
- **Imports**: Organized at top by dependency, open primary namespace
- **Types**: Use typeclasses for mathematical abstractions, explicit type constraints where needed
- **Documentation**: `/--` blocks with markdown, mathematical notation where appropriate
- **Attributes**: Use `@[simp]`, `@[fun_trans]`, `@[data_synth]` for optimization rules
- **Error handling**: Use dependent types and type constraints over runtime checks

## Conventions
- Proofs use the `by` syntax with tactic blocks
- Mathematical properties follow the theorem naming pattern `operation.arg_name.property_rule`
- Make heavy use of metaprogramming for tactics and automation
- Clear distinction between forward and reverse mode differentiation in naming
- Add existing imports as comments when disabling them