import Lake
open Lake DSL

package SciLean {
  dependencies := #[{
    name := `mathlib
    src := Source.git "https://github.com/lecopivo/mathlib4.git" "master"
  }]
}
