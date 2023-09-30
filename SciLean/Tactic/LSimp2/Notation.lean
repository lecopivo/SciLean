import Lean

namespace SciLean.Tactic.LSimp

open Lean.Parser.Tactic

syntax (name := lsimp) "lsimp" (config)? (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")? (location)? : tactic

syntax (name := lsimp_conv) "lsimp" (config)? (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")? : conv

syntax (name := ldsimp) "ldsimp" (config)? (discharger)? (&" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*) "]")? (location)? : tactic

syntax (name := ldsimp_conv) "ldsimp" (config)? (discharger)? (&" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*) "]")? : conv
