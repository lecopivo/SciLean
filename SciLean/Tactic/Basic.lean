
namespace Lean.Parser.Tactic.Conv

  macro "no_op" : conv => `(tactic' => skip)

  syntax "repeat' " convSeq : conv
  macro_rules
    | `(conv| repeat' $seq) => `(conv| first | ($seq); repeat' $seq | no_op)


end Lean.Parser.Tactic.Conv

