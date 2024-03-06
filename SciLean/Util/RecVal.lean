namespace SciLean


-- Pretty printing of `Nat.recOn`
syntax "rec_val" term ppLine "| " term " => " term ppLine "| " term ", " term " => "  term : term

@[app_unexpander Nat.recOn]
def unexpandNatRecOn : Lean.PrettyPrinter.Unexpander
  | `($(_) $_mot $n $base $succ) =>
    match succ with
    | `(fun ($m:ident : $_Y:term) ($prev:ident : $_P:term) => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => $b)
    | `(fun $m:ident $prev:ident => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => $b)
    | `(fun ($m:ident : $_Y:term) ($prev:ident : $_P:term) $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | `(fun $m:ident $prev:ident $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | _ => throw ()
  | `($(_) $n $base $succ) =>
    match succ with
    | `(fun ($m:ident : $_Y:term) ($prev:ident : $_P:term) => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => $b)
    | `(fun $m:ident $prev:ident => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => $b)
    | `(fun ($m:ident : $_Y:term) ($prev:ident : $_P:term) $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | `(fun $m:ident $prev:ident $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | _ => throw ()
  | _ => throw ()

-- Pretty printing of `Nat.rec`
@[app_unexpander Nat.rec]
def unexpandNatRec : Lean.PrettyPrinter.Unexpander
  | `($(_) $_mot $base $succ $n) =>
    match succ with
    | `(fun ($m:ident : $_Y:term) ($prev:ident : $_P:term) => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => $b)
    | `(fun $m:ident $prev:ident => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => $b)

    | `(fun ($m:ident : $_Y:term) ($prev:ident : $_P:term) $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | `(fun $m:ident $prev:ident $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | _ => throw ()
  | `($(_) $base $succ $n) =>
    match succ with
    | `(fun ($m:ident : $_Y:term) ($prev:ident : $_P:term) => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => $b)
    | `(fun $m:ident $prev:ident => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => $b)

    | `(fun ($m:ident : $_Y:term) ($prev:ident : $_P:term) $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | `(fun $m:ident $prev:ident $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | _ => throw ()
  | _ => throw ()
