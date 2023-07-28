import SciLean.FunctionSpaces.ContinuousLinearMap.Basic


namespace SciLean.ContinuousLinearMap


macro "fun " x:ident " =>L[" R:term "] " b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun $x => $b) (by fprop))

macro "fun " x:ident " : " X:term " =>L[" R:term "] " b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun ($x : $X) => $b) (by fprop))

macro "fun " "(" x:ident " : " X:term ")" " =>L[" R:term "] " b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun ($x : $X) => $b) (by fprop))

@[app_unexpander ContinuousLinearMap.mk'] def unexpandContinuousLinearMapMk : Lean.PrettyPrinter.Unexpander

  | `($(_) $R $f:term $hf:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(fun $x' =>L[$R] $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(fun ($x' : $ty) =>L[$R] $b)
    | `(fun $x':ident : $ty => $b:term) => `(fun $x' : $ty =>L[$R] $b)
    | _  => throw ()
  | _  => throw ()


