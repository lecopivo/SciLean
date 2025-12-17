import SciLean.Data.ArrayOperations.Operations.GetElem
import SciLean.Data.DataArray.Float
import SciLean.Data.DataArray.Algebra

open SciLean

variable {n} (i : Idx n) (j : Idx 3)

/--
info: HasRevFDeriv Float (fun x => x[i]) fun x =>
  (x[i], fun xi =>
    have x' := setElem 0 i xi True.intro;
    x') : Prop
-/
#guard_msgs in
#check (HasRevFDeriv Float (fun x : Float^[n] => x[i]) _ ) rewrite_by data_synth


/--
info: HasRevFDeriv Float (fun x => x[(i, j)]) fun x =>
  (x[(i, j)], fun xi =>
    have x' := setElem 0 (i, j) xi True.intro;
    x') : Prop
-/
#guard_msgs in
#check (HasRevFDeriv Float (fun x : Float^[n,3] => x[i,j]) _ ) rewrite_by data_synth


/--
info: HasRevFDeriv Float (fun x => x[(i, j)]) fun x =>
  (x[(i, j)], fun xi =>
    have x' := setElem 0 (i, j) xi True.intro;
    x') : Prop
-/
#guard_msgs in
#check (HasRevFDeriv Float (fun x : Float^[3]^[n] => x[i,j]) _ ) rewrite_by data_synth


-- this is broken!!!
-- some serious issue with type classes :(
-- #check (HasRevFDeriv Float (fun x : Float^[3]^[n] => x[i]) _ ) rewrite_by data_synth
