import SciLean

open SciLean

variable (i : Idx 10)

-- The `setElem 0 i dy True.intro` is bad!
/--
info: HasRevFDerivUpdate Float (fun x => x.1.2[i]) fun x =>
  have x₁ := x.1;
  have x₁ := x₁.2;
  have x₁ := x₁[i];
  (x₁, fun dy dx =>
    have dx₁ := dx.1;
    have dx₂ := dx.2;
    have x' := setElem 0 i dy True.intro;
    have dx' := dx₁.1;
    have dy' := dx₁.2;
    have dx₂_1 := dy' + x';
    ((dx', dx₂_1), dx₂)) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate Float (fun (x : (Float^[10] × Float^[10]) × Float) => x.1.2[i]) _)
  rewrite_by
    data_synth


-- This is good code
/--
info: HasRevFDerivUpdate Float (fun x => x.2.1[i]) fun x =>
  have x₁ := x.2.1;
  have x₁ := x₁[i];
  (x₁, fun dy dx =>
    have dx₁ := dx.2.1;
    have dx₂₁ := dx.1;
    have dx₂₂ := dx.2.2;
    have xi := dx₁[i];
    have x := setElem dx₁ i (xi + dy) True.intro;
    (dx₂₁, x, dx₂₂)) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate Float (fun (x : Float^[10] × (Float^[10] × Float)) => x.2.1[i]) _)
  rewrite_by
    data_synth
