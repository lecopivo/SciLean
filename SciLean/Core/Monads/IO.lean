import SciLean.Util.SorryProof

/-- When we want to differentiate w.r.t to IO.Ref we need to have a separate IO.Ref
that holds the derivative. We define IO.DRef which is just a IO.Ref but tied to
particular IO.Ref through its type.
-/
def IO.DRef (a : IO.Ref α) : Type := IO.Ref α
def IO.Ref.mkDRef (a : IO.Ref α) (da : α) : BaseIO (IO.DRef a) := IO.mkRef da
def IO.DRef.get {a : IO.Ref α} (da : IO.DRef a) : IO α := ST.Ref.get da


-- !!!WARNING!!!
-- We somehow need to guarantee that there is at most one instance of this class
-- This is not enforced and having two different instances could lead to inconsistencies
class HasDRef (a : IO.Ref α) where
  dref : IO.DRef a

def IO.Ref.getDRef (a : IO.Ref α) [HasDRef a] : IO.DRef a := HasDRef.dref

-- We just postulate the existence of differentiability and derivative of IO functions
-- Properties of individual functions will be stated as axioms
-- TODO: parametrize over vector spaces
opaque IsDifferentiableIO (f : X → IO Y) : Prop
opaque fwdDerivIO (f : X → IO Y) : X → X → IO (Y × Y)

axiom Bind.bind.arg_x.fwdDerivIO_rule {X Y Z : Type}
  (f : Y → IO Z) (g : X → IO Y)
  (hf : IsDifferentiableIO f) (hg : IsDifferentiableIO g)
  : fwdDerivIO (fun x => g x >>= f)
    =
    (fun x dx => do
       let ydy ← fwdDerivIO g x dx
       fwdDerivIO f ydy.1 ydy.2)

--TODO: axiom for pure and pair



axiom IO.DRef.get.arg.IsDifferentiableIO_rule {α} (a : IO.Ref α) [HasDRef a]
  : IsDifferentiableIO (fun _ : Unit => a.get)

axiom IO.DRef.get.arg.fwdDerivIO_rule {α} (a : IO.Ref α) [HasDRef a]
  : fwdDerivIO (fun _ : Unit => a.get)
    =
    (fun _ _ => do
      pure (←a.get, ← a.getDRef.get))

-- TODO: axioms for set




initialize a : IO.Ref Nat ← IO.mkRef 1
initialize da : IO.DRef a ← a.mkDRef 10
