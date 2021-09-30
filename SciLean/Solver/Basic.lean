import SciLean.Basic

abbrev SolverTag := String

inductive SolverParm where
  | nat (n : Nat) : SolverParm
  | float (f : Float) : SolverParm
  | string (s : String) : SolverParm  

inductive Solver : Type _  → Type _
  | pure {α : Type u} (a : α) : Solver α
  | limit {α β : Type u} (lim : Nat → α) (f : α → Solver β) (tag : SolverTag) (help : String) : Solver β
  | check {α : Type u} {P : Prop} [Decidable P] (f : P → Solver α) (help : String) : Solver α
  | promise {α : Type u} {P : Prop} (f : P → Solver α) (help : String) : Solver α
  | profile {α β : Type u} (x : Solver α) (f : α → Solver β) (help : String) : Solver β
  | bind {α β : Type u} (a : Solver α) (f : α → Solver β) : Solver β
  | pair {α β γ : Type u} (val : Solver α) (val' : Solver β) (f : α → β → γ) : Solver γ

def Impl {α} (a : α) := Solver α
def finish_impl {α} (a : α) : Impl a := Solver.pure a

namespace Solver

  def run! {α} (a : Solver α) (parms : Array (SolverTag × SolverParm)) : IO α :=
  match a with
    | pure a => a
    | limit lim f tag help => do
        let parm := (parms.find? (λ p => p.1 == tag))
        match parm with
          | none => throw (IO.userError s!"Could not find parameter with tag: '{tag}'!")
          | some a => 
              match a.2 with
                | SolverParm.nat n => run! (f (lim n)) parms 
                | _ => throw (IO.userError s!"Invalid parameter type!")
    | @check _ _ h f help => 
        match h with 
          | isTrue h => run! (f h) parms
          | isFalse h => throw (IO.userError s!"Failed check: {help}.")
    | promise f help => run! (f sorry) parms
    | profile x f help => 
                          let x := (run! x parms)
                          timeit help do (run! (f (← x)) parms)
    | bind g f => do run! (f (← run! g parms)) parms 
    | pair val val' f => do (f (← run! val parms) (← run! val' parms))

  -- def map (f : α → β) : Solver α → Solver β
  --   | (Solver.pure) val => pure (f val)
  --   | (Solver.lim pre post tag) => lim pre (λ a => f (post a)) tag
  --   | (Solver.bind val g) => bind val (λ x => map f (g x))
  --   | (Solver.pair val val' post) => pair val val' (λ a b => f (post a b))

  -- def seq {α β : Type u} (f : Solver (α → β)) (val : Unit → Solver α) : Solver β := pair f (val ()) (λ f x => f x)

  -- instance : Monad Solver :=
  -- {
  --   pure := pure, 
  --   map := map,
  --   seq := seq,
  --   bind := bind
  -- }

  -- namespace Parm
  --   def lift_nat (f : Nat → α)  (p : Parm) : Option α := 
  --     match p with
  --       | nat n => some (f n)
  --       | _ => none
    
  --   def lift_float (f : Float → α) (p : Parm) : Option α := 
  --     match p with
  --       | float x => some (f x)
  --       | _ => none
    
  --   def lift_string (f : String → α) (p : Parm) : Option α := 
  --     match p with
  --       | string s => some (f s)
  --       | _ => none
  -- end Parm
  
end Solver
