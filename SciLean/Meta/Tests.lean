-- import SciLean.Prelude
-- import SciLean.Meta

-- -- Remove Lambda Let tests
-- -- It is crucial that all these are solvable by `by rmlamlet; simp; done`
-- -- TODO: Add tactic to check the expression does not contain any let or lambda
  
-- section 
--   variable (n m a b : Nat) (x : ℝ)
--   def test1 : 
--       (let k := n
--        k + k)
--       =
--       n + n
--   := by rmlamlet; simp; done

--   def test2 : 
--       (let k := n
--        let l := m
--        k + l)
--       =
--       n + m
--   := by rmlamlet; simp; done

--   def test3 : 
--       (do
--        let mut k := n
--        let mut l := m
--        k := l + k
--        l := k * l
--        k + l)
--       =
--       m + n + (m + n) * m
--   := by rmlamlet; simp; done

--   def test4 : (λ x : Nat => x) = id := by rmlamlet; simp; done
                
--   -- def test5 :
--   --     ((do
--   --      let mut x := x
--   --      for i in [0:n] do
--   --        x := x
--   --      x ) : ℝ)
--   --     = 
--   --     (swap
--   --     (comp bind
--   --       (swap
--   --         (swap (comp swap (swap forIn))
--   --           (const Nat (comp (bind (pure PUnit.unit)) (comp (const PUnit) (comp pure ForInStep.yield)))))
--   --         ([0:n])))
--   --     id x)
--   -- := by rmlamlet; simp; done

--   -- def funext_prop {α : Sort u} (a b : α) : (a = b) → ((a = b) = True) := by intro p; induction p; simp; done

--   -- def test6 {X} (x : X) (f : Nat → X → X) (g : X → X) :
--   --     ((do
--   --      let mut x := x
--   --      for i in [a:b:n] do
--   --        x := (f i x)
--   --      g x ) : X)
--   --     = 
--   --     (swap
--   --     (comp bind
--   --       (swap
--   --         (swap (comp swap (swap forIn))
--   --           (comp (comp (comp (bind (pure PUnit.unit)) (comp (const PUnit) (comp pure ForInStep.yield)))) f))
--   --         [a:b:n]))
--   --     g x)
--   -- := by rmlamlet; simp; simp[bind]; simp[pure];  simp; done

--   -- #check Bind

--   -- #check Std.Range.forIn

--   -- def test7 {X} (x : X) (f : Nat → X → X):
--   -- ((forIn ([a:b:n]) x fun i r => ForInStep.yield (f i r)) : X) =
--   --       ((swap (swap forIn x) ([a:b:n])
--   --         (comp (comp (comp (bind PUnit.unit) (comp (const PUnit) (comp pure ForInStep.yield)))) f)) : X)
--   -- := admit

-- end 
