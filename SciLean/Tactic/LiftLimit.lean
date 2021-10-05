



-- This will be usefull

-- partial def modifySubExpression (e : Expr) (test : Expr → Bool) (replace : Expr → MetaM Expr) : MetaM Expr := do
-- if (test e) then
--   (replace e)
-- else
-- match e with
--  | Expr.app f x d => do (mkApp (← (modifySubExpression f test replace)) (← (modifySubExpression x test replace)))
--  | Expr.lam n x b d => Expr.lam n x (← modifySubExpression b test replace) d  -- lambdaTelescope e fun xs b => do (modifySubExpression b test replace)
--  | _ => e



