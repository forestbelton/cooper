module Expr

%default total

%elim data Expr : (n : Nat) -> Type where
  Val   : Int    -> Expr n
  Var   : Fin n  -> Expr n
  Add   : Expr n -> Expr n -> Expr n
  Scale : Int    -> Expr n -> Expr n

evalExpr : Vect n Int -> Expr n -> Int
evalExpr _  (Val v)     = v
evalExpr xs (Var x)     = index x xs
evalExpr xs (Add v u)   = evalExpr xs v + evalExpr xs u
evalExpr xs (Scale k v) = k * evalExpr xs v
