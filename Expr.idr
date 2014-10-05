module Expr

%default total

%elim data Expr : Type where
  Val   : Int -> Expr
--  Var   : Int -> Expr
  Add   : Expr -> Expr -> Expr
  Scale : Int  -> Expr -> Expr
