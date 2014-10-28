module Literals.Reduced

import Step1.Expr

data Reduced : (n : Nat) -> Type where
  LessThan    : Expr (S n) -> Reduced n
  GreaterThan : Expr (S n) -> Reduced n
  Divides     : ZZ     -> Expr (S n) -> Reduced n
  NotDivides  : ZZ     -> Expr (S n) -> Reduced n
