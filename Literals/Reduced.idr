module Literals.Reduced

import Step1.Expr

data Reduced : (n : Nat) -> Type where
  LessThan    : Expr n -> Reduced (S n)
  GreaterThan : Expr n -> Reduced (S n)
  Divides     : ZZ     -> Expr n -> Reduced n
  NotDivides  : ZZ     -> Expr n -> Reduced n
