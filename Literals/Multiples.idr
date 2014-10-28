module Literals.Multiples

import Step1.Expr

data Multiples : (n : Nat) -> Type where
  LessThan    : ZZ -> Expr (S n) -> Multiples n       -- h x < t
  GreaterThan : Expr (S n) -> ZZ -> Multiples n       -- t < h x
  Divides     : ZZ -> ZZ -> Expr (S n) -> Multiples n -- k | h x + t
  NotDivides  : ZZ -> ZZ -> Expr (S n) -> Multiples n -- ~(k | h x + t)
