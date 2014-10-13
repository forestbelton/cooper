module Literals.BaseLit

import Data.ZZ
import Step1.Expr

data BaseLit : (n : Nat) -> Type where
  Equals   : Expr n -> Expr n -> BaseLit n
  LessThan : Expr n -> Expr n -> BaseLit n
  Divides  : ZZ     -> Expr n -> BaseLit n
