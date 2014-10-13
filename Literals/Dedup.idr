module Literals.Dedup

import Data.ZZ
import Step1.Expr

data Dedup : (n : Nat) -> Type where
  LessThan   : Expr n -> Expr n -> Dedup n
  Divides    : ZZ     -> Expr n -> Dedup n
  NotDivides : ZZ     -> Expr n -> Dedup n
