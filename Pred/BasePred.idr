module Pred.BasePred

import Pred
import Expr

%default total

data BasePred : Type where
  PredEQ      : Expr -> Expr -> BasePred
  PredLT      : Expr -> Expr -> BasePred
  PredDivides : Int  -> Expr -> BasePred

instance Pred BasePred where
  interpPred (PredEQ a b)      = a = b
  interpPred (PredLT a b)      = believe_me _|_ -- LT a b
  interpPred (PredDivides k a) = believe_me _|_ -- divides k a
