module Pred.BasePred

import Expr

%default total

%elim data BasePred : Type where
  PredEQ      : Expr -> Expr -> BasePred
  PredLT      : Expr -> Expr -> BasePred
  PredDivides : Int  -> Expr -> BasePred

interpBasePred : BasePred -> Type
interpBasePred (PredEQ a b)      = a = b
interpBasePred (PredLT a b)      = believe_me _|_ -- LT a b
interpBasePred (PredDivides k a) = believe_me _|_ -- divides k a
