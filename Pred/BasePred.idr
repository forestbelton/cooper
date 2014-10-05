module Pred.BasePred

import IntLT
import IntDivides
import Expr

%default total

%elim data BasePred : (n : Nat) -> Type where
  PredEQ      : Expr n -> Expr n -> BasePred n
  PredLT      : Expr n -> Expr n -> BasePred n
  PredDivides : Int    -> Expr n -> BasePred n

interpBasePred : Vect n Int -> BasePred n -> Type
interpBasePred xs (PredEQ a b)      = a = b
interpBasePred xs (PredLT a b)      = IntLT (evalExpr xs a) (evalExpr xs b)
interpBasePred xs (PredDivides k a) = IntDivides k (evalExpr xs a)
