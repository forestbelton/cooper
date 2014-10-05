module Pred.BasePred

import Data.ZZ
import IntLT
import IntDivides
import Expr

%default total

%elim data BasePred : (n : Nat) -> Type where
  PredEQ      : Expr n -> Expr n -> BasePred n
  PredLT      : Expr n -> Expr n -> BasePred n
  PredDivides : ZZ     -> Expr n -> BasePred n

interpBasePred : Vect n ZZ -> BasePred n -> Type
interpBasePred xs (PredEQ a b)      = a = b
interpBasePred xs (PredLT a b)      = IntLT (evalExpr xs a) (evalExpr xs b)
interpBasePred xs (PredDivides k a) = IntDivides k (evalExpr xs a)
