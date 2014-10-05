module Step1.Pred

import Data.ZZ

import IntLT
import IntDivides
import Step1.Expr

%default total

%elim data Pred : (n : Nat) -> Type where
  PredEQ      : Expr n -> Expr n -> Pred n
  PredLT      : Expr n -> Expr n -> Pred n
  PredDivides : ZZ     -> Expr n -> Pred n

interpPred : Vect n ZZ -> Pred n -> Type
interpPred xs (PredEQ a b)      = a = b
interpPred xs (PredLT a b)      = IntLT (evalExpr xs a) (evalExpr xs b)
interpPred xs (PredDivides k a) = IntDivides k (evalExpr xs a)
