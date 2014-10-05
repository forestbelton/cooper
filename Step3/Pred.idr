module Step3.Pred

import Data.ZZ

import IntLT
import IntDivides
import Step1.Expr

%default total

%elim data Pred : (n : Nat) -> Type where
  PredLT         : Expr n -> Expr n -> Pred n
  PredDivides    : ZZ     -> Expr n -> Pred n
  PredNotDivides : ZZ     -> Expr n -> Pred n

interpPred : Vect n ZZ -> Pred n -> Type
interpPred xs (PredLT a b)         = IntLT (evalExpr xs a) (evalExpr xs b)
interpPred xs (PredDivides k a)    = IntDivides k (evalExpr xs a)
interpPred xs (PredNotDivides k a) = Not (IntDivides k (evalExpr xs a))
