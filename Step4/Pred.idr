module Step4.Pred

import Step1.Expr

%default total

%elim data Pred : (n : Nat) -> Type where
  PredLT         : Expr n -> Pred (S n)
  PredGT         : Expr n -> Pred (S n)
  PredDivides    : ZZ -> Expr n -> Pred n
  PredNotDivides : ZZ -> Expr n -> Pred n
