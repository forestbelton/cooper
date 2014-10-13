module Step5.Algo

import Step1.Expr
import Step1.Pred
import Step4.Pred

import Formulas.NotLess

%default total

-- Left infinite projection

leftInfPred : Step4.Pred.Pred n -> NotLess (Step4.Pred.Pred n)
leftInfPred (PredLT _) = True
leftInfPred (PredGT _) = False
leftInfPred x          = Single x

leftInfForm : NotLess (Step4.Pred.Pred n) -> NotLess (Step4.Pred.Pred n)
leftInfForm (Single p) = leftInfPred p
leftInfForm (And a b)  = And (leftInfForm a) (leftInfForm b)
leftInfForm x          = x

-- delta = LCM of divisors in divisibility literals
deltaPred : Step4.Pred.Pred n -> Nat
deltaPred (PredDivides k _)    = absZ k
deltaPred (PredNotDivides l _) = absZ l
deltaPred _                    = 1

deltaForm : NotLess (Step4.Pred.Pred n) -> Nat
deltaForm (Single p) = deltaPred p
deltaForm (And a b)  = lcm (deltaForm a) (deltaForm b)
deltaForm (Or a b)   = lcm (deltaForm a) (deltaForm b)
deltaForm _          = 1

-- substition of x -> j in a literal
substPred : Step4.Pred.Pred (S n) -> Expr n -> Step1.Pred.Pred n
substPred (PredLT a) e           = PredLT e a
substPred (PredGT b) e           = PredLT b e
substPred (PredDivides k c)    e = PredDivides k (substExpr e c)
substPred (PredNotDivides l d) e = ?bla -- PredNotDivides l (substExpr e d)

-- F -> j -> F[j]
substForm : NotLess (Step4.Pred.Pred (S n)) -> Expr n -> NotLess (Step1.Pred.Pred n)
substForm True      _  = True
substForm False     _  = False
substForm (Single p) e = Single (substPred p e)
substForm (And a b) e  = And (substForm a e) (substForm a e)
substForm (Or a b)  e  = Or  (substForm a e) (substForm a e)

-- first major disjunct. F_{-\infty}[j], for 1 <= j <= delta
firstMajorDisjunct : Nat -> NotLess (Step4.Pred.Pred (S n)) -> NotLess (Step1.Pred.Pred n)
firstMajorDisjunct Z     _ = False
firstMajorDisjunct (S k) a = Or (substForm a (Val (Pos (S k)))) (firstMajorDisjunct k a)

-- B is the set of all terms b appearing in the form x' < b.
-- It's okay for B to be a list here because repeating items
-- in B do not change the meaning of the disjunct.
getBPred : Step4.Pred.Pred (S n) -> List (Expr n)
getBPred (PredGT b) = [b]
getBPred _          = []

getBForm : NotLess (Step4.Pred.Pred (S n)) -> List (Expr n)
getBForm (Single p) = getBPred p
getBForm (And a b)  = getBForm a ++ getBForm b
getBForm (Or a b)   = getBForm a ++ getBForm b
getBForm _          = []

-- iteration over B
secondMinorDisjunct : List (Expr n) -> Nat -> NotLess (Step4.Pred.Pred (S n)) -> NotLess (Step1.Pred.Pred n)
secondMinorDisjunct []        _ _ = False
secondMinorDisjunct (b :: bs) j e = Or (substForm e (Add b (Val (Pos j)))) (secondMinorDisjunct bs j e)

-- F[j + b], for 1 <= j <= delta and b in B
secondMajorDisjunct : Nat -> List (Expr n) -> NotLess (Step4.Pred.Pred (S n)) -> NotLess (Step1.Pred.Pred n)
secondMajorDisjunct Z     _  _ = False
secondMajorDisjunct (S k) bs a = Or (secondMinorDisjunct bs k a) (secondMajorDisjunct k bs a)

step5 : NotLess (Step4.Pred.Pred (S n)) -> NotLess (Step1.Pred.Pred n)
step5 a = Or left right
  where delta : Nat
        delta = deltaForm a
        left  = firstMajorDisjunct delta (leftInfForm a)
        right = secondMajorDisjunct delta (getBForm a) a
