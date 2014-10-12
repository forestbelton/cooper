module Step5.Algo

import Step1.Expr
import Step1.Pred
import Step4.Pred
import Step3.Form

%default total

-- Left infinite projection

leftInfPred : Step4.Pred.Pred n -> Form (Step4.Pred.Pred n)
leftInfPred (PredLT _) = FTrue
leftInfPred (PredGT _) = FFalse
leftInfPred x          = Single x

leftInfForm : Form (Step4.Pred.Pred n) -> Form (Step4.Pred.Pred n)
leftInfForm (Single p) = leftInfPred p
leftInfForm (FAnd a b) = FAnd (leftInfForm a) (leftInfForm b)
leftInfForm x          = x

-- delta = LCM of divisors in divisibility literals
lcmZZ : ZZ -> ZZ -> Nat
lcmZZ a b = ?lcmZZImpl

deltaPred : Step4.Pred.Pred n -> Nat
deltaPred (PredDivides k _)    = absZ k
deltaPred (PredNotDivides l _) = absZ l
deltaPred _                    = 1

deltaForm : Form (Step4.Pred.Pred n) -> Nat
deltaForm (Single p)  = deltaPred p
deltaForm (FAnd a b)  = lcm (deltaForm a) (deltaForm b)
deltaForm (FOr a b)   = lcm (deltaForm a) (deltaForm b)
deltaForm _           = 1

-- substition of x -> j in a literal
substPred : Step4.Pred.Pred (S n) -> Expr n -> Step1.Pred.Pred n
substPred (PredLT a) e           = PredLT e a
substPred (PredGT b) e           = PredLT b e
substPred (PredDivides k c)    e = PredDivides k (substExpr e c)
substPred (PredNotDivides l d) e = ?bla -- PredNotDivides l (substExpr e d)

-- F -> j -> F[j]
substForm : Form (Step4.Pred.Pred (S n)) -> Expr n -> Form (Step1.Pred.Pred n)
substForm FTrue      _ = FTrue
substForm FFalse     _ = FFalse
substForm (Single p) e = Single (substPred p e)
substForm (FAnd a b) e = FAnd (substForm a e) (substForm a e)
substForm (FOr a b)  e = FOr (substForm a e) (substForm a e)

-- first major disjunct. F_{-\infty}[j], for 1 <= j <= delta
firstMajorDisjunct : Nat -> Form (Step4.Pred.Pred (S n)) -> Form (Step1.Pred.Pred n)
firstMajorDisjunct Z     _ = FFalse
firstMajorDisjunct (S k) a = FOr (substForm a (Val (Pos (S k)))) (firstMajorDisjunct k a)
