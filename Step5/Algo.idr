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

-- B is the set of all terms b appearing in the form x' < b.
-- It's okay for B to be a list here because repeating items
-- in B do not change the meaning of the disjunct.
getBPred : Step4.Pred.Pred (S n) -> List (Expr n)
getBPred (PredGT b) = [b]
getBPred _          = []

getBForm : Form (Step4.Pred.Pred (S n)) -> List (Expr n)
getBForm (Single p) = getBPred p
getBForm (FAnd a b) = getBForm a ++ getBForm b
getBForm (FOr a b)  = getBForm a ++ getBForm b
getBForm _          = []

-- iteration over B
secondMinorDisjunct : List (Expr n) -> Nat -> Form (Step4.Pred.Pred (S n)) -> Form (Step1.Pred.Pred n)
secondMinorDisjunct []        _ _ = FFalse
secondMinorDisjunct (b :: bs) j e = FOr (substForm e (Add b (Val (Pos j)))) (secondMinorDisjunct bs j e)

-- F[j + b], for 1 <= j <= delta and b in B
secondMajorDisjunct : Nat -> List (Expr n) -> Form (Step4.Pred.Pred (S n)) -> Form (Step1.Pred.Pred n)
secondMajorDisjunct Z     _  _ = FFalse
secondMajorDisjunct (S k) bs a = FOr (secondMinorDisjunct bs k a) (secondMajorDisjunct k bs a)

step5 : Form (Step4.Pred.Pred (S n)) -> Form (Step1.Pred.Pred n)
step5 a = FOr left right
  where delta : Nat
        delta = deltaForm a
        left  = firstMajorDisjunct delta (leftInfForm a)
        right = secondMajorDisjunct delta (getBForm a) a
