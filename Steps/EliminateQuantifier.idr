module Steps.EliminateQuantifier

import Step1.Expr

import Literals.Dedup
import Literals.Reduced

import Formulas.NotLess

%default total

-- Left infinite projection

leftInfPred : Reduced n -> NotLess (Reduced n)
leftInfPred (LessThan _)    = True
leftInfPred (GreaterThan _) = False
leftInfPred x               = Single x

leftInfForm : NotLess (Reduced n) -> NotLess (Reduced n)
leftInfForm (Single p) = leftInfPred p
leftInfForm (And a b)  = And (leftInfForm a) (leftInfForm b)
leftInfForm x          = x

-- delta = LCM of divisors in divisibility literals
deltaPred : Reduced n -> Nat
deltaPred (Divides k _)    = absZ k
deltaPred (NotDivides l _) = absZ l
deltaPred _                = 1

deltaForm : NotLess (Reduced n) -> Nat
deltaForm (Single p) = deltaPred p
deltaForm (And a b)  = lcm (deltaForm a) (deltaForm b)
deltaForm (Or a b)   = lcm (deltaForm a) (deltaForm b)
deltaForm _          = 1

-- substition of x -> j in a literal
substPred : Reduced (S n) -> Expr n -> Dedup n
substPred (LessThan a)     e = LessThan e a
substPred (GreaterThan b)  e = LessThan b e
substPred (Divides k c)    e = Divides k (substExpr e c)
substPred (NotDivides l d) e = ?bla -- PredNotDivides l (substExpr e d)

-- F -> j -> F[j]
substForm : NotLess (Reduced (S n)) -> Expr n -> NotLess (Dedup n)
substForm True      _  = True
substForm False     _  = False
substForm (Single p) e = Single (substPred p e)
substForm (And a b) e  = And (substForm a e) (substForm a e)
substForm (Or a b)  e  = Or  (substForm a e) (substForm a e)

-- first major disjunct. F_{-\infty}[j], for 1 <= j <= delta
firstMajorDisjunct : Nat -> NotLess (Reduced (S n)) -> NotLess (Dedup n)
firstMajorDisjunct Z     _ = False
firstMajorDisjunct (S k) a = Or (substForm a (Val (Pos (S k)))) (firstMajorDisjunct k a)

-- B is the set of all terms b appearing in the form x' < b.
-- It's okay for B to be a list here because repeating items
-- in B do not change the meaning of the disjunct.
getBPred : Reduced (S n) -> List (Expr n)
getBPred (GreaterThan b) = [b]
getBPred _               = []

getBForm : NotLess (Reduced (S n)) -> List (Expr n)
getBForm (Single p) = getBPred p
getBForm (And a b)  = getBForm a ++ getBForm b
getBForm (Or a b)   = getBForm a ++ getBForm b
getBForm _          = []

-- iteration over B
secondMinorDisjunct : List (Expr n) -> Nat -> NotLess (Reduced (S n)) -> NotLess (Dedup n)
secondMinorDisjunct []        _ _ = False
secondMinorDisjunct (b :: bs) j e = Or (substForm e (Add b (Val (Pos j)))) (secondMinorDisjunct bs j e)

-- F[j + b], for 1 <= j <= delta and b in B
secondMajorDisjunct : Nat -> List (Expr n) -> NotLess (Reduced (S n)) -> NotLess (Dedup n)
secondMajorDisjunct Z     _  _ = False
secondMajorDisjunct (S k) bs a = Or (secondMinorDisjunct bs k a) (secondMajorDisjunct k bs a)

step5 : NotLess (Reduced (S n)) -> NotLess (Dedup n)
step5 a = Or left right
  where delta : Nat
        delta = deltaForm a
        left  = firstMajorDisjunct delta (leftInfForm a)
        right = secondMajorDisjunct delta (getBForm a) a
