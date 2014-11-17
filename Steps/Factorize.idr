module Steps.Factorize

import Formulas.NotLess
import Literals.Multiples
import Literals.Reduced

%default total

-- lcm { h : h is a coefficient of x in F[x] }
lcmPred : Multiples n -> Nat
lcmPred (LessThan h _)      = absZ h
lcmPred (GreaterThan _ h)   = absZ h
lcmPred (Divides _ h _)     = absZ h
lcmPred (NotDivides _ h _)  = absZ h

lcmForm : NotLess (Multiples n) -> Nat
lcmForm (Single p) = lcmPred p
lcmForm (And a b)  = lcm (lcmForm a) (lcmForm b)
lcmForm (Or a b)   = lcm (lcmForm a) (lcmForm b)
lcmForm _          = 1

zzDiv : Nat -> ZZ -> ZZ
zzDiv p (Pos q)  = Pos (divNat p q)
zzDiv p (NegS q) = case divNat p (S q) of
  Z   => Pos Z
  S k => NegS k

factorizePred : Nat -> Multiples n -> Reduced n
factorizePred n (LessThan h e)     = LessThan (Scale (zzDiv n h) e)
factorizePred n (GreaterThan e h)  = GreaterThan (Scale (zzDiv n h) e)
factorizePred n (Divides k h e)    = Divides (multZ k h') (Scale h' e)
  where h' = zzDiv n h
factorizePred n (NotDivides k h e) = Divides (multZ k h') (Scale h' e)
  where h' = zzDiv n h

factorize' : Nat -> NotLess (Multiples n) -> NotLess (Reduced n)
factorize' _ True       = True
factorize' _ False      = False
factorize' n (Single p) = Single (factorizePred n p)
factorize' n (And a b)  = And (factorize' n a) (factorize' n b)
factorize' n (Or a b)   = Or (factorize' n a) (factorize' n b)

factorize : NotLess (Multiples n) -> NotLess (Reduced n)
factorize f = let l = lcmForm f in
  And (Single (Divides (Pos l) (Var fZ))) (factorize' l f)
