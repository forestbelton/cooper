module Step2.Algo

import Data.ZZ

import Formulas.NNF
import Formulas.NotLess

import Literals.BaseLit
import Literals.Dedup

%default total

andForm : a -> a -> NotLess a
andForm a b = And (Single a) (Single b)

orForm : a -> a -> NotLess a
orForm a b = Or (Single a) (Single b)

dedup : NNF (BaseLit n) -> NotLess (Dedup n)
dedup True                       = True
dedup False                      = False
dedup (Single (Equals a b))      = andForm (LessThan a (inc b)) (LessThan b (inc a))
dedup (NotSingle (Equals a b))   = orForm (LessThan a b) (LessThan b a)
dedup (Single (LessThan a b))    = Single (LessThan a b)
dedup (NotSingle (LessThan a b)) = Single (LessThan b (inc a))
dedup (Single (Divides k a))     = Single (Divides k a)
dedup (NotSingle (Divides k a))  = Single (NotDivides k a)
dedup (And a b)                  = And (dedup a) (dedup b)
dedup (Or a b)                   = Or (dedup a) (dedup b)
