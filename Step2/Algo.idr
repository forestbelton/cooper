module Step2.Algo

import Data.ZZ

import Formulas.NNF
import Formulas.NotLess

import Step1.Pred
import Step3.Pred

%default total

andForm : a -> a -> NotLess a
andForm a b = And (Single a) (Single b)

orForm : a -> a -> NotLess a
orForm a b = Or (Single a) (Single b)

dedup : NNF (Step1.Pred.Pred n) -> NotLess (Step3.Pred.Pred n)
dedup True                          = True
dedup False                         = False
dedup (Single (PredEQ a b))         = andForm (PredLT a (inc b)) (PredLT b (inc a))
dedup (NotSingle (PredEQ a b))      = orForm (PredLT a b) (PredLT b a)
dedup (Single (PredLT a b))         = Single (PredLT a b)
dedup (NotSingle (PredLT a b))      = Single (PredLT b (inc a))
dedup (Single (PredDivides k a))    = Single (PredDivides k a)
dedup (NotSingle (PredDivides k a)) = Single (PredNotDivides k a)
dedup (And a b)                     = And (dedup a) (dedup b)
dedup (Or a b)                      = Or (dedup a) (dedup b)
