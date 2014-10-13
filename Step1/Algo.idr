module Step1.Algo

import Formulas.Initial
import Formulas.NNF

%default total

mutual
  nnf : Initial a -> NNF a
  nnf True       = True
  nnf False      = False
  nnf (Single p) = Single p
  nnf (Not a)    = nnf' a
  nnf (And a b)  = And (nnf a) (nnf b)
  nnf (Or a b)   = Or (nnf a) (nnf b)

  nnf' : Initial a -> NNF a  
  nnf' True       = False
  nnf' False      = True
  nnf' (Single p) = NotSingle p
  nnf' (Not a)    = nnf a
  nnf' (And a b)  = Or (nnf' a) (nnf' b)
  nnf' (Or a b)   = And (nnf' a) (nnf' b)
