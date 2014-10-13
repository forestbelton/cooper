module Formulas.NNF

data NNF : Type -> Type where
  True      : NNF a
  False     : NNF a
  Single    : a -> NNF a
  NotSingle : a -> NNF a
  And       : NNF a -> NNF a -> NNF a
  Or        : NNF a -> NNF a -> NNF a
