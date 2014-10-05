module Form

import Pred
%default total

%elim data Form : Type -> Type where
  FTrue  : Form a
  FFalse : Form a
  Single : Pred a => a -> Form a
  FNot   : Form a -> Form a
  FAnd   : Form a -> Form a -> Form a
  FOr    : Form a -> Form a -> Form a

interp : Pred a => Form a -> Type
interp FTrue      = ()
interp FFalse     = _|_
interp (Single p) = interpPred p
interp (FNot a)   = Not (interp a)
interp (FAnd a b) = (interp a, interp b)
interp (FOr a b)  = Either (interp a) (interp b)
