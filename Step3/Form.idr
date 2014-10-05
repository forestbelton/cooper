module Step3.Form

%default total

%elim data Form : Type -> Type where
  FTrue  : Form a
  FFalse : Form a
  Single : a -> Form a
  FAnd   : Form a -> Form a -> Form a
  FOr    : Form a -> Form a -> Form a

interp : (a -> Type) -> Form a -> Type
interp _ FTrue      = ()
interp _ FFalse     = _|_
interp f (Single p) = f p
interp f (FAnd a b) = (interp f a, interp f b)
interp f (FOr a b)  = Either (interp f a) (interp f b)
