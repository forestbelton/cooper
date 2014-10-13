module Formulas.Initial

data Initial : Type -> Type where
  True   : Initial a
  False  : Initial a
  Single : a -> Initial a
  Not    : Initial a -> Initial a
  And    : Initial a -> Initial a -> Initial a
  Or     : Initial a -> Initial a -> Initial a
