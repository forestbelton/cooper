module Formulas.NotLess

data NotLess : Type -> Type where
  True   : NotLess a
  False  : NotLess a
  Single : a -> NotLess a
  And    : NotLess a -> NotLess a -> NotLess a
  Or     : NotLess a -> NotLess a -> NotLess a
