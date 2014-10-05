module IntLT

import Data.ZZ

IntLT : ZZ -> ZZ -> Type
IntLT (Pos a) (Pos b)   = LT a b
IntLT (Pos a) (NegS b)  = _|_
IntLT (NegS a) (Pos b)  = ()
IntLT (NegS a) (NegS b) = LT b a
