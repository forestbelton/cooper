module IntDivides

import Data.ZZ
import Divides

IntDivides : ZZ -> ZZ -> Type
IntDivides a b = divides (absZ a) (absZ b)
