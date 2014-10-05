module NNF

import Data.ZZ
import Form
import Pred.BasePred

%default total

mutual
  nnf : Form a -> Form a
  nnf (FNot a)   = nnf' a
  nnf (FAnd a b) = FAnd (nnf a) (nnf b)
  nnf (FOr a b)  = FOr (nnf a) (nnf b)
  nnf x          = x
  
  nnf' : Form a -> Form a
  nnf' FTrue      = FFalse
  nnf' FFalse     = FTrue
  nnf' (Single p) = FNot (Single p)
  nnf' (FNot a)   = nnf a
  nnf' (FAnd a b) = FOr (nnf' a) (nnf' b)
  nnf' (FOr a b)  = FAnd (nnf' a) (nnf' b)

nnfInterp : (f : Form (BasePred n)) -> (xs : Vect n ZZ) -> interp (interpBasePred xs) f = interp (interpBasePred  xs) (nnf f)
nnfInterp FTrue      _  = refl
nnfInterp FFalse     _  = refl
nnfInterp (Single _) _  = refl
nnfInterp (FNot a)   _  = believe_me _|_ -- TODO
nnfInterp (FAnd a b) xs = let ihf_0 = nnfInterp a xs
                              ihf_1 = nnfInterp b xs in
                          rewrite ihf_0 in
                          rewrite ihf_1 in refl
nnfInterp (FOr a b)  xs = let ihf_0 = nnfInterp a xs
                              ihf_1 = nnfInterp b xs in
                          rewrite ihf_0 in
                          rewrite ihf_1 in refl
