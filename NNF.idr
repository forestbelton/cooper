module NNF

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

nnfInterp : (f : Form BasePred) -> interp f = interp (nnf f)
nnfInterp FTrue      = refl
nnfInterp FFalse     = refl
nnfInterp (Single _) = refl
nnfInterp (FNot a)   = believe_me _|_ -- TODO
nnfInterp (FAnd a b) = let ihf_0 = nnfInterp a
                           ihf_1 = nnfInterp b in
                       rewrite ihf_0 in
                       rewrite ihf_1 in refl
nnfInterp (FOr a b)  = let ihf_0 = nnfInterp a
                           ihf_1 = nnfInterp b in
                       rewrite ihf_0 in
                       rewrite ihf_1 in refl
