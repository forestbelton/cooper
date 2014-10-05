module Step1.Algo

import Data.ZZ

import Step1.Form
import Step1.Pred

import Step2.Form

%default total

mutual
  nnf : Step1.Form.Form a -> Step2.Form.Form a
  nnf FTrue      = FTrue
  nnf FFalse     = FFalse
  nnf (Single p) = Single p
  nnf (FNot a)   = nnf' a
  nnf (FAnd a b) = FAnd (nnf a) (nnf b)
  nnf (FOr a b)  = FOr (nnf a) (nnf b)
  
  nnf' : Step1.Form.Form a -> Step2.Form.Form a
  nnf' FTrue      = FFalse
  nnf' FFalse     = FTrue
  nnf' (Single p) = NotSingle p
  nnf' (FNot a)   = nnf a
  nnf' (FAnd a b) = FOr (nnf' a) (nnf' b)
  nnf' (FOr a b)  = FAnd (nnf' a) (nnf' b)

nnfInterp : (f : Step1.Form.Form (Pred n)) -> (xs : Vect n ZZ) -> Step1.Form.interp (interpPred xs) f = Step2.Form.interp (interpPred xs) (nnf f)
nnfInterp FTrue      _  = refl
nnfInterp FFalse     _  = refl
nnfInterp (Single _) _  = refl
nnfInterp (FNot a)   _  = ?nnfInterpNot
nnfInterp (FAnd a b) xs = let ihf_0 = nnfInterp a xs
                              ihf_1 = nnfInterp b xs in
                          rewrite ihf_0 in
                          rewrite ihf_1 in refl
nnfInterp (FOr a b)  xs = let ihf_0 = nnfInterp a xs
                              ihf_1 = nnfInterp b xs in
                          rewrite ihf_0 in
                          rewrite ihf_1 in refl
