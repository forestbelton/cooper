module Step2.Algo

import Data.ZZ

import Step1.Pred
import Step2.Form
import Step3.Form
import Step3.Pred

%default total

andForm : a -> a -> Step3.Form.Form a
andForm a b = FAnd (Single a) (Single b)

orForm : a -> a -> Step3.Form.Form a
orForm a b = FOr (Single a) (Single b)

dedup : Step2.Form.Form (Step1.Pred.Pred n) -> Step3.Form.Form (Step3.Pred.Pred n)
dedup FTrue                         = FTrue
dedup FFalse                        = FFalse
dedup (Single (PredEQ a b))         = andForm (PredLT a (inc b)) (PredLT b (inc a))
dedup (NotSingle (PredEQ a b))      = orForm (PredLT a b) (PredLT b a)
dedup (Single (PredLT a b))         = Single (PredLT a b)
dedup (NotSingle (PredLT a b))      = Single (PredLT b (inc a))
dedup (Single (PredDivides k a))    = Single (PredDivides k a)
dedup (NotSingle (PredDivides k a)) = Single (PredNotDivides k a)
dedup (FAnd a b)                    = FAnd (dedup a) (dedup b)
dedup (FOr a b)                     = FOr (dedup a) (dedup b)

dedupInterp : (f : Step2.Form.Form (Step1.Pred.Pred n)) -> (xs : Vect n ZZ) -> Step2.Form.interp (interpPred xs) f = Step3.Form.interp (interpPred xs) (dedup f)
dedupInterp FTrue         _  = refl
dedupInterp FFalse        _  = refl
dedupInterp (Single p)    xs = ?dedupInterpSingle
dedupInterp (NotSingle p) xs = ?dedupInterpNotSingle
dedupInterp (FAnd a b)    xs = let ihf_0 = dedupInterp a xs
                                   ihf_1 = dedupInterp b xs in
                               rewrite ihf_0 in
                               rewrite ihf_1 in refl
dedupInterp (FOr a b)     xs = let ihf_0 = dedupInterp a xs
                                   ihf_1 = dedupInterp b xs in
                               rewrite ihf_0 in
                               rewrite ihf_1 in refl
