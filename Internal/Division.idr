module Division
%default total

public
data Division : Nat -> Nat -> Type where
    mkDivision : (q, r : Nat)
    -> a = b * q + r
    -> LT r b
    -> Division a b

data DivisionStep : Nat -> Nat -> Nat -> Type where
    mkDivisionStep : (q : Nat)
    -> a = b * q + r
    -> DivisionStep a b r

eitherLTorGTE : (m, n : Nat) -> Either (LT m n) (GTE m n)
eitherLTorGTE m Z         = Right LTEZero
eitherLTorGTE Z (S l)     = Left (LTESucc LTEZero)
eitherLTorGTE (S k) (S l) = case eitherLTorGTE k l of
    Left prf1  => Left (LTESucc prf1)
    Right prf2 => Right (LTESucc prf2)

divideBase : (a, b : Nat) -> a = (S b) * 0 + a
divideBase a b =
    rewrite multZeroRightZero b in
        sym (plusZeroLeftNeutral a)

plusSuccRightBoth : (a, b, c : Nat) -> a + b = c -> a + S b = S c
plusSuccRightBoth a b c prf =
    rewrite sym (plusSuccRightSucc a b) in
        cong {f = S} prf

subtract : (m, n : Nat) -> LTE n m -> (p : Nat ** p + n = m)
subtract Z Z prf = (0 ** Refl)
subtract (S k) Z prf = (S k ** plusZeroRightNeutral (S k))
subtract (S k) (S l) (LTESucc prf) with (subtract k l prf)
    | (p1 ** prf1) = (p1 ** plusSuccRightBoth p1 l k prf1)

divideStep : (a, b, r : Nat)
    -> DivisionStep a b r
    -> LTE b r
    -> (r1 : Nat ** DivisionStep a b r1)
divideStep a b r (mkDivisionStep q prf) ltePrf =
    let (r1 ** prf1) = subtract r b ltePrf
        in (r1 ** mkDivisionStep (S q) ?adjustDivideProof)

-- TODO: Eliminate the call to assert_smaller
divideHelp : (a, b, r : Nat) -> DivisionStep a (S b) r -> Division a (S b)
divideHelp a b r (mkDivisionStep q prf) = case eitherLTorGTE r (S b) of
    Left prf1  => mkDivision q r prf prf1
    Right prf2 => let (r1 ** step) = divideStep a (S b) r (mkDivisionStep q prf) prf2 in
        divideHelp a b (assert_smaller r r1) step

public
divide : (a, b : Nat) -> Not (0 = b) -> Division a b
divide a Z contra     = void (contra Refl)
divide a (S k) contra = divideHelp a k a (mkDivisionStep 0 (divideBase a k))

---------- Proofs ----------

Division.adjustDivideProof = proof
  intros
  rewrite multCommutative (S q) b
  rewrite plusCommutative (mult q b) b
  rewrite plusAssociative (mult q b) b r1
  rewrite plusCommutative r1 b
  rewrite sym prf1
  rewrite multCommutative b q
  exact prf
