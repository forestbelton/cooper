module Divides

divides : Nat -> Nat -> Type
divides d n = (k : Nat ** n = d * k)

oneDivides : (n : Nat) -> divides 1 n
oneDivides n = ?oneDividesProof

selfDivides : (n : Nat) -> divides n n
selfDivides n = ?selfDividesProof

scaleDividesLemma : {n, d, k, c : Nat} -> n = d * k -> n * c = d * (k * c)
scaleDividesLemma p = ?scaleDividesLemmaProof

scaleDivides : {d, n, c : Nat} -> divides d n -> divides d (n * c)
scaleDivides (l ** p) = ?scaleDividesProof

transDividesLemma : {a,b,c,k,l : Nat} -> b = a * k -> c = b * l -> c = a * (k * l)
transDividesLemma p q = ?transDividesLemmaProof

transDivides : divides a b -> divides b c -> divides a c
transDivides (k ** p) (l ** q) = ?transDividesProof

---------- Proofs ----------

Divides.transDividesProof = proof
  intros
  exact (k * l ** transDividesLemma p q)


Divides.transDividesLemmaProof = proof
  intros
  rewrite sym (multAssociative a k l)
  rewrite p
  rewrite q
  trivial


Divides.scaleDividesLemmaProof = proof
  intros
  rewrite sym (multAssociative d k c)
  rewrite sym p
  trivial


Divides.scaleDividesProof = proof
  intros
  exact (l * c ** scaleDividesLemma p)


Divides.oneDividesProof = proof
  intros
  let p = plusZeroRightNeutral n
  exact (n ** sym p)


Divides.selfDividesProof = proof
  intros
  let p = multOneRightNeutral n
  exact (1 ** sym p)


