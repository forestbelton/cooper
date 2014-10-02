import Divides

divisor : Nat -> Nat -> Nat -> Type
divisor m n g = (divides g m, divides g n)

record GCD : (m, n, g : Nat) -> Type where
     IsGCD : (commonDivisor : divisor m n g)
           -> (greatestDivisor : (d : Nat) -> divisor m n d -> divides d g)
           -> GCD m n g

gcdRefl : GCD n n n
gcdRefl = IsGCD (selfDivides n, selfDivides n) gr
  where gr : (d : Nat) -> divisor n n d -> divides d n
        gr d (p, q) = p

gcdSym : GCD m n g -> GCD n m g
gcdSym (IsGCD (dM, dN) gr) = IsGCD (dN, dM) gr'
  where gr' : (d : Nat) -> divisor n m d -> divides d g
        gr' d (p, q) = gr d (q, p)

gcdOne : (n : Nat) -> GCD 1 n 1
gcdOne n = IsGCD (oneDivides 1, oneDivides n) gr
  where gr : (d : Nat) -> divisor 1 n d -> divides d 1
        gr d (p, q) = p
