cooper
======

An implementation of a Presburger arithmetic solver using Cooper's method.
The current plan of attack:

  * Embed classical logic in Idris with double-negation translation
  * Prove embedding is valid with Glivenko's theorem
  * Convert classical formula to negation normal form (Step 1)
  * Prove that each step in Cooper's method produces T_Z-equivalent formulas

For each step I will construct a specialized ADT. This is a little more
verbose, but it means I don't have to prove formula normalization after each
step.
