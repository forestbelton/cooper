cooper
======

An implementation of a Presburger arithmetic solver using Cooper's method.

Progress
--------

| Step | Implemented | Proven |
| ---- | ----------- | ------ |
| Convert to negation normal form                              | ✓ | ✘ |
| Remove redundant predicates                                  | ✓ | ✘ |
| Move quantified variable to one side of literal              | ✘ | ✘ |
| Remove coefficients from quantified variable                 | ✘ | ✘ |
| Construct left infinite projection and remove quantification | ✓ | ✘ |

Each step will have specialized ADTs for convenience.

