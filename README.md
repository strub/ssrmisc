## Misc. modules for the SSReflect Coq extension

Currently, the archive contains:

 - *fset.v*: a finite set library with a carrier T : choiceType. This overcomes
   the limitation of finset.v where the carrier must be a finType. The construction
   is not efficient (but is effective) as it uses a quotient, using the equality
   up to permutation, over uniq list.
