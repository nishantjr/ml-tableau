* Examples:
    *  $(\mu X \ldotp z \lor s(X)) \land \nu X \ldotp \lnot z \land \bar s(X)$
    *  this is an interesting example because it shows the need for alpha renaming in the implementation.
* Extension to theories.
* Examples of patterns inside and outside this fragment
    * Inside: LTL, PDL, Sorts and Subsorts
    * Outside: Guarded Separation Logic, ...
* What happens when we're outside the guarded fragment?
  Refutations are still correct, though models produced may not make sense.

# Next Steps

## Implementation

- Building the parity game solver into the engine itself.

## Extensions of the decidable fragment

- guards allow existentials a la packed logic
- the proof only relies on the restriction to universal quantifiers.
- handle constructors, functions, ACU...

## Combination with other solvers

Integration with SMT solvers for dealing with domain specific reasoning -- integers, bitvectors, arrays...

## Extraction of Proof objects

