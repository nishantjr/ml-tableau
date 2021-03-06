ml-tableau: Decision procedure for guarded matching logic
=========================================================

See [the matching logic website][ml] for more details on matching logic.

The `Main` module reads a _theory_ and a set of _statements_ from standard
input and prints out the parsed theory and statements. (Eventually it will
check and print satisfiability of each statement.)

Given a _signature_ Σ mapping _symbols_ to _arities,_ a _theory_ is a set
of _axioms_ constraining the _models_ (assignments of _interpretations_ to
symbols) for the theory. Signatures are currently `symbols` lines listing
pairs of symbols and their arities. Axioms are not yet supported.

Statements follow the theory and consist of a _check_ followed by a
_pattern._ Each statement will be checked in turn, once that's implemented.
The three checks are
- `sat` or satisfiable: we can show a model for this theory where this
  pattern evaluates to a non-empty set, i.e. we can find a consistent
  interpretation for all the symbols and _valuation_ (set of values or
  _elements_ for the variables).
- `unsat` or unsatisfiable: the negation of `sat`.
- `valid` is the dual of `sat`: any interpretation for symbols and all
  valuations of variables causes the pattern to evaluate to a non-empty
  set.

See the inputs and expected outputs under `ftest/` for examples.


Building and Testing
--------------------

Run the top-level `Test` script. Any arguments given will be passed on to
HTF (the Haskell Test Framework) to be processed as its [command line
options][htf cmd], e.g., `./Test -q` for quieter output or `./Test ':[pr]`
(a case-insensitive POSIX regular expression) to run tests from any test
module but only where the test name itself starts with `p` or `r`.

HTF stores a history of its test runs under `.HTF/`.


Development Setup
-----------------

This is written in Haskell and uses [Stack] as the build system. This can
be installed for a user without root access using the [manual install
instructions][st manual] (this includes a list of packages needed from your
Linux distribution), or installed in `/usr/local/` (sudo access required)
with:

    curl -sSL https://get.haskellstack.org/ | sh
    stack upgrade

Normally one will run the `Test` script (see above), but in case you need
them, the usual Stack commands for development are:

    stack build             # or: build --test
    stack run



<!-------------------------------------------------------------------->
[htf cmd]: https://hackage.haskell.org/package/HTF-0.14.0.3/docs/Test-Framework-CmdlineOptions.html
[st manual]: https://docs.haskellstack.org/en/stable/install_and_upgrade/#linux
[stack]: https://docs.haskellstack.org/en/stable/README/
[ml]: http://www.matching-logic.org/
