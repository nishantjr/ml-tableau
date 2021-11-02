ml-tableau: Decision procedure for guarded matching logic
=========================================================


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
