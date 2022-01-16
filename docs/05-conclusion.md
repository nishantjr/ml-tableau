# Examples

Due to space constraints, we show examples of theories captured by the above fragments, as well as example tableaux in the
Appendix \ref{@app:examples}.

# Future Work

As mentioned in Section \ref{sec:introduction},
our goal and primary motivation
is to use the algorithm defined for guarded patterns as the basis of an automated prover.
Towards that goal, there are two important milestones we need to reach.

First, we must implement our algorithm.
This may prove tricky because we have not found any previous implementations
for the corresponding procedure of guarded fixedpoint logic.
Indeed, it was difficulties implementing the procedure in \cite{guarded-fixedpoint-logic}
that led us to develop the \prule{resolve} rule.
Without it, we had needed to search through all possible combinations of consistent basic assertions.
Our plan is to produce a parity game, and then use a pre-existing solver for parity games&nbsp;\cite{friedmann2009-pgsolver}
to search for pre-models or refutations.
\todo{should we remove this completely?}

Second, we must be able to combine this procedure with our decision procedures
and semi-algorithms. This will allow us to take advantage of this decision
procedure even when the pattern we are dealing with lies outside the fragment.
In the world of first-order SMT solvers, this is typically done using the
Nelson-Oppen combination procedure \cite{nelsonoppen1979-cooperating-decision-procedures,@krstic2007-architecting}.
One approach may be to extend the \prule{conflict-*} and \prule{ok-*} rules
to treat the SMT solver as an oracle for checking the consistency of basic assertions.
This approach will likely work when the algorithm decides that the pattern is unsatisfiable.
However, if the algorithm instead produces a model,
we aren't guaranteed that the pattern is satisfied by that model.
This is because the proof of Theorem \ref{theorem:xxx} depends on the properties of guarded patterns,
whereas that of Theorem \ref{theorem:yyy} does not.
In particular, the model produced may have inconsistencies between assertions
over elements that do not share nodes in the tableau.
In the case where we are able to identify the elements that produce the conflict,
we may be able to synthesize guarded lemmas that allow us to rule out these models.
\todo{relatively complete wrt oracle}
\todo{mention integration with K}
newline

Another important direction is to extend our decidable fragment as much as possible.
\todo{take away: decidability comes from the restriction to quantification}
One easy candidate to to drop the requirement that fixedpoints may not have free
element variables. This will involve extending fixedpoint markers to take arguments,
and changes to the \prule{def}, \prule{mu}, and \prule{nu} rules to work with these extended fixedpoint markers.

A second low hanging fruit stems from the observation that 
the proof of Theorem \ref{theorem:xxx} depends on the properties of guarded patterns,
whereas that of Theorem \ref{theorem:yyy} does not.
This implies that we can likely drop the restriction to existentials patterns
when checking satisfiablilty, and the restriction to universal patterns when checking validity.
Further, axioms in theories are not negated when reducing validity to satisfiability,
so the restriction do existentials can be dropped for axioms when checking
both the validity and satisfiability modulo theories.

A third avenue draw inspiration from other decideable logics. For example, the
decidability of the packed fragment of first-order logic \cite{marx2001-tolerance-logic} seems
to imply that we can allow nested existentials or applications in guards. That
of guarded separation logic \cite{guarded-separation-logic} implies that we could
handle associative-commutive symbols, perhaps by drawing inspiration from
unification algorithms. The relationship between the finite variant property and
the guarded fragment is another exciting direction.
\newline

As we draw inspiration from these decision procedures we increase the complexity
of our decision procedure, and that complexity increases the risk of incorrectness.
To mitigate this risk we aim to produce proofs of validity from refutations.
These proofs can then be checked with a small trust-base, for example by the proof checker
developed in&nbsp;\cite{chen-lin-trinh-rosu-2021-cav}.

For the most part the tableau rules in Figure \ref{fig:guarded-tableau}
(when viewed through the lens of a refutation) correspond directly
to matching logic proof rules.
The \prule{exists} may be thought of as a combination of the \prule{$\exists$-generalization}
followed by case analysis between the introduced variables.
One tricky aspect when converting the refutations to proofs is dealing with infinite plays.
By definition of a refutation, these contain a $\mu$-marker that is unfolded infinitely often.
We must somehow turn this into a finite proof.
Fortunately these plays must be $\omega$-regular, and we should be able to
represent them in a finite proof
through the combination of *implication contexts* introduced in \cite{towards-a-unified-framework},
and the \prule{knaster-tarski} proof rule.
\todo{no need to mention knaster-tarksi rule}
\todo{talk about the the proof checker}
\todo{... so that we don't need to trust the prover.}

# Conclusion

We presented three decision procedures for fragments of matching logic.
The guarded fragment is a powerful fragment supporting both fixedpoints
and some quantification and allows us to capture many theories important to program verification.
We outlined next steps to be taken in order to use this procedure as the core of an automated prover.
\clearpage

# To do

* Examples:
    *  $(\mu X \ldotp z \lor s(X)) \land \nu X \ldotp \lnot z \land \bar s(X)$
    *  this is an interesting example because it shows the need for alpha renaming in the implementation.
* Extension to theories.
* Examples of patterns inside and outside this fragment
    * Inside: LTL, PDL, Sorts and Subsorts
    * Outside: Guarded Separation Logic, ...
* What happens when we're outside the guarded fragment?
  Refutations are still correct, though models produced may not make sense.

