# The Guarded Fragment {#sec:decidable-guarded-fragment}

* Define Assertions, Basic assertions, Sequents
* Show tableau, define parity game
* Informal overview of proofs.
    * Explain importance of (resolve)
    * Informal exlanation of the main lemma used.
* Example:
    *  $(\mu X \ldotp z \lor s(X)) \land \nu X \ldotp \lnot z \land \bar s(X)$
    *  this is an interesting example because it shows the need for alpha renaming in the implementation.
* Extension to theories.
* Examples of patterns inside and outside this fragment
    * Inside: LTL, PDL, Sorts and Subsorts
    * Outside: Guarded Separation Logic, ...
* What happens when we're outside the guarded fragment?
  Refutations are still correct, though models produced may not make sense.

Remark

:   For a nonempty tuple $\bar x$,
    We treat $\exists \bar x  \ldotp \phi$ and $\forall \bar x  \ldotp \phi$
    as shorthand for nested quantifier patterns.

Definition (Guarded pattern)

:   A guarded pattern is a closed pattern (i.e. without any free element or set variables)
    such that:

    1. Every existential   sub-pattern is of the form $\exists \bar x. \alpha \land     \phi$
       and every universal sub-pattern is of the form $\forall \bar x. \alpha \limplies \phi$
       where:

       a)   $\alpha$ is a conjunction where each conjunct is either an element variable,
            or an application pattern where each argument is an element variable,
       b)   every variable $x \in \bar x$ appears in some conjunct,
       c)   for each pair of variables $x \in \bar x$ and $y \in \free{\phi}$
            there is some application $\sigma_i(\bar {z_i})$ in $\alpha$ where $x, y \in \bar {z_i}$.
            \label{gp:xxx}

       We call $\alpha$ a guard.

    2.  If $\sigma(\phi_i)$ is an application, then
        each $\phi_i$ is a conjunction of the form $\xi \land \lAnd_{y \in \bar y} y$
        where $\bar y$ is a (possibly empty) set of element variables and $\xi$ is a pattern,
        and every element variable in $\free{\sigma(\phi_i)}$
        is in $\bar y$ for some $\phi_i$.

    3.  \label{item:fixedpoint-no-elements}
        Each fixedpoint sub-pattern $\mu X \ldotp \phi$ and $\nu X \ldotp \phi$ has no free element variables.

Example

: The pattern $\exists x. c$ is a guarded pattern where $c$ is a nullary symbol.
  Here the guard is the empty conjunction. Since $c$ has no free variables, Condition (\ref{gp:xxx})
  becomes true trivially.

TODO: Give examples that violate each of these conditions.

# Tableau, Games & Strategies

Now, we shall begin defining the sequents over which our tableau operates.

Definition (Assertion)

:   An *assertion* is either:

    1.  a pair of an element variable and a pattern, denoted $\matches{x}{\phi}$,
    2.  a conjunction of assertions: $\alpha_1 \land a_2$
    2.  a disjunction of assertions: $\alpha_1 \lor \alpha_2$

Informally, assertions allow us to capture that a element in the model matches a pattern.

From here on, we treat $\matches{x}{\phi_1\lor\phi_2}$ as equivalent to 
$\matches{x}{\phi_1} \lor \matches{x}{\phi_2}$.
and $\matches{x}{\phi_1\land\phi_2}$ as equivalent to 
$\matches{x}{\phi_1} \land \matches{x}{\phi_2}$.

Definition (Basic assertions)
:   *Basic assertions* are assertions of the form:

    1.  $\matches{x_0}{\sigma(x_1, \ldots, x_n)}$,
    2.  $\matches{x_0}{\bar\sigma(\lnot x_1, \ldots, \lnot x_n)}$.

    where each $x_i$ is an element variable.

*Basic* assertions, capture the relational interpretation of each symbol
and directly specify (portions) of the model.

Definition (Restriction)

:   The *free variables* of an assertion $\matches{x}{\phi}$ are $\{x\} \union \free\phi$.
    For conjunctions and disjunctions of assertion, it is the union of the free variables
    in each sub-pattern.
    For a set of assertions $A$ and a set of element variables $E$,
    the restriction of $A$ to $E$, denoted $A|_{E}$,
    is the subset of assertion in $A$ whose free variables are a subset of $E$.

Definition (Sequent)
:   A *sequent* is:

    1. a tuple, $\sequent{\Gamma; \Basic; \Universals}$,
       where $\Gamma$       is a set of assertions,
             $\Basic$       is a set of basic assertions,
             $\Universals$  is a set of assertions whose pattern is of the form $\bar\sigma(...)$ or $\forall \bar x\ldotp ...$.
    2. $\alpha \leadsto \sequent{\Gamma; \Basic; \Universals}$ where $\alpha$ is an assertion
       and $\Gamma, \Basic, \Universals$ are as above.
    3. $\unsat$

    For a sequent $v$ of the first two forms, we use $\Gamma(v), \Basic(v)$ and $\Universals(v)$
    to denote the corresponding component of the sequent.

Informally,
$\Gamma$ represents the set of assertions whose combined satisfiability we are checking.
$\Basic$ and $\Universals$ represent assertions we have deemed must hold.
Each free element variable in these assertions corresponds (roughly) to a distinct element in the
model we are building (if one exists). We will go into more details about this later.

Definition (Tableau)

:   For a signature $\Sigma$, and a guarded  pattern $\phi$,
    fix an arbitary dependency order,
    and let $K$ be an (arbitary) finite set of fresh element variables.
    A *tableau* is a (possibly infinte) tree
    with nodes labeled by sequents
    and built using the application of the rules below.
    The label of the root node is $\sequent{\matches{x}{\phi}, \emptyset, \emptyset, \{x\}}$
    where $x \in K$.
    Leaf nodes must be labeled either with $\unsat$
    or with a sequent where $\Gamma = \emptyset$.
    -- i.e. it is not a valid tableau when some leaf node does not meet this condition.


\newcommand{\makealign}{ \phantom{\name{choose-existential}}
                       & \phantom{\hskip 40ex}
                         \\ \vspace{-1em}}
\begin{figure*}
\begin{align*}
\makealign
\name{conflict}                 & \pruleun{\sequent{\{ \alpha \} \union \Gamma; \{ \fnot{\alpha} \} \union \Basic; \Universals}}
                                          { \unsat }
&\qquad
                                  \pruleun{\sequent{\{ \alpha \} \union \Gamma; \{ \alpha \} \union \Basic; \Universals}}
                                    {\sequent{        \Gamma; \Basic; \Universals}} &
\quad\name{ok} \\
                                & \quad\text{ when $\alpha$ is a basic assertion.}
                                & \quad\text{ when $\alpha$ is a basic assertion.}
\\
\name{conflict-el}              & \pruleun{\sequent{\matches{x}{y}, \Gamma; \Basic; \Universals}}
                                          { \unsat }
                            \quad \text{when $x \neq y$.}
                            &
 \pruleun{\sequent{\matches{x}{x}, \Gamma; \Basic; \Universals}}
                                          {\sequent{                \Gamma; \Basic; \Universals}}
&\quad\name{ok-el}
\end{align*}
\begin{align*}
\makealign
\name{and} &
                                  \unsatruleun{\sequent{ \matches{z}{\phi} \land \matches{w}{\psi},   \Gamma; \Basic; \Universals}}
                                              {\sequent{ \matches{z}{\phi}, \matches{w}{\psi},  \Gamma; \Basic; \Universals}}
\\
\name{or} &
                                  \satrulebin{\sequent{ \matches{z}{\phi} \lor \matches{w}{\psi}, \Gamma; \Basic; \Universals}}
                                             {\sequent{ \matches{z}{\phi}, \Gamma; \Basic; \Universals}}
                                             {\sequent{ \matches{w}{\psi}, \Gamma; \Basic; \Universals}}
\\
\name{def}                      & \pruleun{\sequent{ \matches{z}{\kappa X . \phi(X)}, \Gamma; \Basic; \Universals}}
                                  {\sequent{ \matches{z}{D}, \Gamma; \Basic; \Universals}} \\
                                & \text{when $D := \kappa X. \phi(X) \in \deflist$ }
\end{align*}
\begin{align*}
\makealign
\name{mu}                    & \pruleun{\sequent{ \matches{z}{D}, \Gamma; \Basic; \Universals}}
                                          {\sequent{ \matches{z}{\phi[D/X]}, \Gamma; \Basic; \Universals}}
&\qquad
 \pruleun{\sequent{ \matches{z}{D}, \Gamma; \Basic; \Universals }}
                                          {\sequent{ \matches{z}{\phi[D/X]}, \Gamma; \Basic; \Universals}}
&\quad\name{nu}                    &\\
                                & \text{when $D := \nu X. \phi \in \deflist$ }
                                & \text{when $D := \mu X. \phi \in \deflist$ }
\end{align*}
\begin{align*}
\makealign
\name{\dapp} &
\unsatruleun{\sequent{ \{\matches{z}{\bar\sigma(\bar \phi)}\} \union \Gamma; \Basic; \Universals}}
            { \sequent{ \mathrm{inst} \union \Gamma;
                        \Basic;
                        \{\matches{z}{\bar\sigma(\bar \phi)}\} \union \Universals;
                      } }
\qquad \text{when $\matches{z}{\bar \sigma(\bar \phi)}$ is not a basic assertion.} \\
  & \text{where $\mathrm{inst} = \left\{ \matches{z}{\fnot{\sigma(\bar y)}} \lor \lOr_i \matches{y_i}{\phi_i}
                                    \mid \bar y \subset \Elements \right\}$} \\
\\
\name{forall}                   & \unsatruleun { \sequent{ \matches{z}{\forall \bar x \ldotp \phi}, \Gamma; \Basic; \Universals} }
                                               { \sequent{ \mathrm{inst} \union \Gamma
                                                         ; \Basic
                                                         ; \matches{z}{\forall \bar x \ldotp \phi}, \Universals
                                                         } } \\
                                & \text{where $\mathrm{inst} = \{ \matches{z}{ \phi[\bar y / \bar x]} \mid \bar y \subset \Elements \}$}
\end{align*}
\end{figure*}
\begin{figure*}
\begin{align*}
\intertext{The following rules may only apply when none of the above rules apply -- i.e. when all assertions in $\alpha$
are either existentials or applications}
\name{choose-existential} &
\unsatruleun {\sequent{ \Gamma; \Basic; \Universals }}
             {\{ \alpha \leadsto \sequent{ \Gamma;\Basic; \Universals } \mid \text{for each $\alpha \in \Gamma$}\}}
   \\ 
\name{app} &
  \satruleun { \matches{z}{\sigma(\bar \phi)} \leadsto \sequent{ \Gamma; \Basic; \Universals  } }
             { \{ \sequent{ \matches{z}{\sigma(\bar k)} \land \lAnd_i \matches{k_i}{\phi_i}, \Gamma' \union \Universals'; \Basic' ; \{ \}  } \} } \\
  & \text{for each $\bar k \subset \{z\} \union \free{\bar \phi} \union (K \setminus \Elements)$} \\
  & \text{where} \\
  & \text{\qquad $\Elements' = \bar k \union \{ z \} \union  \free{\bar \phi}$} \\
  & \text{\qquad $\Basic' = \Basic|_{\Elements'}$},
    \text{       $\Gamma' = \Gamma|_{\Elements'}$},
    \text{and    $\Universals' = \Universals|_{\Elements'}$} \\
\\
\name{exists} &
  \satruleun { \matches{z}{\exists \bar x \ldotp \phi} \leadsto \sequent{ \Gamma; \Basic; \Universals } }
             { \{ \sequent{ \alpha, \Gamma' \union \Universals'; \Basic' ;  \{ \} } \}
             } \\
  & \text{for each $\alpha \in \{ \matches{z}{\phi[\bar k/\bar x]} \mid \bar k \subset \{z\} \union \free{\bar \phi} \union (K \setminus \Elements) \}$} \\
  & \text{where} \\
  & \text{\qquad $\Elements'   = \free{\alpha}$} \\
  & \text{\qquad $\Basic' = \Basic|_{\Elements'}$},
    \text{       $\Gamma' = \Gamma|_{\Elements'}$},
    \text{and    $\Universals' = \Universals|_{\Elements'}$} \\
\\
\cline{1-3}
\intertext{This rule may only apply (as many times as needed) immediately after the (exists)/(app) rules or on the root node.
$\mathsf{fresh}$ denotes the fresh variables introduced by the last application of those rules.}
\name{resolve} & \satrulebin{\sequent{ \Gamma; \Basic; \Universals}}
                            {\sequent{ \Gamma; \matches{x_0}{\sigma(x_1,\ldots,x_n)}      \union \Basic; \Universals}}
                            {\sequent{ \Gamma; \matches{x_0}{\lnot\sigma(x_1,\ldots,x_n)} \union \Basic; \Universals}} \\
               & \text{when neither $\matches{x}{{\sigma(x_1,\ldots,x_n)}}$ nor $\matches{x}{\fnot{\sigma(x_1,\ldots,x_n)}}$ are in $\Basic$} \\
               & \text{and  $\bar x \subset \Elements$ and $\bar x \intersection \mathsf{fresh} \neq \emptyset$.} \\
\\
\cline{1-3}
\end{align*}
\end{figure*}

Proposition
:   For any sequent built using these rules, we cannot have both $\matches{x}{\phi}$ and $\matches{x}{\fnot\phi}$ in $\Basic$

Proof
:   The root node starts with $\Basic$ empty, and therefore this invariant is maintained.
    Basic assertions are added to $\Basic$ only through the (resolve) rule which maintains the invariant.

Proposition
:   There is a tableau for any guarded pattern

Proof
:   For any assertion that is not basic, there is some rule that applies.
    For a basic assertion if either the assertion itself or its negation in in $\Basic$,
    then the (conflict) or (ok) rule applies.
    Otherwise, there was some application of the (exists),  (app) rule
    after which all variables in the assertion are in $\Elements$.
    We may build a tableau where the (resolve) rule
    is applied for this basic assertion after this (exists)/(app) rule. 

## Parity Game

Now that we have defined how a tableau is built,
we define how we may build a parity game from this.

From a tableau, $\mathcal T$, we now define a parity game $\mathcal G(\mathcal T)$.
In this game, player $0$ may be thought of as trying to prove the satisfiablity of the pattern,
and player $1$ as trying to prove it unsatisfiable.

Each position in the game is a pair $(a, v)$ where $a$ is an assertion
and $v$ is either a sequent or $\sat$.
If $v = \unsat$, then $a$ is of the form $\matches{x}{\bot}$.
If $\Gamma = \emptyset$, then $a$ is of the form $\matches{x}{\top}$.
Otherwise, $a \in \Gamma$.

There is an edge from a position $(a_0, v_0)$ to $(a_1, v_2)$ if:

a)  (child constructed by the (conflict) rule):

    $v_1 = \unsat$ is a child constructed through (conflict)
    and (conflict-el), $a_0 = a_1$. (same as above)

b)  (assertion matched by other tableau rule):

    1.  $v_1$ is constructed from $v_0$
        using the (and), (or), (def), (mu), (nu), (\dapp) or (forall) rules
        and $a_0$ was modified by this rule,
        and $a_1$ is one of the newly created assertions.
    2.  $v_0$'s child is created using (ok) or (ok-el)
        and $a_0 = a_1$ and $v_1 = \sat$.
    3.  $v_1$ is constructed from $v_0$
        using (choose-existential)
        and $a_0 = a_1 = \alpha$ is the matched existential.
    4.  $v_1$ is constructed from $v_0$
        using (app) or (exists)
        and $a_0 = \alpha$ and $a_1$ is the an instantiation from $\inst$.

c)  (unmatched by a tableau rule):

    $v_1$ is a child constructed through any rule besides (conflict)
    and (conflict-el),
    $a_0 = a_1$ is in $\Gamma(v_0) \union \Universals(v_0)$
    and $\Gamma(v_1) \union \Universals(v_1)$.
    and $v_1 = v_0$

\newcommand{\green}[1]{{\color{green}#1}}
\newcommand{\blue}[1]{{\color{blue}#1}}
A position $p = (a, v)$ is in $\Pos_0$ by rules with a \green{green} rule. That is, if:

  1.  $v$'s children were built using (or), (app), or (exists) rules
      and $a$ was the assertion matched on by that rule; or
  2.  $v$'s children were built using (resolve); or
  3.  $v = \unsat$

A position $p = (a, v)$ is in $\Pos_1$ by rules with a \blue{blue} rule. That is if:

  1. $v$'s children were built using (and), (\dapp), (forall), or (choose-existential) rules
     and $a$ was the assertion matched on by that rule;
  2. $v = \sat$

All other positions do not offer a choice, and so are arbitrarily assigned to $\Pos_1$.

The parity condition $\Omega$ is defined as follows:

* $\Omega((e \in D_X, v))                       = 2 \times i$     if $D_i$ is a $\mu$-marker that is $i$th in the dependency order.
* $\Omega((e \in D_X, v))                       = 2 \times i + 1$ if $D_i$ is a $\nu$-marker that is $i$th in the dependency order.
* $\Omega((e \in \exists \bar x\ldotp \phi, v)) = 2 \times N + 1$ where $N$ is the number of fixedpoint markers in $\deflist$.
* $\Omega(a, v)                                 = 2 \times N + 2$ otherwise.

Definition (Pre-models & Refutations)

:   For a $\mathcal G(\mathcal T) = (\Pos_0, \Pos_1, E, \Omega)$,
    a winning strategy from a position $q$ for a player $i$ is a subtree $(P \subset \Pos, S \subset E)$ such that:

    1. $q \in P$
    1. If a node $p \in P \intersection \Pos_i$
       then there is exactly one edge outward edge $(p, p')$ in $S$ and $p' \in P$.
    2. If a node $p \not\in \Pos_i$ and $p \in P$ then all outward edges from $p$ in $E$ are in $S_i$ and $p \in W_i$.
    3. Player $i$ wins on every trace.

    We call a winning strategy for player $0$ a pre-model,
    and a winning strategy for player $1$ a refutation.

In the next section we prove some important theorems:

Theorem

:   If a guarded pattern has a tableau with a pre-model, then it is satisfiable.

Theorem

:   \label{theorem:validity}
    If a guarded pattern has a tableau with a refutation, then it is unsatisfiable
    and its negation is valid.

\hl{Note: The following sections may go in the appendix.}

#   Implementation (1/2 - 1 page)

-   To the best of our knowledge, we've not seen an implementation of provers for guarded fp logic
-   Constructs a single tableau/game, and then dispatches it to pre-existing parity game solver -- PGSolver
-   PGSolver returns either a pre-model or a refutation (which we could use to construct a model or a proof of unsatisfiablity)
-   Test cases
    -   LTL Axioms
    -   Few other tests we're using as unit tests

# Future Work (1 page)

- Implementation
    - 
- Integration with SMT solvers for dealing with domain specific reasoning -- integers, bitvectors, arrays...
- Extension of the decidable fragment 
    - guards allow existentials a la packed logic
    - the proof only relies on the restriction to universal quantifiers.
- Optimizations -- things like constructors/functions/commutative symbols
- Building the parity game solver into the engine itself.
  Currently we must build a complete game before sending it to the solver.
  * Integration with the game solver would allow us to return once we have found a winning strategy
    even if the game is not complete.
  * It would also enable incremental solving.
