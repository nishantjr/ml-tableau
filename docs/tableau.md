# Guarded Matching Logic

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
       a)   $\alpha = \lAnd_i \sigma_i(\bar {z_i})$ is a conjunction of application patterns where each argument is an element variable,
       b)   for each pair of variables $x \in \bar x$
            and $y \in \free{\phi} \setminus \bar x$
            there is some application $\sigma_i(\bar {z_i})$ in $\alpha$ where $x, y \in \bar {z_i}$.
            \label{gp:xxx}

       We call $\alpha$ a guard.
    2. Each application sub-pattern is either quantifier-free (i.e. has no universal or existential quantifiers as sub-patterns),
       or
       has arguments of the form $x \land \phi$
       where $x$ is an element variable.  
       Note that the pattern $x$ is equivalent to $x \land \top$
       and we consider that as matching this criteria.
    3. Each fixedpoint sub-pattern $\mu X \ldotp \phi$ and $\nu X \ldotp \phi$ has no free element variables.

Example

: The pattern $\exists x. c$ is a guarded pattern where $c$ is a nullary symbol.
  Here the guard is the empty conjunction. Since $c$ has no free variables, Condition (\ref{gp:xxx})
  becomes true trivially.


# Tableau, Games & Strategies

We define our procedure over "positive-form" patterns
-- patterns where negations are pushed down as far as they can go using De Morgan's and related equivalences.

Definition (Positive Form Pattern)
:   Positive form patterns are defined using the syntax:

    \begin{alignat*}{5}
    \phi := \quad&       \sigma(\phi_1, \ldots, \phi_n)
       &\quad\mid\quad&  \bar \sigma(\phi_1, \ldots, \phi_n) \\
        \quad\mid\quad&  \phi_1 \land \phi_2
       &\quad\mid\quad&  \phi_1 \lor  \phi_2 \\
        \quad\mid\quad&  x
       &\quad\mid\quad&  \lnot x
       &\quad\mid\quad&  \exists x \ldotp \phi
       &\quad\mid\quad&  \forall x \ldotp \phi \\
        \quad\mid\quad&  X &
                      &    &
        \quad\mid\quad&  \mu X \ldotp \phi
       &\quad\mid\quad&  \nu X \ldotp \phi
    \end{alignat*}
    where $\bar \sigma(\phi_1, \ldots, \phi_n) \equiv \lnot\sigma(\lnot \phi_1, \ldots, \lnot\phi_n)$.

Remark

: We allow negation of element variables, but not set variables.
  This ensures that set variables may only occur positively in their binding fixedpoint.

Definition (Definition List)

:   A definition list, $\deflist$, of a pattern $\phi$ is an ordered list assigning
    special constants, called fixedpoint constants, to fixed point patterns.
    We extend the syntax of patterns to allow fixedpoint constants.

    Given a pattern $\phi$, a definition list is constructed as follows:

    \begin{align*}
    \mkDeflist{D} &= \emptyset \qquad \text{where $D$ is a fixedpoint constant.} \\
    \mkDeflist{\sigma(\phi_1,\ldots,\phi_n)} = \mkDeflist{\bar\sigma(\phi_1,\ldots,\phi_n)} &= \mkDeflist{\phi_1}\combineDefList\cdots\combineDefList\mkDeflist{\phi_n} \\
    \mkDeflist{\phi_1\lor\phi_2}  = \mkDeflist{\phi_1\land\phi_2)} &= \mkDeflist{\phi_1}\combineDefList\mkDeflist{\phi_2} \\
    \mkDeflist{\exists \bar x \ldotp\phi}  = \mkDeflist{\forall \bar x \ldotp \phi)} &= \mkDeflist{\phi} \\
    \mkDeflist{\mu X \ldotp\phi}  &= (D \mapsto \mu X . \phi[U/X]) \combineDefList \mkDeflist{\phi} \text{ where $\phi$ has no free element variables.}\\
    \mkDeflist{\nu X \ldotp\phi}  &= (D \mapsto \nu X . \phi[U/X]) \combineDefList \mkDeflist{\phi} \text{ where $\phi$ has no free element variables.}\\
    \\
    \deflist_1 \combineDefList \cdot                           &= \deflist_1 \\
    (D_1 \mapsto \phi)   \deflist_1 \combineDefList (D_2 \mapsto \phi)   \deflist_2 &= (D_1 \mapsto \phi) \deflist_1 \combineDefList \deflist_2[D_1/D_2] \\
                         \deflist_1 \combineDefList (D_2 \mapsto \phi)   \deflist_2 &= \deflist_1 (D_2 \mapsto \phi) \combineDefList \deflist_2 \qquad\text{otherwise.}\\
    \end{align*}

    For a definition list $\deflist$, the denotation of a fixedpoint constant is
    given by:
    $$\denotation{D} = \denotation{\deflist[D]}$$.

Definition (Assertion)

:   An *assertion* is either:

    1.  a pair of an element variable and a pattern, denoted $\matches{e}{\phi}$,
    2.  a conjunction of assertions: $\alpha_1 \land a_2$
    2.  a disjunction of assertions: $\alpha_1 \lor \alpha_2$

Assertions allow us to capture that a particular element variable matches a pattern.
Symantically, $\matches{e}{\phi}$ is equivalent to the pattern $\lceil{e \land \phi}\rceil$
where $\lceil \_ \rceil$ is the definedness symbol.

Definition (Atomic assertions)
:   *Atomic assertions* are assertions of the form:

    1.  $\matches{e}{\sigma(a_1, \ldots, a_n)}$,
    2.  $\matches{e}{\lnot\sigma(a_1, \ldots, a_n)} \equiv \matches{e}{\bar\sigma(\lnot a_1, \ldots, \lnot a_n)}$.

    where $e$ and each $a_i$ is an element variable.

Definition (Sequent)
:   A *sequent* is:

    1. a tuple, $\sequent{\Gamma; \Atoms; \Universals; \Elements}$,
       where $\Gamma$       is a set of assertions,
             $\Atoms$       is a set of atomic assertions,
             $\Universals$  is a set of assertions whose pattern is of the form $\bar\sigma(...)$ or $\forall \bar x\ldotp ...$,
         and $\Elements$    is a set of element variables.
    2. $\alpha \leadsto \sequent{\Gamma; \Atoms; \Universals; \Elements}$ where $\alpha$ is an assertion
       and $\Gamma, \Atoms, \Universals, \Elements$ are as above.
    3. $\unsat$

Informally,
$\Gamma$ represents the set of assertions whose combined satisfiability we are checking.
$\Atoms$ and $\Universals$ represent assertions we have deemed must hold for the
variables in $\Elements$.
We implicitly assume that all element in $\Elements$ have distinct interpretations.

Definition (Tableau)

:   For a signature $\Sigma$, and a guarded  pattern $\phi$,
    let $\deflist$ be its definition list,
    and $K$ be a set of distinct element variables.
    A *tableau* is a (possibly infinte) tree
    with nodes labeled by sequents
    and built using the application of the rules below.
    The label of the root node is $\sequent{\matches{e}{\phi}, \{\}, \{\}, \{e\}}$ for some fresh variable $e$ drawn from $K$.
    Leaf nodes must be labeled either 
       with $\unsat$
    or with a sequent where $\Gamma = \emptyset$.

\allowdisplaybreaks
\begin{align*}
\cline{1-3}
\name{conflict}                 & \pruleun{\sequent{\alpha, \Gamma; \Atoms; ...}}
                                          { \unsat } \\
                                & \text{when $\alpha$ is an atomic assertion, with its negation  in $\Atoms$.}
\\
\name{ok}                       & \pruleun{\sequent{\alpha, \Gamma; \Atoms; ...}}
                                    {\sequent{        \Gamma; \Atoms; ...}} \\
                                & \text{when $\alpha$ is an atomic assertion in $\Atoms$.}
\\
\name{conflict-el}              & \pruleun{\sequent{\matches{e}{e'}, \Gamma; \Atoms; ...}}
                                          { \unsat } \\
                                & \text{when $e' \neq e$ is an element in $\Elements$.}
\\
\name{ok-el}                    & \pruleun{\sequent{\matches{e}{e}, \Gamma; \Atoms; ...}}
                                          {\sequent{        \Gamma; \Atoms; ...}} \\
                                & \text{when $\alpha$ is an atomic assertion in $\Atoms$.}
\\
\cline{1-3}
\name{and}                      & \unsatruleun{\sequent{ \matches{e}{\phi \land \psi},   \Gamma; ...}}
                                              {\sequent{ \matches{e}{\phi}, \matches{e}{\psi},  \Gamma; ...}}
\qquad
                                  \unsatruleun{\sequent{ \matches{e}{\phi} \land \matches{f}{\psi},   \Gamma; ...}}
                                              {\sequent{ \matches{e}{\phi}, \matches{f}{\psi},  \Gamma; ...}}
\\
\name{or}                       & \satrulebin{\sequent{  \matches{e}{\phi \lor \psi}, \Gamma; ... }}
                                              {\sequent{ \matches{e}{\phi}, \Gamma; ... }}
                                              {\sequent{ \matches{e}{\psi},  \Gamma; ... }}
\qquad
                                  \satrulebin{\sequent{  \matches{e}{\phi} \lor \matches{f}{\psi}, \Gamma; ... }}
                                              {\sequent{ \matches{e}{\phi}, \Gamma; ... }}
                                              {\sequent{ \matches{e}{\psi},  \Gamma; ... }}
\\
\name{def}                      & \pruleun{\sequent{ \matches{e}{\kappa X . \phi(X)}, \Gamma; ...}}
                                  {\sequent{ \matches{e}{D}, \Gamma; ...}} \\
                                & \text{when $D := \kappa X. \phi(X) \in \deflist$ }
\\
\name{mu}                    & \pruleun{\sequent{ \matches{e}{D}, \Gamma; ... }}
                                          {\sequent{ \matches{e}{\phi[D/X]}, \Gamma;... }} \\
                                & \text{when $D := \mu X. \phi \in \deflist$ }
\\
\name{nu}                    & \pruleun{\sequent{ \matches{e}{D}, \Gamma; ... }}
                                          {\sequent{ \matches{e}{\phi[D/X]}, \Gamma;... }} \\
                                & \text{when $D := \nu X. \phi \in \deflist$ }
\\
\name{dapp} &
\unsatruleun{\sequent{ \matches{e}{\bar\sigma(\bar \phi)}, \Gamma; \Universals; \Elements; ...}}
            { \sequent{ \mathrm{inst} \union \Gamma; 
               \matches{e}{\bar\sigma(\bar \phi)}, \Universals; \Elements; ... } } \\
  & \text{where $\mathrm{inst} = \left\{ \matches{e}{\sigma(\bar c)} \limplies \lOr_i \matches{c_i}{\phi_i}
                                    \mid \text{ if } \bar c \subset \Elements \right\}$} \\
  & \text{and $\matches{e}{\bar \sigma(\bar \phi)}$ is not an atomic assertion.}
\\
\name{forall}                   & \unsatruleun { \sequent{ \matches{e}{\forall \bar x \ldotp \phi(\bar x)}, \Gamma; \Universals; \Elements; ... } }
                                               { \sequent{ \mathrm{inst} \union \Gamma
                                                         ; \matches{e}{\forall \bar x \ldotp \phi}, \Universals
                                                         ; \Elements
                                                         ; ... } } \\
                                & \text{where $\mathrm{inst} = \{ e \in \phi[\bar c / \bar x] \mid c \subset \Elements \}$}
\\
\cline{1-3}
\intertext{The following rules may only apply when none of the above rules apply -- i.e. when all assertions in $\alpha$
are either existentials or applications}
\name{choose-existential} &
\unsatruleun {\sequent{ \Gamma; ... }}
             {\{ \alpha \leadsto \sequent{ \Gamma;\Atoms; \Universals; \Elements }\}}
    \qquad  \text{for each $\alpha \in \Gamma$}
   \\ 
\name{app} &
  \satruleun { \matches{e}{\sigma(\bar \phi)} \leadsto \sequent{ \Gamma; \Atoms; \Elements } }
             { \{ \sequent{ \matches{e}{\sigma(\bar k)} \land \lAnd_i \matches{k_i}{\phi_i}, \Gamma' \union \Universals'; \Atoms' ; \{ \} ; \Elements'  } \} } \\
  & \text{for each $\bar k \subset K$} \\
  & \text{where} \\
  & \text{\qquad $\Elements' = \bar k \union \{ e \} \union  \free{\bar \phi}$} \\
  & \text{\qquad $\Atoms' = \{ a \mid a \in \Atoms \text{ and } \free{a} \subset \Elements' \}$ \quad($\Atoms$ restricted to $\Elements'$)} \\
  & \text{\qquad $\Gamma' = \{ \gamma \mid \gamma \in \Gamma \text{ and } \free{\gamma} \subset \Elements' \}$ \quad($\Gamma$ restricted to $\Elements'$)} \\
  & \text{\qquad $\Universals' = \{ \alpha \mid \alpha \in \Universals \text{ and } \free{\gamma} \subset \Elements' \}$ \quad($\Universals$ restricted to $\Elements'$)} \\
\\
\name{exists} &
  \satruleun { \matches{e}{\exists \bar x \ldotp \phi(\bar x)} \leadsto \sequent{ \Gamma; \Atoms; \Universals; \Elements } }
             { \{ \sequent{ \alpha, \Gamma' \union \Universals'; \Atoms' ;  \{ \}; \Elements' } \}
             } \\
  & \text{for each $\alpha \in \{ \matches{e}{\phi[\bar k/\bar x]} \mid \bar k \subset K \}$} \\
  & \text{where} \\
  & \text{\qquad $\Elements'   = \free{\alpha}$} \\
  & \text{\qquad $\Atoms'      = \{ a \mid a \in \Atoms \text{ and } \free{a} \subset \Elements' \}$ \quad($\Atoms$ restricted to $\Elements'$)} \\
  & \text{\qquad $\Gamma'      = \{ \gamma \mid \gamma \in \Gamma \text{ and } \free{\gamma} \subset \Elements' \}$ \quad($\Gamma$ restricted to $\Elements'$)} \\
  & \text{\qquad $\Universals' = \{ \alpha \mid \alpha \in \Universals \text{ and } \free{\alpha} \subset \Elements' \}$ \quad($\Universals$ restricted to $\Elements'$)} \\
\\
\cline{1-3}
\intertext{This rule must apply only immediately after the (exists)/(app) rules or on the root node.
$\mathsf{fresh}$ denotes the fresh variables introduced by the last application of those rules.}
\name{resolve} & \satrulebin{\sequent{\Gamma; A; C}}
                            {\sequent{ \Gamma; \matches{e}{\sigma(\bar a)}, A; C}}
                            {\sequent{ \Gamma; \matches{e}{\lnot\sigma(\bar a)}, A; C}} \\
               & \text{when $\{e\}\union \bar a \subset C$ and $(\{e\}\union \bar a)\intersection \mathsf{fresh} \neq \emptyset$.}
\\
\cline{1-3}
\end{align*}

## Games & Strategies

Definition (Parity Game)

:   A parity game is a tuple $(\Pos_0, \Pos_1, E, \Omega)$
    where $\Pos = \Pos_0 \union \Pos_1$ is a possibly infinite set of positions;
    $E : \Pos \times \Pos$ is a transition relation;
    and $\Omega : \Pos \to \N$ defines the *parity winning condition*.

    The game is played between two players, player $0$ and player $1$.
    When the game is in a position $p \in \Pos_i$ then it is player $i$'s turn -- i.e. player $i$ may choose
    the next vertex to transition form the current node, along the transition
    relation $E$.
    Each "game" results in a (possible infinite) sequence of positions, called plays: $p_0, p_1, p_2,...$.
    A play is finite iff one player is unable to make a move. In that case that player loses.
    For an infinite play, we look at the sequence of parities of the vertices in the play
    -- i.e. $\Omega(p_0), \Omega(p_1), \ldots$.
    Player $0$ wins iff the least parity that occurs infinitely often is even, otherwise player $1$ wins.

    ---

From a tableau, $\mathcal T$, we may define a parity game $\mathcal G(\mathcal T)$, as follows.
Each position in the game is a pair $(a, v)$ where $a$ is an assertion
in the label of a vertex $v$ of $\mathcal T$.

There is an edge from $(a_0, v_0)$ to $(a_1, v_1)$ in $E$ iff either:

* $v_1$ is a child of $v_0$ constructed by some rule that matches on the assertion $a_0$
  and $a_1$ is the newly created assertion.
* $v_1$ is a child of $v_0$ constructed by some rule that does not match on the assertion $a_0$
  and $a_0 = a_1$.


\newcommand{\green}[1]{{\color{green}#1}}
\newcommand{\blue}[1]{{\color{blue}#1}}
A position $p = (a, v)$ is in $\Pos_0$ by rules with a \green{green} rule. That is, if:

  1.  $v$'s children were built using (or), (app), or (exists) rules
      and $a$ was the assertion matched on by that rule; or
  2.  $v$'s children were built using (resolve); or
  3.  $v = \unsat$

A position $p = (a, v)$ is in $\Pos_1$ by rules with a \blue{blue} rule. That is if:

  1. $v$'s children were built using (and), (dapp), (forall), or (choose-existential) rules
     and $a$ was the assertion matched on by that rule;
  2. $v$ has $\Gamma = \emptyset$.

All other positions do not offer a choice, and so are arbitrarily assigned to $\Pos_1$.

The parity condition $\Omega$ is defined as follows:

* $\Omega((e \in D_i, v))                       = 2 \times i$     if $D_i$ is a $\mu$ constant with index $i$ in $\mathcal D$.
* $\Omega((e \in D_i, v))                       = 2 \times i + 1$ if $D_i$ is a $\nu$ constant with index $i$ in $\mathcal D$.
* $\Omega((e \in \exists \bar x\ldotp \phi, v)) = 2 \times n + 1$ where $n$ is the length of $\mathcal D$.
* $\Omega(a, v)                                 = 2 \times n + 2$ otherwise.

Definition (Pre-models & Refutations)

:   For a $\mathcal G(\mathcal T) = (\Pos_0, \Pos_1, E, \Omega)$,
    a winning strategy for a player $i$ is a subgraph $(\Pos'_i, S_i)$ such that:

    1. If a node $p$ is in $\Pos_i$ and there are outward edges from $p$
       then there is exactly one edge outward edge from $p$ in $S_i$ and $p \in \Pos'_i$.
    2. If a node $p$ is not in $\Pos_i$ then all outward edges from $p$ in $E$ are in $S_i$ and $p \in \Pos'_i$.
    3. Player $i$ wins on every trace.

    We call a winning strategy for player $0$ a pre-model,
    and a winning strategy for player $1$ a refutation.

# Soundness & Completeness

Below, we define concepts that will be used later for proving the
soundness and completeness of the procedure.

Definition (Approximations)

:   For any ordinal $\tau$ and pattern $\alpha$, we define two new patterns:
    $\mu^\tau X\ldotp \alpha(X)$ and
    $\nu^\tau X\ldotp \alpha(X)$, with the following semantics:

    * $\denotation{\mu^0 X\ldotp \alpha(X)}_{M,\rho} = \emptyset$
    * $\denotation{\nu^0 X\ldotp \alpha(X)}_{M,\rho} = M$
    * $\denotation{\kappa^{\tau + 1} X\ldotp \alpha(X)}_{M,\rho}
      = \denotation{\alpha(X)}_{M,\rho[{\kappa^{\tau + 1} X\ldotp \alpha(X)}/X]}$
      where $\kappa$ is either $\mu$ or $\nu$.

    Then we have
    $\denotation{\mu X\ldotp \alpha(X)}_{M,\rho} = \Union_{\tau'} \denotation{\mu^0 X\ldotp \alpha(X)}_{M,\rho}$
    and $\denotation{\nu X\ldotp \alpha(X)}_{M,\rho} = \Intersection_{\tau'} \denotation{\mu^0 X\ldotp \alpha(X)}_{M,\rho}$.
    TODO: We need to prove this.

    We extend the notion of definition lists by allowing mappings of the form
    $D \mapsto \mu^\tau X \ldotp \alpha$
    and
    $D \mapsto \nu^\tau X \ldotp \alpha$.

Definition ($\mu$-measure -- $\umeasure$)

:   For an assertion $\alpha = \matches{e}{\phi}$, a definition list $\deflist$,
    a model $M$ and valuation $\rho$ such that $\rho{e} \in \denotation{alpha}_{M,\rho}$.

    Let $U_{k_1}, U_{k_2}, \ldots, U_{k_n}$ be the $\mu$-constants occuring in $\deflist$.
    We define the *$\mu$-measure* of $\alpha$ in $M$ for $\rho$ (or just *measure* for short), $\umeasure(\alpha)_{M,\rho}$
    to be the least tuple $(\tau_1,\ldots,\tau_n)$
    such that $\rho(e) \in \denotation{alpha}_{M,\rho}$
    where $\deflist'$ is obtained by replacing each $\mu$-constant $(U_{k_i} \mapsto \mu X\ldotp \alpha_{k_i}(X))$
    with $(U_{k_i} \mapsto \mu^{\tau_i} X\ldotp \alpha_{k_i}(X))$.

## Satisfiability implies a pre-model

Lemma

:   Given a tableau there is a pre-model or a refutation, but not both.

Lemma ($\mu$-measures are (non-strictly) decreasing over children in a pre-model)

:   \label{lemma:measures-decreasing}
    The following facts hold about signatures under a model $M$ and interpretation $\rho$:

    a. If $\matches{e}{\phi\lor\psi}$ has measure $\bar \tau$, then
       either $\matches{e}{\phi\psi}$ or $\matches{e}{\phi\psi}$
       has measure $\bar \tau$.

    b. If $\matches{e}{\exists \bar x \ldotp \phi}$ has measure $\bar \tau$, then
       there is a tuple $\bar m \subset M$
       with measure of $\matches{e}{\phi}$ equal to $\bar \tau$
       for interpretation $\rho[\bar m/\bar x]$.

    c. If $\matches{e}{\sigma(\bar \phi)}$ has measure $\bar \tau$, then
       there is a tuple $\bar m \subset M$
       such that for each $i$,
       the measure of $\matches{e}{\sigma(\bar x)}\land \matches{x_i}{\phi_i}$ is not bigger than $\bar \tau$
       for interpretation $\rho[\bar m/\bar x]$.

    d. If $\matches{e}{\phi\land\psi}$ has measure $\bar \tau$, then
       both $\matches{e}{\phi\psi}$ and $\matches{e}{\phi\psi}$
       have measure not larger than $\bar \tau$.

    e. If $\matches{e}{\forall \bar x \ldotp \phi}$ has measure $\bar \tau$, then
       for every tuple $\bar m \subset M$
       we have measure of $\matches{e}{\phi}$ is not larger than $\bar \tau$
       for interpretation $\rho[\bar m/\bar x]$.

    f. If $\matches{e}{\kappa X\ldotp \phi}$ has measure $\bar \tau$,
       and $\deflist(D_i) = \kappa X\ldotp \phi$ then
       $\matches{e}{D_i}$ also has measure $\bar \tau$.

    g. If $\matches{e}{D_i}$ has measure $\bar \tau$,
       and $\deflist(D_i) = \mu X\ldotp \phi$ then
       $\matches{e}{\phi[D_i/X]}$ has measure identical on the first $i - 1$ positions,
       with the $i$th strictly less.

    h. If $\matches{e}{D_i}$ has measure $\bar \tau$,
       and $\deflist(D_i) = \nu X\ldotp \phi$ then
       $\matches{e}{\phi[D_i/X]}$ also has measure $\bar \tau$.

Proof

:   Same as for guarded fixedpoint logic

Lemma (Satisfiable patterns have pre-models)

: Given a pattern $\phi$ and an element $m$ in $M$ such that
$e \in \denotation{\phi}$, then for any tableau $\mathcal T$, the game
$\mathcal G(\mathcal T)$ contains a pre-model.

Proof

:   We will build a strategy for the game by associating each constant in each
    position $p$ in the constructed strategy with an element in the model
    through a function $\rho_p$, while maintaining two invariants:

    1. Under this interpretation the atoms in the sequent are satisfied.
    2. Every element in a sequent has distinct interpretations.
    3. The measure does not increase between any parent and child.

    We will then show
    that the strategy must be a pre-model -- i.e. winning for player 0.

    The root position of the game is labeled with
    $\mathrm{root} = (\matches{e}{\phi}, \sequent{\matches{e}{\phi}\, \{\}, \{\}, \{e\}})$.
    Define $\rho_\mathrm{root} := e \mapsto m$
    and select the root node as part of the strategy.

    Consider a selected position $p$:

    * Suppose the (resolve) rule was applied at that position
      on the assertion $\matches{e_0, \sigma(e_1,\ldots,e_n)}$.
      Then if $\rho_p(c_0) \in \denotation{\sigma(e_1,\ldots,e_n)}_{\rho_p}$
      we select the left child position, $l$,
      (that has $\matches{c_0}{\sigma(e_1,\ldots,e_n)} \in \Atoms$).
      Otherwise, we select the right child position, $r$,
      (that has $\matches{c_0}{\bar\sigma(\lnot e_1,\ldots,\lnot e_n)} \in \Atoms$).
      We define $\rho_l = \rho_r = \rho_p$.

    * If the (or) rule was applied to assertion $\matches{e}{\psi_1 \lor \psi_2}$
      we select the child with $\matches{e}{\psi_1}$
      if $\umeasure(\matches{e}{\psi_1}) \le \umeasure(\matches{e}{\psi_2})$.
      Otherwise, we select the child with $\matches{e}{\psi_2}$.

    * Suppose the (app) rule was applied to assertion $\matches{c}{\sigma(\phi_1,\ldots,\phi_n)}$.
      We know that $\rho_p(c) \in \denotation{\sigma(\phi_1,\ldots,\phi_n)}_{M,\rho_p}$.
      Therefore there must be some $m_1,\ldots,m_n \in M$
      such that $m_i \in \denotation{\phi_i}_{M,\rho_p}$.

      Select a child of $p$,\newline
      say $p' = \sequent{\matches{e}{\sigma(\bar k)} \land \matches{k_i}{\phi_i}; \Atoms'; \Universals'; \Elements'}$,
      such that:
      * $\Elements' := \{ k_1,\ldots,k_n \} \union \{ e \} \union \Union_i \free{\phi_i}$, and
      * if for some $i$, $m_i = \rho_p(e)$ where $e \in \Elements$ then $k'_i = e$.
      * if $m_i = m_j$, then $k_i = k_j$.

      Define: $\rho_{p'} = \begin{cases}e   \mapsto \rho_p(e) & \text{when $e \in \Elements$} \\
                                        k_i \mapsto  m'_i \\ \end{cases}$

    * Suppose the (exists) rule was applied to assertion
      $\matches{c}{\exists \bar x \ldotp \phi}$.
      We know that $\rho_p(c) \in \denotation{\exists \bar x \ldotp \phi}_{M,\rho_p}$.
      Therefore there must be some $m_1,\ldots,m_n \in M$
      such that $\rho_p(c) \in \denotation{\phi}_{M,\rho_p[\bar m/\bar x]}$
      with measure $\tau$.

      Select a child of $p$,\newline
      say $p' = \sequent{\matches{e}{\phi[\bar k/\bar x]}; \Atoms'; \Universals'; \Elements'}$,
      such that:

      * $\Elements' := \{ k_1,\ldots,k_n \} \union \{ e \} \union \Union_i \free{\phi_i}$, and
      * if for some $i$, $m_i = \rho_p(e)$ where $e \in \Elements$ then $k'_i = e$.
      * if $m_i = m_j$, then $k_i = k_j$.

      Define: $\rho_{p'} = \begin{cases}e_{\phantom{i}}   \mapsto \rho_p(e) & \text{when $e \in \Elements$} \\
                                        k_i \mapsto  m'_i \\ \end{cases}$


    * For all other rules, it is player $1$'s turn.
      We must select all children as part of the strategy.
      Since the elements do not change, associate $\rho_p$ with all children.

    Now, we must show that the constructed strategy is a pre-model.
    We must check that every trace in the pre-model is winning for player $1$.

    Consider any finite trace.
    Because of the two invariants maintained, the (conflict) and (conflict-el)
    rules cannot apply, and all leafs are (ok) or (ok-el) nodes where player $0$ wins.

    Now, consider an infinite trace.
    If an (resolve), (or), or (and) nodes occur infinitely often,
    some other node of lower parity must also occur infinitely often.
    Consider the lowest priority node that occurs inifinitely often.
    If it is a (nu), (dapp), or (forall), then player $1$ wins.
    It cannot be a (mu) node since (mu) nodes strictly decrease the measure, a well-founded measure.
    Suppose it is a (exists) or (app)-node (for sake of contradiction).
    Let us consider an (infinite) suffix of the trace that doesn't have any (nu) or (mu) nodes.
    This must exist, otherwise (mu) or (nu), with lower priority would repeat infinitely.
    Now, every the remaining rules (i.e. excluding (mu) and (nu)) reduce the depth of the pattern.
    So, (exists) or (app) cannot infinitely occur without a (mu) or (nu) rule appearing infinitely often as well.

Notice that this proof does not in anyway rely on the properties of guarded patterns.
Thus, if it is shown that no pre-model exists for any tableau the pattern is not
satisfiable.

## Pre-models imply satisfiability

Next we want to show that for any guarded pattern,
if player $1$ wins, then the pattern is indeed satisfiable
-- i.e. for every pre-model, there is a satisfying model.
To do so, we will construct a model from the pre-model.

Let $S$ be a pre-model for a tableau $\mathcal T = \langle N , L : N \to \Sequent \rangle$.
For a constant $c \in K$, we say that two nodes $v, w \in N$ are $c$-equivalent if
$c$ is in the elements of each node in the path from $v$ to $w$, inclusive.
This relation defines an equivalence class.
Notice that each equivalence class is a subtree of the tableau.

From our pre-model $S$, we define a model $M(S)$.
Let $T_{\equiv_c}$ be the set of equivalence classes in $T$ for a constant $c$
and $T_{\equiv_K} = \Union_{c\in K} T_{\equiv_c}$.

Let the carrier set $M \subset K \times T_{\equiv_K}$ of the constructed model
be the pairs of elements in the sequents of nodes used by the winning strategy
and their corresponding $c$-equivalence classes.

For $m_i = (e_i, v_i) \in M$, and symbol $\sigma$,
we define $\sigma_{S(M)}$ as follows:

* $m_0 \in \sigma_M(m_1,\ldots,m_n)$
  if $\matches{e_0}{\sigma(e_1,\ldots,e_n)}$
  is an assertion in a sequent of $\Intersection_{0\leq i \leq n} v_i$.
* $m_0 \not\in \sigma_M(m_1,\ldots,m_n)$
  if $\matches{e_0}{\lnot\sigma(e_1,\ldots,e_n)}$
  is an assertion in a sequent of $\Intersection_{0\leq i \leq n} v_i$.
* otherwise, it is not important which one holds.
  Arbitarily, we choose $m_0 \in \sigma_M(m_1,\ldots,m_n)$
  if neither $\matches{e_0}{\sigma(e_1,\ldots,e_n)}$ nor $\matches{e_0}{\lnot\sigma(e_1,\ldots,e_n)}$
  are in any of the nodes.

This is well-defined since whenever a new element is created in the tableau (resolve) is applied immediately.
Further, a pre-model may only include one child of the (resolve) node.

Definition ($\nu$-measure -- $\vmeasure$)

:   Suppose, $\rho(m) \not\in \denotation{\phi}_{M,\rho}$.
    Then $\rho(m) \in \denotation{\lnot\phi}_{M,\rho}$
    and the $\mu$-measure of $\matches{m}{\lnot\phi}$ is defined
    (after converting to positive-normal form).
    We call this the $\nu$-measure of $\matches{m}{\phi}$ in $M,\rho$.

Lemma

:   \label{lemma:vmeasure} For a $\nu$-measure, the dual of Lemma \ref{lemma:measures-decreasing} holds.

Lemma

:   \label{lemma:guards}
    Let $\alpha = \matches{c}{\phi} = \matches{c}{\phi_1(\bar x, \bar y) \land \cdots \land \phi_n(\bar x, \bar y)}$
    where each $\phi_i$ is of the form $\sigma(\bar x)$ where $\bar x$ is a tuple of element variables.
    and   each variable in $\bar y$ co-exists with a variable in $\{c\} \union \bar x \union \bar y$
          for some application $\phi_i$.
    Then, if there is a valuation $\rho: \{c\} \union \bar x \union \bar y \to M(S)$ such that
    $\rho(c) \in \denotation{\alpha}_{M(S),\rho}$ and $\Intersection_{x\in\{c\}\bar x}\rho(x) \neq \emptyset$
    taken as a set of vertices
    then $\Intersection_{x\in\{c\}\bar x\union\bar y}\rho(x) \neq \emptyset$.

Proof

:   Same as Guarded Fixedpoint Logic.

Lemma (Pre-model implies satisfiability)

:   For a *guarded* pattern $\phi$ and a pre-model $S$, $M(S) \satisfies \phi$.

Proof

:   Suppose, by way of contradiction, $\psi$ is not satisfied in $M(S)$.
    We will use this to prove that there must by a play conforming to $S$ such that player $1$ wins
    -- i.e. $S$ is not a winning strategy for player 0, and therefore not a pre-model.
    Along this play we maintain these invariants:

    * At each position $p = (\matches{e}{\phi}, s)$,
      we define a evaluation $\rho_p$ such that $\rho_p(e) \not\in \denotation{\phi}_{M,\rho_p}$.
    * The $\nu$-measure at each position is decreasing.

    The root of the play is $(\matches{e}{\psi}, v = \sequent{\matches{e}{\phi}; ...; \{e\};})$.
    By our assumptions, $\vmeasure(\psi)$ is defined.
    We define $\rho_p(e)$ to be the $e$-equivalence defined by the root node.

    Consider a paritally constructed play until position $p = (\matches{e}{\phi}, s)$:

    * (conflict)/(ok): $\phi$ cannot be an atomic application or an element variable
        by definition of $M(S)$ and by our invariants.
    * (resolve): Application of this rule does not affect the $\nu$-measure.
        or the elements in the sequent. We use the same $\rho_p$ for the child node.
        Since it is player $1$'s turn, there is no choice to make.
    * (or): if $\phi = \zeta \lor \eta$ then by Lemma \ref{lemma:vmeasure},
        $\vmeasure(\phi) \leq \vmeasure{\zeta}$ and $\vmeasure(\phi) \leq \vmeasure{\eta}$.
        Since it is player $1$'s turn, there is no choice to make.
        We use the same $\rho_p$ for the child node.
    * (and): if $\phi = \zeta \land \eta$ then by Lemma \ref{lemma:vmeasure},
             for some $\theta \in \{\zeta, \eta\}$
             we have $\vmeasure(\phi) = \vmeasure{\theta}$.
             We select the child corresponding to $\theta$ as the next position in the play.
             We use the same $\rho_p$ for the child node.
    * (exists): if $\phi = \exists \bar x\ldotp \gamma$,
                then by Lemma \ref{lemma:vmeasure}, the measure doesn't increase.
                We extend $\rho_p$ to evaluate each constant to its corresponding equivalence class.
    * (app):    Similar to (exists).
    * (forall): if $\phi = \forall \bar x\ldotp \alpha(\bar x, \bar y) \limplies \phi(\bar x, \bar y)$
        then we may choose between an immediate instantiation, or postponing instantiation
        until until after application of (exists) or (app).

        Since $\rho_p(e) \not\in \denotation{\phi}_{M,\rho_p}$
        we know that there is some extension $\rho'$ to $\rho_p$ such that
        $\rho'(e) \in \alpha(\bar x, \bar y) \land \lnot \phi(\bar x, \bar y)$
        and by Lemma \ref{lemma:vmeasure} that $\nu$-measure
        of the corresponding assertion is not larger than the current $\nu$-measure.

        By Lemma \ref{lemma:guards}, there is a position $w \in \Intersection_{x\in\{c\}\bar x\union\bar y}\rho'(x)$.
        If $v = w$ then we choose the corresponding instantiation.
        If $v \neq w$ then choose the child the $v$ on the path to $w$.

    * (dapp): Similar to (forall).
    * In the remaining cases there is no choice.

    We must show that the trace constructed above is winning for player $1$.
    First, note that the above trace is infinite.
    If the node with least parity occuring infinitely often is an existential, then player $1$ wins.
    If cannot be a universal, because of the way we build the trace -- we know that
    there is a finite path to a node with an instatiation that contradicts the quantifier.
    $\mu$ patterns are winning for player $1$ while $\nu$ patterns decrease the $\nu$-measure.
    So, the trace must be winning for player $1$ and the pattern is satisfiable.

\fbox{\parbox{\textwidth}{
\color{red}{Xiaohong: Review upto here.}
}}

## Refutations as proofs

Let us take a look refutations through the lens of checking the validity of a pattern.

\newcommand{\vmatches}[2]{( #1 \land #2 ) \limplies \bot}

- If a game position is labeled with assertion $\matches{e}{\phi}$,
  it may be viewed as a proof for then validity of the pattern $\vmatches{e}{\phi}$.
- The (exists) can be thought of as a combination of
  the matching logic proof rule ($\exists$-Generalization)
  and a case analysis over the distinctness of each pair of free variables and the newly introduced variables.

  This also validates the (conflict-el) rule.
- The difficult things left involve dealing with infinite traces:
    1. Constructing a finite proof from a $\mu$-traces.
       We could likely use unfolding within a contextual implication here.
    2. $\exists$-traces must decrease the size of the pattern at each step, and so cannot be infinite.
    3. $\nu$-traces     are winning for player $0$ and cannot be part of a refutation.
    4. $\forall$-traces are winning for player $0$ and cannot be part of a refutation.

----

\fbox{\parbox{\textwidth}{
\color{red}{Under construction, do not review}
}}

1. View them as transitions in the strategy rather than in the tableau
2. Only consider the perspective of building a refutation
3. Sequents and assertions are presented differently.
4. Display them as proof rules rather than tableaux rules.

\begin{align*}
\cline{1-3}
\name{conflict}                 & \vruleun{ \Atoms, ... \proves \alpha \limplies \bot }
                                          { \valid } \\
                                & \text{when $\alpha$ is an atomic assertion, with its negation  in $\Atoms$.}
\\
\name{conflict-el}              & \vruleun{ \Atoms, ... \proves \vmatches{e}{e'} }
                                          { \valid } \\
                                & \text{when $e' \neq e$ is an element in $\Elements$.}
\\
\cline{1-3}
\name{and}                      & \vruleun{ ... \proves \vmatches{e}{\phi \land \psi} }
                                           { ... \proves \vmatches{e}{\phi} }
\qquad
                                  \vruleun{ \vmatches{e}{\phi} \land \vmatches{f}{\psi}}
                                           { ... \proves \vmatches{e}{\phi} }
\\
                                & \vruleun{ ... \proves \vmatches{e}{\phi \land \psi} }
                                           { ... \proves \vmatches{e}{\psi} }
\qquad
                                  \vruleun{ \vmatches{e}{\phi} \land \vmatches{f}{\psi}}
                                           { ... \proves \vmatches{f}{\psi} }
\\
\name{or}                       & \vrulebin{...\proves \vmatches{e}{\phi \lor \psi} }
                                           {...\proves \vmatches{e}{\phi}}
                                           {...\proves \vmatches{e}{\psi}}
\qquad
                                  \vrulebin{...\proves \vmatches{e}{\phi} \lor \vmatches{f}{\psi} }
                                           {...\proves \vmatches{e}{\phi}}
                                           {...\proves \vmatches{e}{\psi}}
\\
\name{def}                      & \vruleun{...\proves \vmatches{e}{\kappa X . \phi(X)}}
                                  {\vmatches{e}{D}} \\
                                & \text{when $D := \kappa X. \phi(X) \in \deflist$ }
\\
\name{mu}                    & \vruleun{ ...\proves \vmatches{e}{D}}
                                       { ...\proves \vmatches{e}{\phi[D/X]}} \\
                                & \text{when $D := \mu X. \phi \in \deflist$ }
\\
\name{nu}                    & \vruleun{ ...\proves \vmatches{e}{D} }
                                       { ...\proves \vmatches{e}{\phi[D/X]} } \\
                                & \text{when $D := \nu X. \phi \in \deflist$ }
\\
\name{dapp} &
    \vruleun{ \vmatches{e}{\bar\sigma(\bar \phi)} }
            { \mathrm{inst} \union \Gamma; 
              \vmatches{e}{\bar\sigma(\bar \phi)} } \\
  & \text{where $\mathrm{inst} = \left\{ \vmatches{e}{\sigma(\bar c)} \limplies \lOr_i \vmatches{c_i}{\phi_i}
                                    \mid \text{ if } \bar c \subset \Elements \right\}$} \\
  & \text{and $\matches{e}{\bar \sigma(\bar \phi)}$ is not an atomic assertion.}
\\
\name{forall}                   & \unsatruleun { \sequent{ \matches{e}{\forall \bar x \ldotp \phi(\bar x)}, \Gamma; \Universals; \Elements; ... } }
                                               { \sequent{ \mathrm{inst} \union \Gamma
                                                         ; \matches{e}{\forall \bar x \ldotp \phi}, \Universals
                                                         ; \Elements
                                                         ; ... } } \\
                                & \text{where $\mathrm{inst} = \{ e \in \phi[\bar c / \bar x] \mid c \subset \Elements \}$}
\\
\cline{1-3}
\intertext{The following rules may only apply when none of the above rules apply -- i.e. when all assertions in $\alpha$
are either existentials or applications}
\name{choose-existential} &
\unsatruleun {\sequent{ \Gamma; ... }}
             {\{ \alpha \leadsto \sequent{ \Gamma;\Atoms; \Universals; \Elements }\}}
    \qquad  \text{for each $\alpha \in \Gamma$}
   \\ 
\name{app} &
  \satruleun { \matches{e}{\sigma(\bar \phi)} \leadsto \sequent{ \Gamma; \Atoms; \Elements } }
             { \{ \sequent{ \matches{e}{\sigma(\bar k)} \land \lAnd_i \matches{k_i}{\phi_i}, \Gamma' \union \Universals'; \Atoms' ; \{ \} ; \Elements'  } \} } \\
  & \text{for each $\bar k \subset K$} \\
  & \text{where} \\
  & \text{\qquad $\Elements' = \bar k \union \{ e \} \union  \free{\bar \phi}$} \\
  & \text{\qquad $\Atoms' = \{ a \mid a \in \Atoms \text{ and } \free{a} \subset \Elements' \}$ \quad($\Atoms$ restricted to $\Elements'$)} \\
  & \text{\qquad $\Gamma' = \{ \gamma \mid \gamma \in \Gamma \text{ and } \free{\gamma} \subset \Elements' \}$ \quad($\Gamma$ restricted to $\Elements'$)} \\
  & \text{\qquad $\Universals' = \{ \alpha \mid \alpha \in \Universals \text{ and } \free{\gamma} \subset \Elements' \}$ \quad($\Universals$ restricted to $\Elements'$)} \\
\\
\name{exists} &
  \satruleun { \matches{e}{\exists \bar x \ldotp \phi(\bar x)} \leadsto \sequent{ \Gamma; \Atoms; \Universals; \Elements } }
             { \{ \sequent{ \alpha, \Gamma' \union \Universals'; \Atoms' ;  \{ \}; \Elements' } \}
             } \\
  & \text{for each $\alpha \in \{ \matches{e}{\phi[\bar k/\bar x]} \mid \bar k \subset K \}$} \\
  & \text{where} \\
  & \text{\qquad $\Elements'   = \free{\alpha}$} \\
  & \text{\qquad $\Atoms'      = \{ a \mid a \in \Atoms \text{ and } \free{a} \subset \Elements' \}$ \quad($\Atoms$ restricted to $\Elements'$)} \\
  & \text{\qquad $\Gamma'      = \{ \gamma \mid \gamma \in \Gamma \text{ and } \free{\gamma} \subset \Elements' \}$ \quad($\Gamma$ restricted to $\Elements'$)} \\
  & \text{\qquad $\Universals' = \{ \alpha \mid \alpha \in \Universals \text{ and } \free{\alpha} \subset \Elements' \}$ \quad($\Universals$ restricted to $\Elements'$)} \\
\\
\cline{1-3}
\intertext{This rule must apply only immediately after the (exists)/(app) rules or on the root node.
$\mathsf{fresh}$ denotes the fresh variables introduced by the last application of those rules.}
\name{resolve} & \satrulebin{\sequent{\Gamma; A; C}}
                            {\sequent{ \Gamma; \matches{e}{\sigma(\bar a)}, A; C}}
                            {\sequent{ \Gamma; \matches{e}{\lnot\sigma(\bar a)}, A; C}} \\
               & \text{when $\{e\}\union \bar a \subset C$ and $(\{e\}\union \bar a)\intersection \mathsf{fresh} \neq \emptyset$.}
\\
\cline{1-3}
\end{align*}
-->

----

Lemma

:   For any pattern (guarded or not), the existance of a refutation implies
    $\lnot \phi$ is valid.


Theorem (Emerson; Julta)

: For every parity game, if a player has a winning strategy, then there is a
  memoryless winning strategy for player $i$.

# Functional symbols

A symbol $f$ is called functional
if, for any tuple of element $\bar a$,
$\size{f_M(\bar a)} = 1$.

Proposition (Functional Axioms)

:   A symbol $f$ is functional iff it satisfies the axiom:
    $$\forall \bar x \ldotp \exists y. f(\bar x) = y$$

This axiom is 

# Pseudocode

```
class ClosureMembership:
    --- Assertion of the form $e \in App(\bar args)$ or $e \in e'$
    atom: Assertion

    --- Status
    status in: Holds, DoesNotHold, Undecided

    --- Node in which membership's status was decided.
    --- Must have type App or Exists for status = Undecided
    --- and type Resolve or Unify for Holds and DoesNotHold.
    originating_node: GameNode

class GameNode:
    type in:
        Unsat(  conflict: Assertion, ClosureMembership )

          And(   matched: Assertion)
           Or(   matched: Assertion)
          Def(   matched: Assertion)
       Unfold(   matched: Assertion)
         DApp(   matched: Assertion)
       Forall(   matched: Assertion)

          App(   matched: Assertion)
       Exists(   matched: Assertion)

      Resolve(membership: ClosureMembership)
        Unify(     first: EVar, second: EVar) -- EVars we unify on.
                                              -- We require that `first` is fresh.
          Sat()

   Incomplete( assertion: Assertion)
     Backlink(      node: GameNode)

    --- For Gamma, only existentials and universals need to be stored.
    --- The rest are immediately processed.
    universals:     Set{ Assertion }
    existentials:   Set{ Assertion }

    --- A
    atoms:          Set{ ClosureMembership }

    --- C
    constants:      Set{ EVar }

    children:       Set { GameNode}

--- Builds a graph representation of G(T) for the pattern phi.
def build_game_init(phi):
    --- e = fresh_constant()
    g = GameNode( type = Incomplete(Assertion(\exists e. e \in phi))
                , children = undefined
                , universals = {}
                , existentials = {}
                , atoms = {}
                , constants = {}
                )
    complete_nodes([g], {})

def complete_nodes(incomplete_nodes, processed_nodes):
    curr, remaining = incomplete_nodes
    
    if has_same_existentials_universals_atoms_and_matched_in(curr, processed_nodes):
        curr.type = Backlink(curr)
        complete_nodes(remaining, processed_nodes)
        return
    if is_atomic_assertion(assertion):
        membership = get_membership_for_assertion(curr, assertion)
        if  matches(assertion, membership):
            curr.type = Sat()
            return
        elif conflicts(assertion, membership):
            curr.type = Unsat(assertion, membership)
            return
        else:
            --- assertion is undecided.
            --- We must clone the sub-game starting from where the membership we care about originated.
            --- on one branch, the assertion is satisfiable, on the other it is not.

            orig = membership.originating_node
            --- assert orig.parent.type matches App( _ ) or Exists( _ )

            --- The clone operation copies the entire tree begining at orig,
            --- with one copy where the membership holds, and one where it does not.
            --- If a node in the `incomplete_nodes` list is cloned,
            --- the clones are placed into the new copy of the list,
            --- otherwise, the original is left in the list.
            --- Preferably, a stable order is maintained.
            left_clone_membership, right_clone_membership,
            left_clone_orig, right_clone_orig,
            incomplete_nodes = orig.clone_resolving_membership(membership, incomplete_nodes) 
            orig.children = { GameNode( type = Resolve(parent_membership, left_clone_membership, right_clone_membership)
                                      , universals = orig.universals
                                      , existentials = orig.existentials
                                      , atoms =  orig.atoms
                                      , contants = orig.constants
                                      , children = { left_clone_orig, right_clone_orig }
                                      )
                            }
            complete_nodes(incomplete_nodes, processed_nodes)
            return
    if assertion matches Assertion(e \in And(phi, psi)):
        curr.type     = And(assertion)
        left = GameNode( type = Incomplete(e \in phi)
                       , children = undefined
                       , ... --- copy other parameters
                       )
        --- TODO(clone-incomplete-nodes)
        right = GameNode( type = Incomplete(e \in phi)
                        , children = undefined
                        , ...)
        node.children = { left, right }
        complete_nodes({ left, right } + remaining, { curr } + processed_nodes)
    if assertion matches Assertion(e \in Or(phi, psi)):
        --- identical to above besides assignment to curr.type
    if assertion matches Assertion(e \in Mu/Nu):
        --- build single child
    if assertion matches Assertion(e \in SVar(D)):
        --- build single child
    if assertion matches Assertion(e \in Forall(x, Phi)):
        type = Forall(assertion)
        curr.universals += assertion
        --- instantiate with all permutations of curr.constants, and no fresh variables.
        instantiations = make_conjunction(instantiate(assertion, curr.constants, 0))
        curr.children = { GameNode( type = Incomplete(Instantiations)
                                  , children = undefined
                                  , ...)
                        }
        complete_nodes(curr.children + remaining, {curr} + processed_nodes)
        return
    if assertion matches Assertion(e \in DApp(...)):
        --- similar to above

    if assertion matches Assertion(e \in Exists(...)):
        --- TODO: I think this is OK to process immediately,
        --- since we are building the parity game and not the tableau.
        --- Any changes to the membership created by other branches of the game
        --- will propagate from here, and replicate the same conflicts.
        --- We should think about this more, though.

        --- TODO: Can we apply the unify rule here to reduce size of the tableau?
        --- We need the child node to bring in only the constants
        --- that are required for handling the existential,
        --- otherwise, the number of constants will grow unbounded
        --- and we may not terminate.
        ---
        --- I think figuring out the correct application of the (unify) rule is the source
        --- of undecidability for un-guarded patterns.
        --- What is it about guarded patterns that avoids this?!
        ---
        --- We therefore avoid using it for now and just try all possible instantiations.

        type = Exists(assertion)
        new_constants = make_fresh(len(assertion.bound_vars), curr.constants)
                      + free_vars(assertion)
        curr.children = {}
        for instantiation in instantiations(assertion, curr.constants, len(assertion.free_evars())):
            child += { GameNode( type = Incomplete(curr.children)
                               , children = undefined
                               , existentials = { a | a in curr.existentials and a.free_evars() <= instantiation.free_evars()) }
                               , universals   = { a | a in curr.universals   and a.free_evars() <= instantiation.free_evars()) }
                               , memberships  = { a | a in curr.memberships  and a.free_evars() <= instantiation.free_evars()) }
                     }
        complete_nodes(curr.children + remaining, {curr} + processed_nodes)
        return
```

## Notes

- Clean up deflist
    - Add deflist case for element, set variables
    - Clarify merge operator ofr deflists
    - Use list of order list of constants
    - Give examples
    - Can we define a pre-order
- Assertions
    - use x instead of c/e
    - ELement variables x, y, z
    - Symantically => Intuitively
    - ONly use positive form for assertions
- Seqeunts
    - Atoms, Univesrals, Elements => Use greek letters
- Tableau
    - Remove requirement for guarded pattern
    - Remove K is a set of "distinct"
    - Get rid of K
        - State that tableau if for $\phi$
- Proof that there we use a bounded set of constatns

Novelties:

1. We build a model and refutation simultanously, throught the introduction
   of the (resolve) tableau rule.
2. If the tableau is not accepted, then the the negation is valid
   (irrespective of guardedness).
3. This has practical implications for the implementation as well
   --- It allows us to use alpha equivalence to reduce the
   size of the representation of the tableau.

1. Implementation

    a. Implement resolution procedure
    b. Implement alpha-equivalence over the nodes in the tableau (very important for efficiency)
    c. Test on benchmarks (LTL (finite/infinite); PDL; SL)

2. Theory

    a. Extend to handle nested guards, as in packed logic.
    b. Extract proof object from refutation.
    c. Handling functional symbols. Look at Lucas' work on Basic Function Patterns.
    d. Look at finite variant property and see if we can relate it to guarded patterns

3.  Minor additional work

    1. Find a better name for $\Elements$. THey are not the same as elements in
       the constructed model, so this is confusing. Maybe "elemental constants"?
       to correspond with fixedpoint constants?

---

