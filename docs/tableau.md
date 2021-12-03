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

\newpage

# Tableau, Games & Strategies

We define our procedure over "positive-form" patterns
-- patterns where negations are pushed down as far as they can go using De
Morgan's and related equivalences.

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

When $\sigma$ is a nullary symbol we use $\sigma$ and $\bar \sigma$ as shorthand for $\sigma()$ and $\bar \sigma()$.

Remark

: We allow negation of element variables, but not set variables.
  This ensures that set variables may only occur positively in their binding fixedpoint.

Further, we restrict ourselves to "well-named" patterns
-- patterns where each set and element variable is uniquely named.
Through alpha-renaming, all patterns are equivalent to some well-named pattern
so there is no loss in generality here.

To simplify the presentation of the tableau and parity game,
we introduce *fixedpoint markers*.
Fixedpoint markers are notational shorthand to represent fixedpoint sub-patterns of a pattern.

Definition (Definition list)

:   For a guarded pattern $\phi$, a *definition list*
    (denoted $\deflist^\phi$ or just $\deflist$ when $\phi$ is understood)
    is a mapping from each occurring set variable to the pattern by which it is bound.
    Since we assume well-named patterns, each set variable is bound by a unique
    fixedpoint pattern and such a mapping is well-defined.
    We use $\deflist^\phi(X)$ to denote the fixedpoint sub-pattern corresponding to the set variable $X$.

Definition (Fixedpoint marker)

:   For a definition list $\deflist^\phi$,
    we call $\deflist^\phi_X$ (or just $\deflist_X$ when $\phi$ is understood)
    a *fixedpoint marker*.
    We call a marker a $\mu$-marker if the corresponding fixedpoint pattern is a $\mu$ pattern
    and a $\nu$-marker otherwise.
    We extend the syntax of patterns to allow fixedpoint markers. These markers may
    be used whereever set variables may be used -- in particular, they may not
    appear negated in positive-form patterns. We define the evaluation of fixedpoint
    makers as the evaluation of their corresponding fixedpoint pattern:
    $$\evaluation{\deflist^\phi_X}_{M,\rho} = \evaluation{\deflist^\phi(X)}_{M,\rho}$$


\newcommand {\dependson}{\prec^\phi}

Definition (depends on) 

:   For two fixedpoint markers $\deflist^\phi_X$ and $\deflist^\phi_Y$,
    we say $\deflist^\phi_X$ *depends on* $\deflist^\phi_Y$
    if $\deflist^\phi(Y)$ is a sub-pattern of $\deflist^\phi(X)$.

The transitive closure of this relation is a pre-order -- i.e. it is reflexive and transitive.
It is also antisymmetric -- for a pair of distinct markers $\deflist^\phi_X$ and $\deflist^\phi_Y$
we may have either $\deflist^\phi_X$ transitively depends on $\deflist^\phi_Y$
or $\deflist^\phi_Y$ transitively depends on $\deflist^\phi_X$ but not both.
So, it is also a partial order.

Definition (Dependency order)

:   For a pattern $\phi$, a *dependency order*, 
    is an (arbitary) extension of the above partial order to a total (linear) order.

Note that the partial order may extend to several total orders.
For defining our parity game, it does not matter which one we choose so long as it is a total order.
So, through abuse of notation, we use $\dependson$ to denote some arbitary dependency order.

Example

:   For the pattern, $\nu X \ldotp (s(X) \land \mu Y \ldotp z \lor s(Y))$,
    we have $$\deflist^\phi = 
    \begin{cases}
    X &\mapsto \nu X \ldotp (s(X) \land \mu Y \ldotp z \lor s(Y)) \\
    Y &\mapsto \mu Y \ldotp z \lor s(Y)
    \end{cases}$$

    and a dependency order: $X \dependson Y$.

Example

:   For the pattern, $\nu X \ldotp s(X) \land \bar p \land \mu Y \ldotp s(Y) \land p$,
    we have $$\deflist^\phi = 
    \begin{cases}
    X &\mapsto \nu X \ldotp s(X) \land \bar p \\
    Y &\mapsto \mu Y \ldotp s(Y) \land p
    \end{cases}$$

    and dependency order: $X \dependson Y$.
    However, this isn't the only dependency order -- we also have $Y \dependson X$.

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

    1. a tuple, $\sequent{\Gamma; \Basic; \Universals; \Elements}$,
       where $\Gamma$       is a set of assertions,
             $\Basic$       is a set of basic assertions,
             $\Universals$  is a set of assertions whose pattern is of the form $\bar\sigma(...)$ or $\forall \bar x\ldotp ...$,
         and $\Elements$    is a set of element variables.
    2. $\alpha \leadsto \sequent{\Gamma; \Basic; \Universals; \Elements}$ where $\alpha$ is an assertion
       and $\Gamma, \Basic, \Universals, \Elements$ are as above.
    3. $\unsat$

    For a sequent $v$ of the first two forms, we use $\Gamma(v), \Basic(v), \Universals(v)$ and $\Elements(v)$
    to denote the corresponding component of the sequent.

Informally,
$\Gamma$ represents the set of assertions whose combined satisfiability we are checking.
$\Basic$ and $\Universals$ represent assertions we have deemed must hold for the variables in $\Elements$.
Each variable in $\Elements$ corresponds (roughly) to a distinct element in the
model we are building (if one exists).
We will go into more details about this later.

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

\allowdisplaybreaks
\begin{align*}
\cline{1-3}
\name{conflict}                 & \pruleun{\sequent{\{ \alpha \} \union \Gamma; \{ \fnot{\alpha} \} \union \Basic; \Universals; \Elements}}
                                          { \unsat }
                           \qquad \text{when $\alpha$ is a basic assertion.}
\\
\name{ok}                       & \pruleun{\sequent{\{ \alpha \} \union \Gamma; \{ \alpha \} \union \Basic; \Universals; \Elements}}
                                    {\sequent{        \Gamma; \Basic; \Universals; \Elements}}
                           \quad \text{when $\alpha$ is a basic assertion.}
\\
\name{conflict-el}              & \pruleun{\sequent{\matches{x}{y}, \Gamma; \Basic; \Universals; \Elements}}
                                          { \unsat }
                            \quad \text{when $x$ and $y$ are distinct.}
\\
\name{ok-el}                    & \pruleun{\sequent{\matches{x}{x}, \Gamma; \Basic; \Universals; \Elements}}
                                          {\sequent{                \Gamma; \Basic; \Universals; \Elements}} \\
\\
\cline{1-3}
\name{and} &
                                  \unsatruleun{\sequent{ \matches{z}{\phi} \land \matches{w}{\psi},   \Gamma; \Basic; \Universals; \Elements}}
                                              {\sequent{ \matches{z}{\phi}, \matches{w}{\psi},  \Gamma; \Basic; \Universals; \Elements}}
\\
\name{or} &
                                  \satrulebin{\sequent{ \matches{z}{\phi} \lor \matches{w}{\psi}, \Gamma; \Basic; \Universals; \Elements }}
                                             {\sequent{ \matches{z}{\phi}, \Gamma; \Basic; \Universals; \Elements }}
                                             {\sequent{ \matches{w}{\psi}, \Gamma; \Basic; \Universals; \Elements }}
\\
\name{def}                      & \pruleun{\sequent{ \matches{z}{\kappa X . \phi(X)}, \Gamma; \Basic; \Universals; \Elements }}
                                  {\sequent{ \matches{z}{D}, \Gamma; \Basic; \Universals; \Elements }} \\
                                & \text{when $D := \kappa X. \phi(X) \in \deflist$ }
\\
\name{mu}                    & \pruleun{\sequent{ \matches{z}{D}, \Gamma; \Basic; \Universals; \Elements }}
                                          {\sequent{ \matches{z}{\phi[D/X]}, \Gamma; \Basic; \Universals; \Elements }} \\
                                & \text{when $D := \mu X. \phi \in \deflist$ }
\\
\name{nu}                    & \pruleun{\sequent{ \matches{z}{D}, \Gamma; \Basic; \Universals; \Elements }}
                                          {\sequent{ \matches{z}{\phi[D/X]}, \Gamma; \Basic; \Universals; \Elements }} \\
                                & \text{when $D := \nu X. \phi \in \deflist$ }
\\
\name{\dapp} &
\unsatruleun{\sequent{ \{\matches{z}{\bar\sigma(\bar \phi)}\} \union \Gamma; \Basic; \Universals; \Elements}}
            { \sequent{ \mathrm{inst} \union \Gamma;
                        \Basic;
                        \{\matches{z}{\bar\sigma(\bar \phi)}\} \union \Universals;
                        \Elements } }
\qquad \text{when $\matches{z}{\bar \sigma(\bar \phi)}$ is not a basic assertion.} \\
  & \text{where $\mathrm{inst} = \left\{ \matches{z}{\fnot{\sigma(\bar y)}} \lor \lOr_i \matches{y_i}{\phi_i}
                                    \mid \bar y \subset \Elements \right\}$} \\
\\
\name{forall}                   & \unsatruleun { \sequent{ \matches{z}{\forall \bar x \ldotp \phi}, \Gamma; \Basic; \Universals; \Elements} }
                                               { \sequent{ \mathrm{inst} \union \Gamma
                                                         ; \Basic
                                                         ; \matches{z}{\forall \bar x \ldotp \phi}, \Universals
                                                         ; \Elements
                                                         } } \\
                                & \text{where $\mathrm{inst} = \{ \matches{z}{ \phi[\bar y / \bar x]} \mid \bar y \subset \Elements \}$}
\\
\cline{1-3}
\intertext{The following rules may only apply when none of the above rules apply -- i.e. when all assertions in $\alpha$
are either existentials or applications}
\name{choose-existential} &
\unsatruleun {\sequent{ \Gamma; \Basic; \Universals; \Elements }}
             {\{ \alpha \leadsto \sequent{ \Gamma;\Basic; \Universals; \Elements } \mid \text{for each $\alpha \in \Gamma$}\}}
   \\ 
\name{app} &
  \satruleun { \matches{z}{\sigma(\bar \phi)} \leadsto \sequent{ \Gamma; \Basic; \Universals ; \Elements } }
             { \{ \sequent{ \matches{z}{\sigma(\bar k)} \land \lAnd_i \matches{k_i}{\phi_i}, \Gamma' \union \Universals'; \Basic' ; \{ \} ; \Elements'  } \} } \\
  & \text{for each $\bar k \subset \{z\} \union \free{\bar \phi} \union (K \setminus \Elements)$} \\
  & \text{where} \\
  & \text{\qquad $\Elements' = \bar k \union \{ z \} \union  \free{\bar \phi}$} \\
  & \text{\qquad $\Basic' = \Basic|_{\Elements'}$},
    \text{       $\Gamma' = \Gamma|_{\Elements'}$},
    \text{and    $\Universals' = \Universals|_{\Elements'}$} \\
\\
\name{exists} &
  \satruleun { \matches{z}{\exists \bar x \ldotp \phi} \leadsto \sequent{ \Gamma; \Basic; \Universals; \Elements } }
             { \{ \sequent{ \alpha, \Gamma' \union \Universals'; \Basic' ;  \{ \}; \Elements' } \}
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
\name{resolve} & \satrulebin{\sequent{ \Gamma; \Basic; \Universals; \Elements}}
                            {\sequent{ \Gamma; \matches{x_0}{\sigma(x_1,\ldots,x_n)}      \union \Basic; \Universals; \Elements}}
                            {\sequent{ \Gamma; \matches{x_0}{\lnot\sigma(x_1,\ldots,x_n)} \union \Basic; \Universals; \Elements}} \\
               & \text{when neither $\matches{x}{{\sigma(x_1,\ldots,x_n)}}$ nor $\matches{x}{\fnot{\sigma(x_1,\ldots,x_n)}}$ are in $\Basic$} \\
               & \text{and  $\bar x \subset \Elements$ and $\bar x \intersection \mathsf{fresh} \neq \emptyset$.} \\
\\
\cline{1-3}
\end{align*}

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
But first, we must define what a parity game is.

Definition (Parity game)

:   A parity game is a tuple $(\Pos_0, \Pos_1, E, \Omega)$
    where $\Pos = \Pos_0 \union \Pos_1$ is a possibly infinite set of positions;
    $E : \Pos \times \Pos$ is a transition relation;
    and $\Omega : \Pos \to \N$ defines the *parity winning condition*.
    The game is played between two players, player $0$ and player $1$.
    When the game is in a position $p \in \Pos_i$ then it is player $i$'s turn -- i.e. player $i$ may choose
    the next vertex to transition form the current node, along the transition
    relation $E$.
    Each game results in a (possible infinite) sequence of positions, called plays: $p_0, p_1, p_2,...$.
    A play is finite if a player is unable to make a move. In that case that player loses.
    For an infinite play, we look at the sequence of parities of the vertices in the play
    -- i.e. $\Omega(p_0), \Omega(p_1), ...$.
    Player $0$ wins iff the least parity that occurs infinitely often is even, otherwise player $1$ wins.

From a tableau, $\mathcal T$, we now define a parity game $\mathcal G(\mathcal T)$.
In this game, player $0$ may be thought of as trying to prove the satisfiablity of the pattern,
and player $1$ as trying to prove it unsatisfiable.

Each position in the game is a pair $(a, v)$ where $a$ is an assertion.
If $v = \unsat$, then $a$ is of the form $\matches{x}{\bot}$.
If $\Gamma = \emptyset$, then $a$ is of the form $\matches{x}{\top}$.
Otherwise, $a \in \Gamma$.

If $v_1$ is a child of $v_0$
there is an edge from $(a_0, v_0)$ to $(a_1, v_1)$ in $E$ with if:

* $v_1$ is constructed by some rule that does not modify the assertion $a_0$
  and $a_0 = a_1$, or
* $v_1$ is constructed by some rule that modifies the assertion $a_0 \in \Gamma$
  and $a_1$ is a newly created assertion, or
* $a_0 = a_1$ is an assertion $\Universals(v_1)$, or
* $v_1$ is constructed by an application of one of the (conflict-*) rules
  and $a_1$ is $\matches{x}{\bot}$ where $x$ is the element variable of the assertion $a_0$, or
* $v_1$ is constructed by an application of one of the (ok-*) rules,
  $a_0$ is removed from $\Gamma$ by the rule, and $a_1$ is $\matches{e}{\top}$ where $e$ is the element marker of the assertion $a_0$.

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
  2. $v$ has $\Gamma = \emptyset$.

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

In the next sections we prove some important theorems:

Theorem

:   If a guarded pattern has a tableau with a pre-model, then it is satisfiable.


Theorem

:   If a guarded pattern has a tableau with a refutation, then it is unsatisfiable.

\newpage

# Soundness & Completeness

Below, we define concepts that will be used later for proving the
soundness and completeness of the procedure.

Definition (Approximations)

:   For any ordinal $\tau$ and pattern $\alpha$, we define two new patterns:
    $\mu^\tau X\ldotp \alpha(X)$ and
    $\nu^\tau X\ldotp \alpha(X)$, with the following semantics:

    * $\evaluation{\mu^0 X\ldotp \alpha(X)}_{M,\rho} = \emptyset$
    * $\evaluation{\nu^0 X\ldotp \alpha(X)}_{M,\rho} = M$
    * $\evaluation{\kappa^{\tau + 1} X\ldotp \alpha(X)}_{M,\rho}
      = \evaluation{\alpha(X)}_{M,\rho[{\kappa^{\tau + 1} X\ldotp \alpha(X)}/X]}$
      where $\kappa$ is either $\mu$ or $\nu$.

    Then we have
    $\evaluation{\mu X\ldotp \alpha(X)}_{M,\rho} = \Union_{\tau'} \evaluation{\mu^0 X\ldotp \alpha(X)}_{M,\rho}$
    and $\evaluation{\nu X\ldotp \alpha(X)}_{M,\rho} = \Intersection_{\tau'} \evaluation{\mu^0 X\ldotp \alpha(X)}_{M,\rho}$.
    TODO: We need to prove this.

    We extend the notion of definition lists by allowing mappings of the form
    $D \mapsto \mu^\tau X \ldotp \alpha$
    and
    $D \mapsto \nu^\tau X \ldotp \alpha$.

Definition ($\mu$-measure -- $\umeasure$)

:   For an assertion $\alpha = \matches{e}{\phi}$, a dependency order $\deflist$,
    a model $M$ and valuation $\rho$ such that $\rho{e} \in \evaluation{alpha}_{M,\rho}$.

    Let $U_{k_1}, U_{k_2}, \ldots, U_{k_n}$ be the $\mu$-constants occuring in $\deflist$.
    We define the *$\mu$-measure* of $\alpha$ in $M$ for $\rho$ (or just *measure* for short), $\umeasure(\alpha)_{M,\rho}$
    to be the least tuple $(\tau_1,\ldots,\tau_n)$
    such that $\rho(e) \in \evaluation{alpha}_{M,\rho}$
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
$e \in \evaluation{\phi}$, then for any tableau $\mathcal T$, the game
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
      Then if $\rho_p(c_0) \in \evaluation{\sigma(e_1,\ldots,e_n)}_{\rho_p}$
      we select the left child position, $l$,
      (that has $\matches{c_0}{\sigma(e_1,\ldots,e_n)} \in \Basic$).
      Otherwise, we select the right child position, $r$,
      (that has $\matches{c_0}{\bar\sigma(\lnot e_1,\ldots,\lnot e_n)} \in \Basic$).
      We define $\rho_l = \rho_r = \rho_p$.

    * If the (or) rule was applied to assertion $\matches{e}{\psi_1 \lor \psi_2}$
      we select the child with $\matches{e}{\psi_1}$
      if $\umeasure(\matches{e}{\psi_1}) \le \umeasure(\matches{e}{\psi_2})$.
      Otherwise, we select the child with $\matches{e}{\psi_2}$.

    * Suppose the (app) rule was applied to assertion $\matches{c}{\sigma(\phi_1,\ldots,\phi_n)}$.
      We know that $\rho_p(c) \in \evaluation{\sigma(\phi_1,\ldots,\phi_n)}_{M,\rho_p}$.
      Therefore there must be some $m_1,\ldots,m_n \in M$
      such that $m_i \in \evaluation{\phi_i}_{M,\rho_p}$.

      Select a child of $p$,\newline
      say $p' = \sequent{\matches{e}{\sigma(\bar k)} \land \matches{k_i}{\phi_i}; \Basic'; \Universals'; \Elements'}$,
      such that:
      * $\Elements' := \{ k_1,\ldots,k_n \} \union \{ e \} \union \Union_i \free{\phi_i}$, and
      * if for some $i$, $m_i = \rho_p(e)$ where $e \in \Elements$ then $k'_i = e$.
      * if $m_i = m_j$, then $k_i = k_j$.

      Define: $\rho_{p'} = \begin{cases}e   \mapsto \rho_p(e) & \text{when $e \in \Elements$} \\
                                        k_i \mapsto  m'_i \\ \end{cases}$

    * Suppose the (exists) rule was applied to assertion
      $\matches{c}{\exists \bar x \ldotp \phi}$.
      We know that $\rho_p(c) \in \evaluation{\exists \bar x \ldotp \phi}_{M,\rho_p}$.
      Therefore there must be some $m_1,\ldots,m_n \in M$
      such that $\rho_p(c) \in \evaluation{\phi}_{M,\rho_p[\bar m/\bar x]}$
      with measure $\tau$.

      Select a child of $p$,\newline
      say $p' = \sequent{\matches{e}{\phi[\bar k/\bar x]}; \Basic'; \Universals'; \Elements'}$,
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
    If it is a (nu), (\dapp), or (forall), then player $1$ wins.
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

:   Suppose, $\rho(m) \not\in \evaluation{\phi}_{M,\rho}$.
    Then $\rho(m) \in \evaluation{\lnot\phi}_{M,\rho}$
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
    $\rho(c) \in \evaluation{\alpha}_{M(S),\rho}$ and $\Intersection_{x\in\{c\}\bar x}\rho(x) \neq \emptyset$
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
      we define a evaluation $\rho_p$ such that $\rho_p(e) \not\in \evaluation{\phi}_{M,\rho_p}$.
    * The $\nu$-measure at each position is decreasing.

    The root of the play is $(\matches{e}{\psi}, v = \sequent{\matches{e}{\phi}; ...; \{e\};})$.
    By our assumptions, $\vmeasure(\psi)$ is defined.
    We define $\rho_p(e)$ to be the $e$-equivalence defined by the root node.

    Consider a paritally constructed play until position $p = (\matches{e}{\phi}, s)$:

    * (conflict)/(ok): $\phi$ cannot be a basic application or an element variable
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

        Since $\rho_p(e) \not\in \evaluation{\phi}_{M,\rho_p}$
        we know that there is some extension $\rho'$ to $\rho_p$ such that
        $\rho'(e) \in \alpha(\bar x, \bar y) \land \lnot \phi(\bar x, \bar y)$
        and by Lemma \ref{lemma:vmeasure} that $\nu$-measure
        of the corresponding assertion is not larger than the current $\nu$-measure.

        By Lemma \ref{lemma:guards}, there is a position $w \in \Intersection_{x\in\{c\}\bar x\union\bar y}\rho'(x)$.
        If $v = w$ then we choose the corresponding instantiation.
        If $v \neq w$ then choose the child the $v$ on the path to $w$.

    * (\dapp): Similar to (forall).
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
\name{conflict}                 & \vruleun{ \Basic, ... \proves \alpha \limplies \bot }
                                          { \valid } \\
                                & \text{when $\alpha$ is a basic assertion, with its negation  in $\Basic$.}
\\
\name{conflict-el}              & \vruleun{ \Basic, ... \proves \vmatches{e}{e'} }
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
\name{\dapp} &
    \vruleun{ \vmatches{e}{\bar\sigma(\bar \phi)} }
            { \mathrm{inst} \union \Gamma; 
              \vmatches{e}{\bar\sigma(\bar \phi)} } \\
  & \text{where $\mathrm{inst} = \left\{ \vmatches{e}{\sigma(\bar c)} \limplies \lOr_i \vmatches{c_i}{\phi_i}
                                    \mid \text{ if } \bar c \subset \Elements \right\}$} \\
  & \text{and $\matches{e}{\bar \sigma(\bar \phi)}$ is not a basic assertion.}
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
             {\{ \alpha \leadsto \sequent{ \Gamma;\Basic; \Universals; \Elements }\}}
    \qquad  \text{for each $\alpha \in \Gamma$}
   \\ 
\name{app} &
  \satruleun { \matches{e}{\sigma(\bar \phi)} \leadsto \sequent{ \Gamma; \Basic; \Elements } }
             { \{ \sequent{ \matches{e}{\sigma(\bar k)} \land \lAnd_i \matches{k_i}{\phi_i}, \Gamma' \union \Universals'; \Basic' ; \{ \} ; \Elements'  } \} } \\
  & \text{for each $\bar k \subset K$} \\
  & \text{where} \\
  & \text{\qquad $\Elements' = \bar k \union \{ e \} \union  \free{\bar \phi}$} \\
  & \text{\qquad $\Basic' = \{ a \mid a \in \Basic \text{ and } \free{a} \subset \Elements' \}$ \quad($\Basic$ restricted to $\Elements'$)} \\
  & \text{\qquad $\Gamma' = \{ \gamma \mid \gamma \in \Gamma \text{ and } \free{\gamma} \subset \Elements' \}$ \quad($\Gamma$ restricted to $\Elements'$)} \\
  & \text{\qquad $\Universals' = \{ \alpha \mid \alpha \in \Universals \text{ and } \free{\gamma} \subset \Elements' \}$ \quad($\Universals$ restricted to $\Elements'$)} \\
\\
\name{exists} &
  \satruleun { \matches{e}{\exists \bar x \ldotp \phi(\bar x)} \leadsto \sequent{ \Gamma; \Basic; \Universals; \Elements } }
             { \{ \sequent{ \alpha, \Gamma' \union \Universals'; \Basic' ;  \{ \}; \Elements' } \}
             } \\
  & \text{for each $\alpha \in \{ \matches{e}{\phi[\bar k/\bar x]} \mid \bar k \subset K \}$} \\
  & \text{where} \\
  & \text{\qquad $\Elements'   = \free{\alpha}$} \\
  & \text{\qquad $\Basic'      = \{ a \mid a \in \Basic \text{ and } \free{a} \subset \Elements' \}$ \quad($\Basic$ restricted to $\Elements'$)} \\
  & \text{\qquad $\Gamma'      = \{ \gamma \mid \gamma \in \Gamma \text{ and } \free{\gamma} \subset \Elements' \}$ \quad($\Gamma$ restricted to $\Elements'$)} \\
  & \text{\qquad $\Universals' = \{ \alpha \mid \alpha \in \Universals \text{ and } \free{\alpha} \subset \Elements' \}$ \quad($\Universals$ restricted to $\Elements'$)} \\
\\
\cline{1-3}
\intertext{This rule must apply only immediately after the (exists)/(app) rules or on the root node.
$\mathsf{fresh}$ denotes the fresh variables introduced by the last application of either of those rules.}
\name{resolve} & \satrulebin{\sequent{\Gamma; \Basic; \Universals; \Elements}}
                            {\sequent{ \Gamma; \matches{e}{\sigma(\bar f)}, \Basic; \Universals; \Elements}}
                            {\sequent{ \Gamma; \matches{e}{\lnot\sigma(\bar f)}, \Basic; \Universals; \Elements}} \\
               & \text{when $\{e\}\union \bar f \subset \Elements$ and $(\{e\}\union \bar f)\intersection \mathsf{fresh} \neq \emptyset$.}
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


3. Misc

    * The parity game looks like an extension of binary decision trees or BDDs
      (depending on how you look at it).
      This may be a  useful source of optimizations. 

---

