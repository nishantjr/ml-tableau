---
xgeometry: margin=2cm
header-includes: |
    \usepackage{xcolor}

    \renewcommand{\phi}{\varphi}

    \newcommand{\N}{\mathbb N}

    \newcommand{\limplies}{\rightarrow}
    \newcommand{\lOr}{\bigvee}
    \newcommand{\lAnd}{\bigwedge}

    \renewcommand{\subset}{\subseteq}
    \newcommand{\union}{\mathrel{\cup}}
    \newcommand{\Union}{\bigcup}
    \newcommand{\intersection}{\mathrel{\cap}}
    \newcommand{\Intersection}{\bigcap}

    \newcommand{\denotation}[1]{\left\lVert #1 \right\rVert}
    \newcommand{\free} {\mathrm{free}}

    \newcommand{\matches}[2]{\mathsf{matches}(#1, #2)}
    \newcommand{\sequent}[1]{\left\langle #1 \right\rangle}
    \newcommand{\unsat}{\mathsf{unsat}}
    \newcommand{\Atoms}{\mathrm{Atoms}}
    \newcommand{\Universals}{\mathrm{Universals}}
    \newcommand{\Elements}{\mathrm{Elements}}
    \newcommand{\signature}[1]{\mathsf{Sig}(#1)}

    \newcommand{\name}[1]{(\text{#1})\quad}

    \newcommand{\pruleun}[2]{\frac{#1}{#2}}
    \newcommand{\prulebin}[3]{\frac{#1}{#2\quad#3}}

    \newcommand{\satruleun}[2]
        {{\color{green}\pruleun{\color{black}#1}{\color{black}#2}}}
    \newcommand{\satrulebin}[3]
        {{\color{green}\prulebin{\color{black}#1}{\color{black}#2}{\color{black}#3}}}

    \newcommand{\unsatruleun}[2]
        {{\color{blue}\pruleun{\color{black}#1}{\color{black}#2}}}
    \newcommand{\unsatrulebin}[3]
        {{\color{blue}\prulebin{\color{black}#1}{\color{black}#2}{\color{black}#3}}}

    \newcommand{\Pos}{\mathrm{Pos}}

    \newcommand{\inst}{\mathsf{inst}}

    \newcommand{\deflist}{\mathcal D}
    \newcommand{\mkDeflist}[1]{\mathsf{deflist}(#1)}
    \newcommand{\combineDefList}{\circ}
    \newcommand{\expand}[1]{\langle\mid #1 \mid \rangle}
    \newcommand{\Sig}{\mathsf{Sig}}
---

## Positive-form patterns

Definition (Positive Form Pattern)
: Positive form patterns are defined using the syntax:

\begin{alignat*}{3}
\phi := \quad&       \sigma(\phi_1, \ldots, \phi_n)
   &\quad\mid\quad&   \bar \sigma(\phi_1, \ldots, \phi_n) \\
    \quad\mid\quad&  \phi_1 \land \phi_2
   &\quad\mid\quad&  \phi_1 \lor  \phi_2 \\
    \quad\mid\quad&  \exists x \ldotp \phi
   &\quad\mid\quad&  \forall x \ldotp \phi \\
    \quad\mid\quad&  \mu X \ldotp \phi
   &\quad\mid\quad&  \nu X \ldotp \phi
\end{alignat*}

where $$\bar \sigma(\phi_1, \ldots, \phi_n) \equiv \lnot\sigma(\lnot \phi_1, \ldots, \lnot\phi_n)$$

## Definition List

Definition (Definition List)

:   A definition list, $\deflist$, of a pattern $\phi$ is an ordered list assigning
    special constants, called definition constants, to fixed point patterns.

    We allow the use of definitional constants whereever set variables are allowed.

    TODO: We assume no free element variables in fixed point patterns.

    Given a pattern $\phi$, a definition list is constructed as follows:

    \begin{align*}
    \mkDeflist{D} &= \emptyset \qquad \text{where $D$ is a definition constant.} \\
    \mkDeflist{\sigma(\phi_1,\ldots,\phi_n)} = \mkDeflist{\bar\sigma(\phi_1,\ldots,\phi_n)} &= \mkDeflist{\phi_1}\combineDefList\cdots\combineDefList\mkDeflist{\phi_n} \\
    \mkDeflist{\phi_1\lor\phi_2}  = \mkDeflist{\phi_1\land\phi_2)} &= \mkDeflist{\phi_1}\combineDefList\mkDeflist{\phi_2} \\
    \mkDeflist{\exists \bar x \ldotp\phi}  = \mkDeflist{\forall \bar x \ldotp \phi)} &= \mkDeflist{\phi} \\
    \mkDeflist{\mu X \ldotp\phi}  &= (D \mapsto \mu X . \phi[U/X]) \combineDefList \mkDeflist{\phi} \text{ where $\phi$ has no free element variables.}\\
    \mkDeflist{\nu X \ldotp\phi}  &= (D \mapsto \nu X . \phi[U/X]) \combineDefList \mkDeflist{\phi} \text{ where $\phi$ has no free element variables.}\\
    \end{align*}
    \begin{align*}
                         \deflist_1 \combineDefList \cdot                           &= \deflist_1 \\
    (D_1 \mapsto \phi)   \deflist_1 \combineDefList (D_2 \mapsto \phi)   \deflist_2 &= (D_1 \mapsto \phi) \deflist_1 \combineDefList \deflist_2[D_1/D_2] \\
                         \deflist_1 \combineDefList (D_2 \mapsto \phi)   \deflist_2 &= \deflist_1 (D_2 \mapsto \phi) \combineDefList \deflist_2 \qquad\text{otherwise.}\\
    \end{align*}

    We define the semantics of patterns with definition constants in terms
    of an expansion operator:
    $$\expand{\phi}_\deflist = \phi[\alpha_n/D_n]\ldots[\alpha_1/D_q]$$
    where $\deflist = (D_1 \mapsto \alpha_1)\cdots (D_n \mapsto \alpha_n)$.

## Tableau

Definition (Assertion)
:   An *assertion* is either:

    1.  a pair of an element variable and a pattern, denoted $\matches{e}{\phi}$,
    2.  a conjunction of assertions: $\alpha_1 \land a_2$
    2.  a disjunction of assertions: $\alpha_1 \lor \alpha_2$

Assertions allow us to capture that a particular element in the model
represented by the first argument $e$ is in the denotation of $\phi$.

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
    2. $\alpha \leadsto \mathrm{sequent}$ where $\alpha$ is an assertion.
    3. $\unsat$

Informally,
$\Gamma$ represents the set of assertions we'd like to hold in the current tableau node,
$\Atoms$ represents the paritally built interpretations for symbols in the model,
and $\Elements$ are a subset of elements in the model.
We implicitly assume that all element in $\Elements$ have distinct interpretations
in the model.

Definition (Tableau)

:   For a signature $\Sigma$, and a guarded  pattern $\phi$,
    let $\deflist$ be its definition list,
    and $K$ be a set of distinct element variables.

    a tableau is a (possibly infinte) tree
    with nodes labeled by sequents
    and built using the application of the rules below.

    The label of the root node is $\sequent{\matches{e}{\phi}, \{\}, \{\}, \{e\}}$ for some fresh variable $e$ drawn from $K$.
    Leaf nodes must be labeled either 
       with $\unsat$
    or with a sequent where $\Gamma$ contains only universal assertions
    i.e. assertions of the form $\matches{e}{\forall \bar x\ldotp \phi}$
    or $\matches{e}{\bar\sigma(\bar\phi)}$.

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
\\
\name{or}                       & \satrulebin{\sequent{  \matches{e}{\phi \lor \psi}, \Gamma; ... }}
                                              {\sequent{ \matches{e}{\phi}, \Gamma; ... }}
                                              {\sequent{ \matches{e}{\psi},  \Gamma; ... }}
\\
\name{def}                      & \pruleun{\sequent{ \matches{e}{\kappa X . \phi(X)}, \Gamma; ...}}
                                  {\sequent{ \matches{e}{D}, \Gamma; ...}} \\
                                & \text{when $D := \kappa X. \phi(X) \in \deflist$ }
\\
\name{unfold}                   & \pruleun{\sequent{ \matches{e}{D}, \Gamma; ... }}
                                          {\sequent{ \matches{e}{\phi[D/X]}, \Gamma;... }} \\
                                & \text{when $D := \kappa X. \phi \in \deflist$ }
\\
\name{dapp} &
\unsatruleun{\sequent{ \matches{e}{\bar\sigma(\bar \phi)}, \Gamma; \Universals; \Elements; ...}}
            { \sequent{ \mathrm{inst} \union \Gamma; 
               \matches{e}{\bar\sigma(\bar \phi)}, \Universals; \Elements; ... } } \\
  & \text{where $\mathrm{inst} = \left\{ \matches{e}{\sigma(\bar c)} \limplies \lOr_i \matches{c_i}{\alpha_i}
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
             {\alpha \leadsto \sequent{ \Gamma;\Atoms; \Universals; C }}
    \qquad  \text{where $\alpha \in \Gamma$}
   \\ 
\name{app} &
  \satruleun { \matches{e}{\sigma(\bar \phi)} \leadsto \sequent{ \Gamma; \Atoms; C } }
             { \{ \sequent{ \matches{e}{\sigma(\bar k)} \land \matches{k_i}{\phi_i} \text{ for each } i, \Gamma'; C' } \} } \\
  & \text{where} \\
  & \text{\qquad $\bar k \subset \free(\bar \phi) \union \{e\} \union K \setminus C$} \\
  & \text{\qquad $C'     = \bar k \union \free(\bar \phi)$} \\
  & \text{\qquad $A' = \{ a \mid a \in A \text{ and } \free(a) \subset C' \}$ \quad($A$ restricted to $C'$)} \\
  & \text{\qquad $\Gamma' = \{ \gamma \mid \gamma \in \Gamma \text{ and } \free(\gamma) \subset C' \}$ \quad($\Gamma$ restricted to $C'$)} \\
\\
\name{exists} &
  \satruleun { \matches{e}{\exists \bar x \ldotp \phi(\bar x)} \leadsto \sequent{ \Gamma; A; C } }
             { \{ \sequent{ \alpha, \Gamma'; A' ; C' } \}
             } \\
  & \text{where} \\
  & \text{\qquad $\alpha \in \{ \matches{e}{\phi[\bar k/\bar x]} \mid \bar k \subset \free(\exists \bar x \ldotp \phi(\bar x)) \union \{e\} \union K \setminus C\}$} \\
  & \text{\qquad $C'     = \free(\alpha)$} \\
  & \text{\qquad $A' = \{ a \mid a \in A \text{ and } \free(a) \subset C' \}$ \quad($A$ restricted to $C'$)} \\
  & \text{\qquad $\Gamma' = \{ \gamma \mid \gamma \in \Gamma \text{ and } \free(\gamma) \subset C' \}$ \quad($\Gamma$ restricted to $C'$)} \\
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

## Games

A parity game is a tuple $(\Pos_0, \Pos_1, E, \Omega)$
where $\Pos = \Pos_0 \union \Pos_1$ is a possibly infinite set of positions;
$E : \Pos \times \Pos$ is a transition relation;
and $\Omega : \Pos \to \N$ is parity winning condition.

The game is played between two player, player $0$ and player $1$.
When the game is in a position $p \in \Pos_i$ then it is player $i$'s turn -- i.e. player $i$ may choose
the next vertex to transition form the current node, along the transition
relation $E$.
Each "game" results in a (possible infinite) sequence of vertices, called plays: $p_0, p_1, p_2,...$.
A play is finite iff one player is unable to make a move. In that case that player __wins__.
For an infinite play, we look at the sequence of parities of the vertices in the play
-- i.e. $\Omega(p_0), \Omega(p_1), \ldots$.
Player $0$ wins iff the least parity that occurs infinitely often is even, otherwise player $1$ wins.


From the tableau, $\mathcal T$, as above we may define a parity game $\mathcal G(\mathcal T)$, as follows.
Each position in the game is a pair $(a, v)$ where $a$ is an assertion
in the label of a vertex $v$ in the tableau.

* A position $p = (a, v)$ is in $\Pos_0$ if:
  1.  $v$'s children were built using (or), (app), or (exists) rules
      and $a$ was the assertion matched on by that rule; or
  2.  $v$'s children were built using (resolve), or (unify) rules; or
  3.  $v = \top$
* A position $p = (a, v)$ is in $\Pos_1$ if:
  1. $v$'s children were built using (and), (dapp), or (forall) rules;
  2. $\bot$ is in $\Pos_1$;
* All other positions do not offer a choice, and so are arbitrarily assigned to $\Pos_1$.

There is an edge from $(a_0, v_0)$ to $(a_1, v_1)$ in $E$ iff either:

* $v_1$ is a child of $v_0$ constructed by some rule that matches on the assertion $a_0$
  and $a_1$ is the newly created assertion.
* $v_1$ is a child of $v_0$ constructed by some rule that does not match on the assertion $a_0$
  and $a_0 = a_1$.

The parity condition $\Omega$ is defined as follows:

* $\Omega((e \in D_i, v))                       = 2 \times i$     if $D_i$ is a $\mu$ constant with index $i$ in $\mathcal D$.
* $\Omega((e \in D_i, v))                       = 2 \times i + 1$ if $D_i$ is a $\nu$ constant with index $i$ in $\mathcal D$.
* $\Omega((e \in \exists \bar x\ldotp \phi, v)) = 2 \times n + 1$ where $n$ is the length of $\mathcal D$.
* $\Omega(a, v)                                 = 2 \times n + 2$ otherwise.

## Strategies

For a $\mathcal G(\mathcal T) = (\Pos_0, \Pos_1, E, \Omega)$,
a winning strategy for a player $i$ is a subgraph $(\Pos'_i, S_i)$ such that:

1. If a node $p$ is in $\Pos_i$ and there are outward edges from $p$
   then there is exactly one edge outward edge from $p$ in $S_i$ and $p \in \Pos'_i$.
2. If a node $p$ is not in $\Pos_i$ then all outward edges from $p$ in $E$ are in $S_i$ and $p \in \Pos'_i$.
3. Player $i$ wins from every position in $\Pos'_i$

We call a winning strategy for player $0$ a pre-model,
and a winning strategy for player $1$ a refutation.

## Approximations & Signatures

In this section, we define concepts that will be used later for proving the
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

Definition (Signatures)

:   TODO: We need to rename this to avoid confusion with $\Sigma$.

    Fix an assertion $\alpha = \matches{e}{\phi}$, a definition list $\deflist$,
    a model $M$ and valuation $\rho$ such that $\rho{e} \in \denotation{\expand{alpha}_\deflist}_{M,\rho}$.

    Let $U_{k_1}, U_{k_2}, \ldots, U_{k_n}$ be the $\mu$-constants occuring in $\deflist$.
    We define the signature of $\alpha$ in $M$ for $\rho$, $\Sig(\alpha)_{M,\rho}$
    to be the least tuple $(\tau_1,\ldots,\tau_n)$
    such that $\rho(e) \in \denotation{\expand{alpha}_{\deflist'}}_{M,\rho}$
    where $\deflist'$ is obtained by replacing each $\mu$-constant $(U_{k_i} \mapsto \mu X\ldotp \alpha_{k_i}(X))$
    with $(U_{k_i} \mapsto \mu^{\tau_i} X\ldotp \alpha_{k_i}(X))$.

## Soundness

Lemma

:   Given a tableau there is a pre-model or a refutation, but not both.

Lemma (Satisfiable patterns have pre-models)

: Given a pattern $\phi$ and an element $m$ in $M$ such that
$e \in \denotation{\phi}$, then for any tableau $\mathcal T$, the game
$\mathcal G(\mathcal T)$ contains a pre-model.

Proof

:   We will build a pre-model for the game by associating each constant in each
    position $p$ in the constructed strategy with an element in the model
    through a function $\rho_p$, while maintaining the invariant that under this
    interpretation the atoms in the sequent are satisfied. We will then show
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
      if $\Sig(\matches{e}{\expand{\psi_1}_\deflist}) \le \Sig(\matches{e}{\expand{\psi_2}_\deflist})$.
      Otherwise, we select the child with $\matches{e}{\psi_2}$.

    * Suppose the (app) rule was applied to assertion $\matches{c}{\sigma(\phi_1,\ldots,\phi_n)}$.
      We know that $\rho_p(c) \in \denotation{\expand{\sigma(\phi_1,\ldots,\phi_n)}}_{M,\rho_p}$.
      Therefore there must be some $m_1,\ldots,m_n \in M$
      such that $m_i \in \denotation{\expand{\phi_i}_{M,\rho_p}}$.

      --- TODO: Complete me.

      Define a set of fresh constants .
      such for each $m_i$ that does not appear in $p$'s elements.
      If $m_i = m_j$ use the same constant for both.
      For each $m_i$ such that $m_i \neq \rho_p(e_j)$ for some $e_j$ in $p$'s elements,
      define a new constant $c'_i$.

      Choose a child that corres

      Define $$\rho_{p'} = \begin{cases}
                              e \mapsto \rho_p(e) & \text{where $e$ is free in some $\phi_i$} \\
                              c'_i \mapsto m_i
      \end{cases}$$

<!--

    * If $\matches{e}{\phi\lor\psi} \in \Gamma$,
      then we construct child nodes $l$ and $r$ using the (or) rule.
      If $\signature{\matches{e}{\phi}, n}\le\signature{\matches{e}{\psi}, n}$
      we place $l$ in $W$. If not, we place $r$ in $W$.

    * If the sequent is of the form $\matches{e}{\alpha} \leadsto \sequent{...}$
      we apply the (app)
      or (exists) rule and 

    * In all other cases, it is player $1$'s turn.
      We choose any arbitary rule and place all children in $W$.

   For incomplete nodes *not* in $W$,
   we first apply (resolve) repeatedly until all possible atomic assertions
   or their negations are in $\Atoms$ and then build the tableau arbitarily.
   Since there is a rule matching any pattern we will be able to complete
   the tableau (possibly after infinite applications).
-->

Lemma

:   For a pattern $\phi$, given a pre-model we may build a satisfying model.


Lemma

:  The existance of a refutation implies $\lnot \phi$ is valid.

## Termination

\newpage

## Pseudocode

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

