---
geometry: margin=2cm
header-includes: |
    \usepackage{xcolor}

    \renewcommand{\phi}{\varphi}

    \newcommand{\N}{\mathbb N}

    \newcommand{\limplies}{\rightarrow}
    \newcommand{\lOr}{\bigvee}
    \newcommand{\lAnd}{\bigwedge}

    \renewcommand{\subset}{\subseteq}
    \newcommand{\union}{\mathrel{\cup}}
    \newcommand{\intersection}{\mathrel{\cap}}

    \newcommand{\denotation}[1]{\left\lVert #1 \right\rVert}
    \newcommand{\free} {\mathrm{free}}

    \newcommand{\matches}[2]{\mathsf{matches}(#1, #2)}
    \newcommand{\sequent}[1]{\left\langle #1 \right\rangle}
    \newcommand{\unsat}{\mathsf{unsat}}
    \newcommand{\Atoms}{\mathrm{Atoms}}
    \newcommand{\Universals}{\mathrm{Universals}}
    \newcommand{\Elements}{\mathrm{Elements}}
    \newcommand{\signature}[1]{\mathsf{Sig}(#1)}

    \newcommand{\deflist}{\mathcal D}

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

    \newcommand {\mkDeflist}[1]{\mathsf{deflist}(#1)}
    \newcommand {\combineDefList}{\circ}
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

:   A definition list, $\deflist$, of a pattern $\phi$ is an ordered list assigning set variables,
    called definition constants, to fixed point patterns.

    NOTE: We assume no free element variables in fixed point patterns.

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

    The label of the root node is $\sequent{e \in \phi, \{\}, \{e\}}$ for some fresh variable $e$ drawn from $K$.
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

## Soundness

Lemma

:   Given a tableau there is a pre-model or a refutation, but not both.

Lemma (Satisfiable patterns have pre-models)

:   Given a pattern $\phi$ and an element $e$ in $M$ such that $e \in \denotation{\phi}$,
    there is a tableau $\mathcal T$ and game $\mathcal G(\mathcal T)$
    with a pre-model.

Proof

:   First, we will construct a tableau,
    and then show that the game for that tableau has a winning strategy.

    While constructing the tableau, we will
    associate each constant $c$
    in nodes $n$ needed for the winning strategy
    with an element in model through a function $\rho_n$.
    We will build a set $W$ that are needed by the winning strategy.

    The root node of the tableau is $\mathrm{root} = \sequent{\matches{c}{\phi}; \{\}; \{c\}}$.
    Define $\rho_\mathrm{root} := c \mapsto e$. Let $\mathrm{root} \in W$.

    Consider an incomplete node $n$ in $W$;

    * Suppose there is some tuple of constants $\bar c \subset C$ such that
      neither $\matches(c_0,       \sigma(c_1,\ldots,c_n))$
      nor     $\matches(c_0, \lnot \sigma(c_1,\ldots,c_n))$
      are in  $\Atoms$, then we use the (resolve) rule to construct its children.

      Suppose $\rho_n(c_0) \in \denotation{\sigma(c_1,\ldots,c_n)}_{M,\rho_n}$
      then we place the left child of (resolve) in $W$,
      otherwise we place the right child of (resolve) in $W$.

    * Otherwise, if $\matches{e}{\phi\lor\psi} \in \alpha$,
      then we construct child nodes $l$ and $r$ using the (or) rule.
      If $\signature{\matches{e}{\phi}, n}\le\signature{\matches{e}{\psi}, n}$
      we place $l$ in $W$. If not, we place $r$ in $W$.

    * 

    * In all other cases, it is player $1$'s turn.
      We choose any arbitary rule and place all children in $W$.

   For incomplete nodes *not* in $W$,
   we first apply (resolve) repeatedly until all possible atomic assertions
   or their negations are in $\Atoms$ and then build the tableau arbitarily.
   Since there is a rule matching any pattern we will be able to complete
   the tableau (possibly after infinite applications).

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

