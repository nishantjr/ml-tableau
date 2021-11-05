---
geometry: margin=2cm
header-includes: |
    \usepackage{xcolor}

    \renewcommand{\phi}{\varphi}

    \newcommand{\N}{\mathbb N}

    \newcommand{\lOr}{\bigvee}
    \newcommand{\lAnd}{\bigwedge}

    \renewcommand{\subset}{\subseteq}
    \newcommand{\union}{\cup}
    \newcommand{\intersection}{\cap}

    \newcommand{\free} {\mathrm{free}}

    \newcommand{\sequent}[1]{\left\langle #1 \right\rangle}
    \newcommand{\deflist}{\mathcal D}
    \newcommand{\name}[1]{(\text{#1})\quad}

    \newcommand{\pruleun}[2]{\frac{#1}{#2}}
    \newcommand{\prulebin}[3]{\frac{#1}{#2\qquad#3}}

    \newcommand{\satruleun}[2]
        {\color{green}\pruleun{\color{black}#1}{\color{black}#2}}
    \newcommand{\satrulebin}[3]
        {\color{green}\prulebin{\color{black}#1}{\color{black}#2}{\color{black}#3}}

    \newcommand{\unsatruleun}[2]
        {\color{blue}\pruleun{\color{black}#1}{\color{black}#2}}
    \newcommand{\unsatrulebin}[3]
        {\color{blue}\prulebin{\color{black}#1}{\color{black}#2}{\color{black}#3}}

    \newcommand{\Pos}{\mathrm{Pos}}
---

## Definition List

...

## Tableau

An *assertion* is:

1.  a pair of a set variable and a pattern, denoted $e \in \phi$.
2.  a disjunction of assertions: $a_1 \lor a_2$

*Atomic assertions* are assertions of the form:

1.  $e \in \sigma(\bar a)$,
2.  $e \not\in \sigma(\bar a)$,
3.  $e \in e'$ (This is not used. It is here just for symmetry),
4.  $e \not\in e'$.

A *sequent* is:

1. a tuple, $\sequent{\Gamma; A; C}$,
   where $\Gamma$ is a set of assertions,
          $A$ is a set of atomic assertions
             where $e$, $e'$, are $\bar a$ element variables.
       and $C$ is a set of element variables.
2. $\bot$
3. $\top$

Given signature $\Sigma$, definition list $\deflist$ and guarded pattern $\phi$,
a tableau is a (possibly infinte) tree
with nodes labeled by sequents
and built using the application of the rules below.
The label of the root node is $\sequent{e \in \phi, \{e\}}$ for some fresh variable $e$.

\begin{align*}
\cline{1-3}
\intertext{The (unsat) rule has highest priority.}
\name{unsat} &
    \pruleun{\sequent{\alpha, \Gamma; A; ...}}
            { \bot } &
    \text{when $\alpha$ is an atomic assertion \emph{not} in $A$.}
\\
\cline{1-3}
\intertext{Next, any of the following rules may apply}
%
\name{and} &
    \pruleun{\sequent{ e \in \alpha \land \beta,   \Gamma; ...}}
            {\sequent{ e \in \alpha, e \in \beta,  \Gamma; ...}}
\\
\name{or}  &
 \satrulebin{\sequent{ e \in \alpha \lor \beta, \Gamma; ... }}
             {\sequent{ e \in \alpha, \Gamma; ... }}
             {\sequent{ e \in \beta,  \Gamma; ... }}
\\
\name{def} &
    \pruleun{\sequent{ e \in \kappa X . \alpha(X), \Gamma; ...}}
            {\sequent{ D, \Gamma; ...}} &
    \text{when $D := \kappa X. \alpha(X) \in \deflist$ }
\\
\name{unfold} &
    \pruleun{\sequent{ e \in D, \Gamma; ... }}
            {\sequent{ e \in \alpha(D), \Gamma;... }} & \text{when $D := \kappa X. \alpha(X) \in \deflist$ }
\\
\name{dapp} &
\unsatruleun{\sequent{e \in \bar\sigma(\bar \alpha), \Gamma; ...}}
            { \sequent{ \mathrm{instantiations}
               \union e \in \bar\sigma(\bar \alpha), \Gamma; ... } }
  & \text{where $\mathrm{instantiations} = \{ \lOr_i c_i \in \alpha_i \mid$ if $(e \in \sigma(\bar c) \in \Gamma \}$} \\
 && \text{and $e \in \bar \sigma(\bar \alpha)$ is not an atomic assertion.}
\\
\name{forall} &
\unsatruleun { \sequent{ e \in \forall \bar x \ldotp \phi(\bar x), \Gamma; ... } }
             { \sequent{ \mathrm{instantiations}
               \union e \in \forall \bar x \ldotp \phi, \Gamma; ... } }
  & \text{where $\mathrm{instantiations} = \{ e \in \phi[\bar c / \bar x] \mid c \subset C \}$}
\\
\cline{1-3}
\intertext{The following rules may only apply when none of the above rules apply.}
\name{app} &
  \satruleun { \sequent{ e \in \sigma(\bar \phi), \Gamma; C } }
             { \{ \sequent{ e \in \sigma(\bar k), k_i \in \phi_i \text{ foreach } i, \Gamma'; C' } \} }
  & \text{where $\bar k$ is a set of distinct fresh variables}\\
 && \text{ and $\Gamma' = \{ \gamma \mid \gamma \in \Gamma \text{ and } \free(\gamma) \subset \{e\} \union \free(\exists \bar x \ldotp \phi(\bar x)) \}$} \\
 && \text{ and $e \in \sigma(\bar \alpha)$ is not an atomic assertion.}
\\
\name{exists} &
  \satruleun { \sequent{ e \in \exists \bar x \ldotp \phi(\bar x), \Gamma; C } }
             { \{ \sequent{  \phi[\bar k / \bar x], \Gamma'; C' } \} }
  & \text{where $\bar k$ is a set of distinct fresh variables}\\
 && \text{ and $\Gamma' = \{ \gamma \mid \gamma \in \Gamma \text{ and } \free(\gamma) \subset \{e\} \union \free(\exists \bar x \ldotp \phi(\bar x)) \}$}
\\
\cline{1-3}
\intertext{This following rules must apply only immediately after the (exists)/(app) rules.
$\mathrm{fresh}$ denotes the fresh variables introduced by the last application of those rules.}
\name{resolve} &
 \satrulebin{\sequent{\Gamma; A; C}}
          {\sequent{ \Gamma; e \in \sigma(\bar a), A; C}}
          {\sequent{ \Gamma; e \not\in \sigma(\bar a), A; C}} &
   \text{when $\{e\}\union \bar a \subset C$ and $(\{e\}\union \bar a)\intersection \mathrm{fresh} \neq \emptyset$.}
\\
\name{unify} &
 \satrulebin{\sequent{\Gamma; A ; C}}
          {\sequent{ \Gamma[d/c]; A; C \setminus \{ c \}}}
          {\sequent{ \Gamma; c \not\in d , A ; C }} &
   \text{when $\{c, d\} \subset C$ and $d \in \mathrm{fresh}$.}
\\
\cline{1-3}
\intertext{The (sat) rule has lowest priority and may only apply when none of
the rules from the first three sections apply -- i.e. when only atomic patterns
remain, and (unsat) does not apply.
}
\name{sat} &
    \pruleun{\sequent{\Gamma; C}}
            {\top} &
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

**Lemma 1**: For every tableau, $\mathcal G(\mathcal T)$, must have either a pre-model or a refutation but not both.

**Lemma 2a**: The existance of a pre-model  implies the existance of a satisfying model for that pattern.
**Lemma 2b**: For any satisfiable guarded pattern there exists tableau a pre-model.

**Lemma 3**: The existance of a refutation implies $\lnot \phi$ is valid.

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

