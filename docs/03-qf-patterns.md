# The Quantifier-Free Fragment {#sec:qf-fragment}

The quantifier free fragment is less restrictive, allowing fixedpoints in patterns as well:

Definition (Quantifier-Free Patterns)

:   The *quantifier-free patterns* of matching logic has:

    \begin{align*}
    \PP &= \left\{\begin{array}{l}\text{ patterns built from \structure{}, } \\
                \text{\logic{} and \fixedpoint{}}
                  \end{array}\right\}\\
    \TT &= \{\emptyset\}
    \end{align*}

This fragment also exhibits the small-model property as proved in [@sec:decidable-qf-fragment].

In this section, we prove that quantifier-free fragment is decidable and has
the small model property.
We do this by reducing the satisfiability problem to a solving a "parity game" (a decidable problem).
Given a pattern, the parity game is built from a "tableau".
The tableau is a possibly infinite tree constructed using a set of syntax driven rules.
Although the tree itself is infinite,
its labels range over a finite set of labels that repeat along infinite paths in a "regular" way
and so has a finite representation.

In both this section and the next,
we define our procedure over "positive-form" patterns
-- patterns where negations are pushed down as far as they can go using
De Morgan's and related equivalences.

Definition (Positive-Form Patterns)
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

We allow negation of element variables, but not set variables.
This ensures that set variables may only occur positively in their binding fixedpoint.
While positive form patterns allow existentials and universals,
in the fragment under consideration in this section we do not allow them.
 
By definition, we have:

\begin{lemma}
Every pattern is equivalent to some positive-form pattern.
\end{lemma}

From now on, we only consider positive-form patterns and simply call them 
patterns.

## Defintion lists and dependency orders

Definition (Definition Lists)

:   For a quantifier-free pattern $\phi$, a *definition list*
    (denoted $\deflist^\phi$ or just $\deflist$ when $\phi$ is understood)
    is a mapping from each occurring set variable to the pattern by which it is bound.
    Since we assume well-named patterns, each set variable is bound by a unique
    fixedpoint pattern and such a mapping is well-defined.
    We use $\deflist^\phi(X)$ to denote the fixedpoint sub-pattern corresponding to the set variable $X$.

Definition (Fixedpoint Markers)

:   For a variable $X \in \dom(\deflist^\phi)$,
    $\deflist^\phi_X$ (or just $\deflist_X$ when $\phi$ is understood)
    is a *fixedpoint marker*.
    We call a marker a $\mu$-marker if $\deflist^\phi(X)$ is a $\mu$ pattern
    and a $\nu$-marker otherwise.
    We extend the syntax of patterns to allow fixedpoint markers. These markers may
    be used whereever set variables may be used -- in particular, they may not
    appear negated in positive-form patterns. We define the evaluation of fixedpoint
    makers as the evaluation of their corresponding fixedpoint pattern:
    $$\evaluation{\deflist^\phi_X}^\deflist_{M,\rho} = \evaluation{\deflist^\phi(X)}_{M,\rho}$$

Since the evaluation of a pattern now also depends on its dependency list,
we make the dependency list used explicit by adding it as a superscript as in $\evaluation{\phi}^\deflist_{M,\rho}$.

\begin{figure*}
\footnotesize
$$\def\arraystretch{2.5}\begin{array}{rlrl}
\prule{conflict}
& \pruleun{\sigma,\bar\sigma,\Gamma}
  { \unsat }
\\
\prule{and} 
& \pruleun{\phi_1 \wedge \phi_2,\Gamma}
                {\phi_1,\phi_2,\Gamma}
&\prule{or}
& \prulebin{\phi_1 \vee \phi_2, \Gamma}
                 {\phi_1,\Gamma}
                 {\phi_2,\Gamma}
\\
\prule{unfold}
&
\multicolumn{3}{l} {
 \pruleun{U, \Gamma}
                {\phi[U/X], \Gamma}
\where{$(\deflist_U = \kappa X \ldotp \phi)$ \\
         and $\kappa \in \{\mu,\nu\}$}
} \\
\prule{mu}
& \pruleun{\mu X \ldotp \phi, \Gamma}{U,\Gamma}
\where{ $(\deflist_U = \mu X \ldotp \phi)$}

&\prule{nu}
&  \pruleun{\nu X \ldotp \phi, \Gamma}{U,\Gamma}
\where{$(\deflist_U = \nu X \ldotp \phi)$}
\\
\appa
& \multicolumn{3}{l} {
\pruleun {\Gamma}
                 {\left\{ \sigma(\phi_1,\dots,\phi_n) \leadsto \Gamma_{\bar\sigma}
                  \mid \sigma(\phi_1,\dots,\phi_n) \in \Gamma
                  \right\} }
                 {
                 \where{
                    $\Gamma$ contains only
                    $\sigma$-patterns, and $\bar\sigma$-patterns.
                    (In other words, only if all other rules cannot be applied.)
                 }
                 }
}
\\
\appb
&
\pruleun{\sigma(\phi_1,\dots,\phi_n) \leadsto \Gamma }
        {\left\{ \sigma(\phi_1,\dots,\phi_n) \leadsto \wit \leadsto \Gamma \mid \wit \in 
         \Wit(\Gamma,\sigma) \right\}}
\\
\appc
& \pruleun{\sigma(\phi_1,\dots,\phi_n) \leadsto \wit \leadsto \Gamma}
{\left\{ \phi_i, \Gamma^\wit_i \mid i \in \{1,\dots,n\} \right\}}
\end{array}$$
\caption{Tableau rules for the quantifier-free fragment.}
\label{fig:qf-tableau}
\end{figure*}


Definition (Depends On)

:   For two fixedpoint markers $\deflist^\phi_X$ and $\deflist^\phi_Y$,
    we say $\deflist^\phi_X$ *depends on* $\deflist^\phi_Y$
    if $\deflist^\phi(Y)$ is a sub-pattern of $\deflist^\phi(X)$.

The transitive closure of this relation is a pre-order -- i.e. it is reflexive and transitive.
It is also antisymmetric -- for a pair of distinct markers $\deflist^\phi_X$ and $\deflist^\phi_Y$
we may have either $\deflist^\phi_X$ transitively depends on $\deflist^\phi_Y$
or $\deflist^\phi_Y$ transitively depends on $\deflist^\phi_X$ but not both.
So, it is also a partial order.

Definition (Dependency Orders)

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

## Tableau Construction


\begin{definition}
Let $\Gamma$ be a set of patterns.
We define $\Gamma_\sigma$ (resp. $\Gamma_{\bar\sigma}$) to be the set of 
$\sigma$-patterns 
(resp. $\bar\sigma$-patterns) in $\Gamma$.
Formally,
\begin{align*}
\Gamma_\sigma &= \{ 
\sigma(\phi_1,\dots,\phi_n) \mid \sigma(\phi_1,\dots,\phi_n) \in 
\Gamma \} \\
\Gamma_{\bar\sigma} &= \{ 
\bar\sigma(\phi_1,\dots,\phi_n) \mid \bar\sigma(\phi_1,\dots,\phi_n) \in 
\Gamma \}
\end{align*}
\end{definition}

\begin{definition}
Given $\Gamma$ and any non-constant symbol $\sigma$ of arity $n \ge 1$,
we define
a \emph{witness function} $\wit \colon \Gamma_{\bar\sigma} \to \{1,\dots,n\}$
as a function that maps every pattern of the form 
$\bar\sigma(\psi_1,\dots,\psi_n) 
\in \Gamma$ with a number between $1$ and $n$, called the \emph{witness}.
Let $\Wit(\Gamma,\sigma) = [\Gamma_{\bar\sigma} \to \{1,\dots,n\}]$ denote the set 
of all witness functions with respect to $\Gamma$ and $\sigma$.
Let $\Gamma^\wit_i = \{\psi_i \mid \bar\sigma(\psi_1,\dots,\psi_n) \in \Gamma 
\text{ and } \wit(\bar\sigma(\psi_1,\dots,\psi_n)) = i \}$.
\end{definition}

\begin{remark}
When $\Gamma_{\bar\sigma} = \emptyset$, we assume there is a unique witness 
function denoted $\wit_\emptyset$, whose domain is empty. 
This is mainly for technical convenience. 
\end{remark}

We use $\size{A}$ to denote the cardinality of any set $A$.

\begin{remark}
Suppose $\sigma$ has arity $n$ and $\size{\Gamma_{\bar\sigma}} = m$  is finite.
Then $\size{\Wit(\Gamma,\sigma)} = n^m$.
In particular, if $\sigma$ is a unary symbol, i.e., $n = 1$, then 
$\size{\Wit(\Gamma,\sigma)} = 1$. 
\end{remark}


Definition
:   A \emph{tableau sequent} is one of the following:

    1.  a finite nonempty pattern set $\Gamma$;
    2.  $\Gamma \leadsto \sigma(\phi_1,\dots,\phi_n)$, where 
        $\sigma(\phi_1,\dots,\phi_n) \in \Gamma$;
    3.  $\Gamma \leadsto \wit \leadsto \sigma(\phi_1,\dots,\phi_n)$, where
        $\sigma(\phi_1,\dots,\phi_n) \in \Gamma$
        and $\wit \in \Wit(\Gamma,\sigma)$.
    4. $\unsat$

Definition (Tableaux)
:   \label{def:tableau}
    Fix a definition list $\deflist$ for $\psi$.
    A *tableau* for $\psi$ is a possibly infinite labeled tree
    $(T,L)$.
    We denote its nodes as $\Nodes(T)$ and the root node is $\rt(T)$.
    The labeling function $L \colon \Nodes \to \mathsf{Sequents}$
    associates every node of $T$ with a sequent, such that the following conditions 
    are satisfied:

    1.  $L(\rt(T)) = \{ \psi \}$;
    3.  For every $s \in \Nodes(T)$, if one of the tableau rules in $\SSS$ can be applied (with respect to the 
        definition list $\deflist^\psi$), and the resulting sequents are  
        $\seq_1,\dots,\seq_k$, then
        $s$ has exactly $k$ child nodes $s_1,\dots,s_k$, and 
        $L(s_1) = \seq_1$, \dots, $L(s_k) = \seq_k$. 

In (3), we categorize the nodes by the corresponding tableau rules that are 
applied. 
For example, if the two child nodes of $s$ is obtained by applying \prule{or},
then we call $n$ an \prule{or} node. 

\begin{remark}
For any tableau $(T,L)$ and an \appa{} node $s \in \Nodes(T)$,
its child nodes (if there are any) must be \appb{} nodes, 
whose child nodes must be \appc{} nodes.
\appb{} and \appc{} nodes must have at least one child nodes,
i.e., they are not leaf nodes. 
\end{remark}

\begin{remark}
For any tableau $(T,L)$, the leaves of $T$
are either labeled with inconsistent sequents, or they are
\appa{} nodes whose labels contain no $\sigma$-patterns for any 
$\sigma$.
For any non-leaf node, unless it is labeled with \prule{or} or \prule{app$_i$} 
for $i \in \{1,2,3\}$,
it has exactly one child node. 
\end{remark}

## Parity games

Now that we know how to construct a tableau for a quantifier-free pattern,
we can derive a parity game from it.

Definition (Parity Games)

:   A *parity game* is a tuple $(\Pos_0, \Pos_1, E, \Omega)$
    where $\Pos = \Pos_0 \disjointunion \Pos_1$ is a possibly infinite set of positions;
    Each $\Pos_i$ is called the *winning set* for player $i$.
    $E : \Pos \times \Pos$ is a transition relation;
    and $\Omega : \Pos \to \N$ defines the *parity winning condition*
    mapping each position to a natural number below some finite bound.
 
The game is played between two players, player $0$ and player $1$.
When the game is in a position $p \in \Pos_i$ then it is player $i$'s turn -- i.e. player $i$ may choose
the next node to transition to form the current node, along the transition relation $E$.

Definition (Plays)
:   Each game results in a (possible infinite) sequence of positions, called plays: $p_0, p_1, p_2,...$.
    A play is finite if a player is unable to make a move. In that case that player loses.
    For an infinite play, we look at the sequence of parities of the vertices in the play
    -- i.e. $\Omega(p_0), \Omega(p_1), ...$.
    Player $0$ wins iff the least parity that occurs infinitely often is even, otherwise player $1$ wins.

Definition

:   For a $(\Pos_0, \Pos_1, E, \Omega)$,
    a *strategy* from a position $q$ for a player $i$ is a subtree $(P \subset \Pos, S \subset E)$ such that:

    1. $q \in P$
    2. If a node $p \in P \intersection \Pos_i$
       then there is *exactly* one edge outward edge $(p, p')$ in $S$ and $p' \in P$.
    3. If a node $p \not\in \Pos_i$ and $p \in P$ then all outward edges from $p$ in $E$ are in $S_i$ and $p \in W_i$.

    A strategy is *winning* for a player $i$ if Player $i$ wins on every trace.

\todo{ (cite: Infinite games on finitely coloured graphs with applicatiosn to automata on infinite trees)}
\todo{ (cite: Tree automata, mu-calculus and determinacy) }

\todo{define memoryless strategy}


In the case of the particular parity game we define for quantifier-free patterns,
one may think of player $0$ as trying to search for a model and player $1$
as trying to show that there cannot be a model.

Definition

:   Let $\mathcal T = (T, L)$ be a tableau for a quantifier-free pattern $\psi$.
    Below, we define a parity game $\game = (\PosT_0, \PosT_1, \ET, \OmegaT)$.
    The positions are the set of pairs from $\Pattern \times (\{\sat\} \union \Sequent)$.
    The positions and edge relation are inductively defined as below:

    * there is a position $p = (\psi, \rt(T))$ corresponding to the root sequent.
    * If $p = (\phi, s)$ is a position, and $s'$ is a child of $s$ in $T$
        * if $s$ is not \appc{} node, then
            * there is a positon $p' = (\phi, s')$ with $(p, p') \in E$
              if the rule does not reduce $\phi$;
            * for each $\phi'$ in the set of reductions of $\phi$ in $s'$
              there is a positon $p' = (\phi', s')$ with $(p, p') \in E$.
        * if $s$ is an \appc{} node with $s = \sigma(\phi_1,\ldots,\phi_n) \leadsto \wit \leadsto \Gamma$, then
            * if $\phi = \sigma(\phi_1,\ldots,\phi_n)$
              then there is a position $p' = (\phi_i, s')$  with $(p, p') \in E$
            * if $\phi = \bar\sigma(\chi_1,\ldots,\chi_n)$
              and $\wit(\phi) = i$
              then there is a position $p' = (\phi_i, s')$  with $(p, p') \in E$
        * if a position has no children as defined by the above rules
          then there is a position $p' = (\phi, \sat)$  with $(p, p') \in E$ .
          (this is the case when a $\bar\sigma-$pattern is dropped by all children of a \appa{} node
          or when $\appc$ is applied to a nullary $\sigma$ pattern)

    These positions are partitioned into $\Pos_0$ and $\Pos_1$ as follows:

    *   A position $p = (\phi, s)$ is in $\Pos_0$ if either:
        * $s$ is an (or)- or \appb{}-node $\phi$ and $\phi$ was transformed by the rule
        * $s = \unsat{}$
    *   A position $p = (\phi, s)$ is in $\Pos_1$ if either:
        * $s$ is an (and)-, \appa{}-, or \appc{}-node $\phi$ and $\phi$ was transformed by the rule
        * $s = \sat{}$
    *  All other positions offer no choice---they have exactly one outward edge.
       We arbitarily assign this to $\Pos_1$.

    We define the parity condition $\Omega$:

    * $\Omega((\nu X\ldotp \phi, s)) = 2i$     if $\deflist_X$ is $i$th in the dependency order
    * $\Omega((\mu X\ldotp \phi, s)) = 2i + 1$ if $\deflist_X$ is $i$th in the dependency order
    * $\Omega((\phi, s))             = 2N + 2$ if where $N$ is the size of $\deflist$

By this definition, all leaf positions are either $\sat{}$ or $\unsat{}$.

Definition (Pre-models & Refutations)

:   We call a winning strategy for player $0$ a pre-model,
    and a winning strategy for player $1$ a refutation.

Any play consistent with a pre-model must terminate with $\sat{}$ if finite.
An infinite play must have an even number as lowest parity---i.e. the priority corresponding to some $\nu$ fixedpoint marker.
Any play consistent with a winning strategies for player $1$ terminate with $\unsat{}$ if finite.
An infinite play must have an odd number as lowest parity---i.e. the priority corresponding to some $\mu$ fixedpoint marker.

We show that for any quantifier-free sentence $\psi$, it is satisfied in a 
model (i.e., its interpretation is nonempty) iff a pre-model exists for $\psi$.
In the interest of space we only give an informal overview of the proof here,
and refer the reader to the [Appendix @sec:qf-proofs] for the proofs in their
entirety.

Our first objective is to prove that if there is a satisfying model, then
every tableau for $\psi$ contains a pre-model as a sub-tree.

\begin{proposition}
\label{prop:mpm}
If a quantifier-free sentence $\psi$ is satisfied in $M$ on $a$, then
any tableau for $\psi$ contains a pre-model for $\psi$ as a sub-tree. 
\end{proposition}

We do this by constructing a strategy for player $0$ while maintaining the
invariant that the patterns labeling each position reachable using the strategy
are satisfied by some element in the model.
We show that this strategy is winning for player $0$, i.e. a pre-model.
This is done by showing the every move taken must either reduces the size of the patterns in the sequent
or a measure called the $\umeasure$, corresponding roughly to the minimum number of unfoldings of $\mu$ patterns needed to satisfy a pattern in the model,
unless the move is unfolding a $\nu$-pattern.

Next, we show that if we have a pre-model for some quantifier-free pattern,
then that pattern must be satisfiable.

\begin{proposition}\label{prop:pmm}
If there exists a pre-model for a positive-from quantifier-free sentence $\psi$
then $\psi$ is satisfiable in the corresponding canonical model. 
\end{proposition}

In this case we construct a model, called the cannonical model, from the pre-model.
We then assume that the model does not satisfy the pattern, by way of contradiction,
and show that there must be a $\mu$-play in the strategy if this model does
not satisfy the pattern.

\begin{theorem}\label{thm:pm}
For any positive-form quantifier-free sentence $\psi$, there exists a pre-model for $\psi$ 
iff $\psi$ is satisfiable.
\end{theorem}
\begin{proof}
By Propositions \ref{prop:mpm} and \ref{prop:pmm}. 
\end{proof}

\begin{theorem}
For any positive-form quantifier-free sentence $\psi$, determining whether $\psi$ is 
satisfiable is decidable.
\end{theorem}
\begin{proof}
\todo{Check details.}
By Theorem \ref{thm:pm}, we can look for a pre-model for $\psi$.
We will construct a tree automaton $\Aut$ on infinite trees that accepts 
exactly the pre-models for $\psi$.
Then by the Emerson-Jutla theorem, it is decidable to determine whether the 
language accepted by $\Aut$ is empty. 

$\Aut$ is constructed in two steps. Firstly, we define an \emph{outer automaton}
$\Aut_o$ that accepts the quasi-models, which are essentially the \emph{regular 
trees} generated by the set of tableau rules $\SSSmod$.
Secondly, we define an \emph{inner automaton} $\Aut_i$ that is a B\"uchi 
automaton on infinite words that accepts the $\mu$-traces.
Then, we combine the two automatons using the Safra deterministic construction
and obtain a tree automaton that accepts precisely the pre-models for $\psi$.
\end{proof}

\todo{talk about refutations}
