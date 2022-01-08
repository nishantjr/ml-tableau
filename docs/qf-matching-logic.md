# Quantifier-free fragment

The quantifier free fragment is less restrictive, allowing fixedpoints in patterns as well:

Definition (The quantifier-free fragment)

:   The *quantifier-free fragment* of matching logic has:

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

We allow negation of element variables, but not set variables.
This ensures that set variables may only occur positively in their binding fixedpoint.
While positive form patterns allow existentials and universals,
in the fragment under consideration in this section we do not allow them.
 
By definition, we have:

\begin{lemma}
Every pattern is equivalent to some positive guarded pattern.
\end{lemma}

From now on, we only consider positive guarded patterns and simply call them 
patterns.

## Defintion lists and dependency orders

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
    $$\evaluation{\deflist^\phi_X}^\deflist_{M,\rho} = \evaluation{\deflist^\phi(X)}_{M,\rho}$$

    Since the evaluation of a pattern now also depends on its dependency list,
    we make the dependency list used explicit by adding it as a superscript as in $\evaluation{\phi}^\deflist_{M,\rho}$.

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

Definition (Tableau sequent)
:   A \emph{tableau sequent} is one of the following:

    1.  a finite nonempty pattern set $\Gamma$;
    2.  $\Gamma \leadsto \sigma(\phi_1,\dots,\phi_n)$, where 
        $\sigma(\phi_1,\dots,\phi_n) \in \Gamma$;
    3.  $\Gamma \leadsto \sigma(\phi_1,\dots,\phi_n) \leadsto \wit$, where
        $\sigma(\phi_1,\dots,\phi_n) \in \Gamma$
        and $\wit \in \Wit(\Gamma,\sigma)$.

    We call (1) a \emph{normal sequent} and (2) and (3) \emph{ghost sequents}. 

Definition  (Normal sequent)
:   For a normal sequent $\Gamma$,
    we say $\Gamma$ is an \emph{inconsistent sequent}
    if for some constant $\sigma$, both $\sigma$ and $\bar\sigma$ are in $\Gamma$.
    If a normal sequent is not inconsistent, then it is a consistent sequent. 

Definition (Tableau)
:   \label{def:tableau}
    Let $\deflist$ be a definition list.
    We define the set $\SSS$ of \emph{tableau rules} with respect to 
    $\deflist$ in [@fig:qf-tableau], where $\Gamma$ is a finite nonempty set of sentences and 
    $\phi,\phi_1,\phi_2$ are sentences, whose definition constants are 
    all contained in $\deflist$.

    A \emph{tableau} for $\psi$ is a possibly infinite labeled tree
    $(T,L)$, where $T$ is a tree whose set of nodes is $\Nodes(T)$ and nodes are 
    denoted $s,s_1,s_2,\dots$, 
    and the root node is $\rt(T)$.
    The labeling function $L \colon \Nodes \to \mathit{Sequents}$
    associates every node of $T$ with a sequent, such that the following conditions 
    are satisfied:
    \begin{enumerate}
    \item $L(\rt(T)) = \{ \psi \}$;
    \item For every $s \in \Nodes(T)$, if $L(s)$ is an inconsistent sequent then 
    $s$ is a leaf of $T$;
    \item For every $s \in \Nodes(T)$, if $L(s)$ is not an inconsistent sequent 
    and one of the tableau rules in $\SSS$ can be applied (with respect to the 
    definition list $\deflist = \contr{\psi}$), and the resulting sequents are  
    $\seq_1,\dots,\seq_k$, then
    $s$ has exactly $k$ child nodes $s_1,\dots,s_k$, and 
    $L(s_1) = \seq_1$, \dots, $L(s_k) = \seq_k$. 
    \end{enumerate}

\begin{figure*}
$$\def\arraystretch{2.5}\begin{array}{|rlrl|}
\name{and} 
&\qquad \pruleun{\phi_1 \wedge \phi_2,\Gamma}
                {\phi_1,\phi_2,\Gamma}
\qquad\qquad\qquad\qquad\qquad\qquad
&\name{or}
&\qquad \prulebin{\phi_1 \vee \phi_2, \Gamma}
                 {\phi_1,\Gamma}
                 {\phi_2,\Gamma}
\\
\name{unfold}
&
\multicolumn{3}{l} {
\qquad \pruleun{U, \Gamma}
                {\phi[U/X], \Gamma}
\where{$(\deflist_U = \kappa X \ldotp \phi)$ \\
         and $\kappa \in \{\mu,\nu\}$}
} \\
\name{mu}
&\qquad \pruleun{\mu X \ldotp \phi, \Gamma}{U,\Gamma}
\where{ $(\deflist_U = \mu X \ldotp \phi)$}
\qquad
&\name{nu}
& \qquad \pruleun{\nu X \ldotp \phi, \Gamma}{U,\Gamma}
\where{$(\deflist_U = \nu X \ldotp \phi)$}
\\
\name{choose-app}
& \multicolumn{3}{l} {\qquad
\pruleun {\Gamma}
                 {\left\{ \sigma(\phi_1,\dots,\phi_n) \leadsto \Gamma 
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
\name{app$_2$}
&\qquad
\pruleun{\sigma(\phi_1,\dots,\phi_n) \leadsto \Gamma }
        {\left\{ \sigma(\phi_1,\dots,\phi_n) \leadsto \Gamma \leadsto \wit \mid \wit \in 
         \Wit(\Gamma,\sigma) \right\}}
\\
\name{app$_3$}
&\qquad \pruleun{\sigma(\phi_1,\dots,\phi_n) \leadsto \Gamma \leadsto \wit}
{\left\{ \phi_i, \Gamma^\wit_i \mid i \in \{1,\dots,n\} \right\}}
\end{array}$$
\caption{Tableau rules for the quantifier-free fragment.}
\label{fig:qf-tableau}
\end{figure*}


In (3), we categorize the nodes by the corresponding tableau rules that are 
applied. 
For example, if the two child nodes of $s$ is obtained by applying \prule{or},
then we call $s$ an \prule{or} node, or that $n$ is labeled with \prule{or}. 
We also categorize the nodes by their labeling  sequents.
If a node is labeled with a normal sequent, we call it a normal node. 
Otherwise, it is labeled with a ghost sequent and we call it a ghost node.
Note that a node is a ghost node iff it is an \appb{} or \appc{} node. 
In either case, its closest ancestor normal node is an \appa{} node.

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
First, we will define a parity game.
A parity game is played between two player, player $0$ and player $1$,
on a (possibly infinite) tree, with some nodes belonging to player $0$ and
the rest to player $1$. Each node is assigned a parity---a natural number below some bound.
The game begins at the root of the tree.
If the game is at a node belonging to a player
that player may take their turn by moving the game to some child node.
If the the node is a leaf, the player loses.
Infinite plays are decided by the least parity that occurs infinitely often.
If it is even, then player $0$ wins, otherwise player $1$ wins.

Definition (Parity game)

:   A *parity game* is a tuple $(\Pos_0, \Pos_1, E, \Omega)$
    where $\Pos = \Pos_0 \disjointunion \Pos_1$ is a possibly infinite set of positions;
    Each $\Pos_i$ is called the *winning set* for player $i$.
    $E : \Pos \times \Pos$ is a transition relation;
    and $\Omega : \Pos \to \N$ defines the *parity winning condition*
    mapping each position to a natural number below some finite bound.
    The game is played between two players, player $0$ and player $1$.
    When the game is in a position $p \in \Pos_i$ then it is player $i$'s turn -- i.e. player $i$ may choose
    the next vertex to transition form the current node, along the transition
    relation $E$.
    Each game results in a (possible infinite) sequence of positions, called plays: $p_0, p_1, p_2,...$.
    A play is finite if a player is unable to make a move. In that case that player loses.
    For an infinite play, we look at the sequence of parities of the vertices in the play
    -- i.e. $\Omega(p_0), \Omega(p_1), ...$.
    Player $0$ wins iff the least parity that occurs infinitely often is even, otherwise player $1$ wins.

\todo{ (cite: Infinite games on finitely coloured graphs with applicatiosn to automata on infinite trees)}
\todo{ (cite: Tree automata, mu-calculus and determinacy) }

In the case of the particular parity game we define for quantifier-free patterns,
one may think of player $0$ as trying to search for a model and player $1$
as trying to show that there cannot be a model.

Definition

:   Let $\psi$ be a sentence and $(T,L)$ be a tableau for $\psi$.
    The root node of the game is labeled by $\psi$

    * If $\Tr(s)$ is defined on $s \in \Nodes(T)$, and 
        * if $s$ is a normal node then $\Tr(s) \in L(s)$; 
        * if $s$ is a ghost node, then let $s'$ be the closest ancestor normal node 
          of $n$ and define $\Tr(s) = \Tr(s')$; 
    * $\Tr(\rt(T))$ is defined, and by (1), $\Tr(\rt(T)) = \psi$;
    * If $\Tr(s)$ is defined on $s \in \Nodes(T)$ 
      and $s'$ is the next node of $s$ in $P$
      that is a normal node and is obtained \emph{not} by applying \appc, and 
        * if the rule does not reduce $\Tr(s)$, then we define $\Tr(s') = \Tr(s)$;
        * if the rule reduces $\Tr(s)$, then we let $\Tr(s')$ be one of the results 
          of the reduction, nondeterministically. Note that the nondeterministic choice 
          only occurs when $s$ is an \prule{and} node,
          $L(s) = \{\phi_1 \wedge \phi_2\} \cup \Gamma$, 
          $T(s) = \phi_1 \wedge \phi_2$, and
          $L(s') = \{\phi_1,\phi_2\} \cup \Gamma$.
          In this case, $T(s')$ is $\phi_1$ or $\phi_2$, nondeterministically.
---

\begin{definition}
Let $\psi$ be a sentence and $(T,L)$ be a tableau for $\psi$.
Given a rooted maximal (possibly infinite) path $P$ of $T$, 
a \emph{trace} on $P$ is a partial function $\Tr \colon P \pto \Pattern$
whose domain $\dom(\Tr)$ is a prefix of $P$, such that the following conditions 
are satisfied:
\begin{enumerate}
\item If $\Tr(s)$ is defined on $s \in \Nodes(T)$, and 
\begin{enumerate}
\item if $s$ is a normal node then $\Tr(s) \in L(s)$; 
\item if $s$ is a ghost node, then let $s'$ be the closest ancestor normal node 
of $n$ and define $\Tr(s) = \Tr(s')$; 
\end{enumerate}
\item $\Tr(\rt(T))$ is defined, and by (1), $\Tr(\rt(T)) = \psi$;
\item If $\Tr(s)$ is defined on $s \in \Nodes(T)$ 
and $s'$ is the next node of $s$ in $P$
that is a normal node and is obtained \emph{not} by applying \appc, and 
\begin{enumerate}
\item if the rule does not reduce $\Tr(s)$, then we define $\Tr(s') = \Tr(s)$;
\item if the rule reduces $\Tr(s)$, then we let $\Tr(s')$ be one of the results 
of the reduction, nondeterministically. Note that the nondeterministic choice 
only occurs when $s$ is an \prule{and} node,
$L(s) = \{\phi_1 \wedge \phi_2\} \cup \Gamma$, 
$T(s) = \phi_1 \wedge \phi_2$, and
$L(s') = \{\phi_1,\phi_2\} \cup \Gamma$.
In this case, $T(s')$ is $\phi_1$ or $\phi_2$, nondeterministically.
\end{enumerate}
\item If $\Tr(s)$ is defined on $s \in \Nodes(T)$ whose label
$L(s) = \Gamma \leadsto \sigma(\phi_1,\dots,\phi_n) \leadsto \wit$,
and $s'$ is the next node of $s$ in $P$ obtained by applying \appc,
and $L(s') = \{\phi_i\} \cup \Gamma^\wit_i$ for some $i \in 
\{1,\dots,n\}$, and 
\begin{enumerate}
\item if $\Tr(s) = \sigma(\phi_1,\dots,\phi_n)$, then $\Tr(s') = 
\phi_i$;
\item if $\Tr(s) = \bar\sigma(\psi_1,\dots,\psi_n)$ and $\psi_i \in 
\Gamma^\wit_i$, then $\Tr(s') = \psi_i$;
\item $\Tr(s')$ is undefined for any other cases. 
\end{enumerate}
\end{enumerate}
\end{definition}


--------------------------------------------------------------------------------

\begin{definition}
We say a definition constant $U$ \emph{regenerates}  on $\Tr$ if
exists a node $s$ such that $\Tr(s) = U$ and 
$\Tr(s') = \kappa X \ldotp \phi[U/X]$,
where $s'$ is the next node of $n$ on $\Tr$ and
$(U = \kappa X . \phi) \in \deflist$.
We say $\Tr$ is a $\kappa$-trace for $\kappa \in \{\mu,\nu\}$, if it is 
infinite and the oldest definition constant (with respect to $\deflist$) that 
regenerates infinitely often is a $\kappa$-constant. 
\end{definition}

\begin{lemma}
Any infinite trace is either a $\mu$-trace or a $\nu$-trace. 
\end{lemma}
\begin{proof}
The conclusion only holds for positive guarded patterns. 
\end{proof}

\begin{definition}
A quasi-model is called a \emph{pre-model} iff any infinite trace on any path 
if a $\nu$-trace.
\end{definition}

\subsection{Equivalence between Pre-Models and Models}

We show that for any positive guarded sentence $\psi$, it is satisfied in a 
model (i.e., its interpretation is nonempty) iff there exists a pre-model for 
$\psi$.

\begin{definition}
We extend the pattern syntax with two new constructs
$\mu^\alpha X \ldotp \phi$ and $\nu^\alpha X \ldotp \phi$, where $\alpha$ is an 
ordinal. 
We define their semantics in $M$ under the valuation $\rho$ by transfinite 
induction as follows:
\begin{align*}
\evaluation{\mu^0 X \ldotp \phi} &= \emptyset
\\
\evaluation{\mu^{\alpha+1} X \ldotp \phi} &= \wbar{\rho[\evaluation{\mu^\alpha X \ldotp 
\phi} / X]}(\phi)
\\
\evaluation{\mu^\lambda X \ldotp \phi} &= \bigcup_{\alpha < \lambda} 
\evaluation{\mu^\alpha X \ldotp \phi}
\quad\text{for $\lambda$ limit ordinal} \\
\evaluation{\nu^0 X \ldotp \phi} &= M
\\
\evaluation{\nu^{\alpha+1} X \ldotp \phi} &= \wbar{\rho[\evaluation{\nu^\alpha X \ldotp 
\phi} / X]}(\phi)
\\
\evaluation{\nu^\lambda X \ldotp \phi} &= \bigcap_{\alpha < \lambda} 
\evaluation{\nu^\alpha X \ldotp \phi}
\quad\text{for $\lambda$ limit ordinal}
\end{align*}
\end{definition}

\begin{lemma}
$
\evaluation{\mu X \ldotp \phi} = \bigcup_{\alpha} \evaluation{\mu^\alpha X \ldotp \phi}$
and $
\evaluation{\nu X \ldotp \phi} = \bigcap_{\alpha} \evaluation{\nu^\alpha X \ldotp \phi}
$.
\end{lemma}

Let us extend the notion of definition lists given in 
Definition~\ref{def:deflist} by allowing equations of the form
$U = \kappa^\alpha X \ldotp \phi$ for $\kappa \in \{\mu,\nu\}$. 
Let us extend the expansion operator $\expan{\phi}_\deflist$ accordingly.

\begin{definition}\label{def:osig}
Let $\psi$ be a sentence, $\deflist$ be a definition list containing all definition 
constants in $\psi$, $M$ be a 
model, and $a$ be an element of $M$.
Let $U_{k_1},\dots,U_{k_d}$ be the list of $\mu$-constants in $\deflist$,
ordered from the oldest to the youngest.
If for some (irrelevant) valuation $\rho$ we have
$a \in \evaluation{\expan{\psi}_\deflist}$, then 
we define the \emph{signature ordinal sequence}, or simply the \emph{signature} 
of $\psi$ in $a$, written
$\SigD(\psi,a)$, as the least (in the lexicographical ordering) sequence of 
ordinals $(\alpha_1,\dots,\alpha_d)$ such that
$a \in \evaluation{\expan{\psi}_{\deflist'}}$, where $\deflist'$ is obtained from $\deflist$ by 
replacing all equations of the form $U_{k_i} = \mu X \ldotp \phi_{k_i}$ for $i 
\in \{1,\dots,d\}$ with $U_{k_i} = \mu^{\alpha_i} X \ldotp \phi_{k_i}$.
\end{definition} 

\begin{lemma}
$\SigD(\psi,a)$ as given in Definition~\ref{def:osig} is well-defined. 
\end{lemma}
\begin{proof}
Let us assume the notations given in Definition~\ref{def:osig}.
Note that finite sequences of ordinals are well-founded. 
Therefore, we only need to show that there exists a sequence
$(\alpha_1,\dots,\alpha_n)$ such that $a \in \evaluation{\expan{\psi}_{\deflist'}}$. 
The proof is standard and can be carried out by induction on $n$ and the 
structural induction 
on $\psi$. 
\end{proof}

Note that $\SigD(\psi,a)$ is defined when $a \in \evaluation{\psi}$.
For technical convenience, we define $\SigD(\psi,a) = \infty$ when $a \not\in 
\evaluation{\psi}$ and assume $\infty$ is larger than all other ordinal sequences.


\begin{lemma}\label{lem:osig}
Let $\phi_1,\phi_2,\phi$ 
be sentences whose definitions constants are in $\deflist$,
$M$ be a 
model, and $a$ be an element of $M$.
The following propositions hold.
\begin{enumerate}
\item If $a \in \evaluation{\phi_1 \wedge \phi_2}$ then $$\SigD(\phi_1 
\wedge \phi_2 , a) = \max\left(\SigD(\phi_1 , a) , \SigD(\phi_2 , a) 
\right)$$
\item If $a \in \evaluation{\phi_1 \vee \phi_2}$ then 
$$\SigD(\phi_1 \vee \phi_2, a) = \min\left(\SigD(\phi_1 ,a),  
\SigD(\phi_2 ,a) \right)$$
\item If $a \in \evaluation{\sigma(\phi_1,\dots,\phi_n)}$ then
$$\SigD(\sigma(\phi_1,\dots,\phi_n), a) \ge \min_{(a_1,\dots,a_n) \in 
\bar{A}} \max_{i \in 
\{1,\dots,n\}} \SigD(\phi_i, a_i)$$
where $\bar{A} = \{(a_1,\dots,a_n) \mid a_1 \in \evaluation{\expan{\phi_1}},
\dots, a_n \in \evaluation{\expan{\phi_n}}, a \in 
\sigma_M(a_1,\dots,a_n) \}$. 
\item If $a \in \evaluation{\bar\sigma(\phi_1,\dots,\phi_n)}$ then
$$\SigD(\bar\sigma(\phi_1,\dots,\phi_n), a) \ge \sup_{(a_1,\dots,a_n) \in 
\bar{A}} \min_{i \in \{1,\dots,n\}} \SigD(\phi_i,a_i) $$
where $\bar{A} = \{(a_1,\dots,a_n) \mid a_1 \in \evaluation{\expan{\phi_1}},
\dots, a_n \in \evaluation{\expan{\phi_n}}, a \in 
\sigma_M(a_1,\dots,a_n) \}$. 
\item If $a \in \evaluation{\mu X \ldotp \phi}$ and $\left(U_i = \mu X \ldotp \phi 
\right) \in \deflist$ is the $i$th $\mu$-constant in $\deflist$, then
$\SigD(\mu X \ldotp \phi, a)$ and $\SigD(U_i, a)$ are the same
at the first $(i-1)$ ordinals.
\item If $a \in \evaluation{\nu X \ldotp \phi}$ and $\left(V = \nu X \ldotp \phi 
\right) \in \deflist$, then $\SigD(\nu X \ldotp \phi, a) = \SigD(V, a)$;
\item If $a \in \evaluation{U}$ and $\left(U_i = \mu X \ldotp \phi_i\right) \in 
\deflist$ is the $i$th $\mu$-constant in $\deflist$, 
then $\SigD(U, a) > \SigD(\phi[U/X], a)$,
and they are the same at the first $(i-1)$ ordinals.
\item If $a \in \evaluation{V}$ and $\left(V = \nu X \ldotp \phi \right) \in \deflist$,
then $$\SigD(V, a) = \SigD(\phi[V/X], a)$$
\end{enumerate}
\end{lemma}
\begin{proof}
We only prove (3) and (4). The other proofs are the same as in~\cite{NW96}.

(3). Let $\bar{\alpha} = \SigD(\sigma(\phi_1,\dots,\phi_n))$
and $\DD_{\alphab}$ be $\deflist'$ as given in Definition~\ref{def:osig}. 
Then, we have $a \in 
\evaluation{\expan{\sigma(\phi_1,\dots,\phi_n)}_{\DD_\alphab}}$.
By the definition of expansion operator, 
we have $a \in 
\evaluation{\sigma(\expan{\phi_1}_{\DD_\alphab}, 
\dots,\expan{\phi_n}_{\DD_\alphab})}$.
Then, there exist $a_1,\dots,a_n$ such that
$a \in \sigma_M(a_1,\dots,a_n)$ and 
$a_i \in \expan{\phi_i}_{\DD_\alphab}$ for $i \in 
\{1,\dots,n\}$.
Let ${\alphab_i} = \SigD(\phi_i,a_i)$.
Then we have $\alphab_i \le \alphab$.
This implies that $\max_i \alphab_i \le \alphab$. 
Therefore, we have
$$\SigD(\sigma(\phi_1,\dots,\phi_n)) \ge \min_{(a_1,\dots,a_n) \in 
\bar{A}} \max_{i \in 
\{1,\dots,n\}} \SigD(\phi_i, a_i)$$

(4). Let $\alphab = \SigD(\bar\sigma(\phi_1,\dots,\phi_n))$
and $\DD_\alphab$ be $\deflist'$ as given in Definition~\ref{def:osig}. 
Then, we have $a \in 
\evaluation{\expan{\bar\sigma(\phi_1,\dots,\phi_n)}_{\DD_\alphab}}$. 
By the definition of expansion operator, we have
$a \in 
\evaluation{\bar\sigma(\expan{\phi_1}_{\DD_\alphab},
\dots,\expan{\phi_n}_{\DD_\alphab})}$.
Then for all $a_1,\dots,a_n$ such that $a \in \sigma_M(a_1,\dots,a_n)$, 
there exists $i \in \{1,\dots,n\}$ such that $a_i \in 
\evaluation{\expan{\phi_i}_{\DD_\alphab}}$,
and thus $\DD_{\alphab} \ge \SigD(\phi_i,a_i)$. 
Therefore, $\DD_{\alphab} \ge \min_i \SigD(\phi_i,a_i)$
for every $a_1,\dots,a_n$ such that $a \in \sigma_M(a_1,\dots,a_n)$, and we have
$$\SigD(\bar\sigma(\phi_1,\dots,\phi_n)) \ge \sup_{(a_1,\dots,a_n) \in 
\bar{A} } \min_{i \in \{1,\dots,n\}} \SigD(\phi_i,a_i) $$
\end{proof}

For any normal sequent $\Gamma = \{\phi_1,\dots,\phi_n\}$, we write
$\evaluation{\expan{\Gamma}_\deflist}$ to mean
$\bigcap_i \evaluation{\expan{\phi_i}_\deflist}$ and drop $\deflist$ when it is 
understood from the context.

\begin{proposition}
\label{prop:mpm}
If a positive guarded sentence $\psi$ is satisfied in $M$ on $a$, then
any tableau for $\psi$ contains a pre-model for $\psi$ as a sub-tree. 
\end{proposition}
\begin{proof}
Let $\deflist = \contr{\psi}$ and 
$(U_{k_1} = \mu X \ldotp \psi_{k_1}) ; \dots ; (U_{k_d} = \mu X \ldotp \psi_{k_d})$ 
be the sub-list of all $\mu$-constants. 
Let
$(T,L)$ be any tableau for $\psi$. 
We construct a quasi-model for $\psi$ by selecting the nodes of $T$.
For every selected node $s$, we associate an element $a_s \in M$, with the 
property that $a_s \in \evaluation{\expan{L(s)}}$, if $L(s)$ is a normal sequent. 

Firstly, we select the root of $T$ and for the associated element, we choose 
any element that matches $\psi$. 

Suppose we have already selected a node $s$ and included it in the quasi-model,
with the associated element $a_s$. 
We show how to proceed from this point, depending on what tableau rule was used 
in the node $s$ of $T$:
\begin{enumerate}
\item $L(s)$ cannot be an inconsistent sequent, because 
$a_s \in \evaluation{\expan{L(s)}}$.
\item If $s$ is an \prule{and}, or an \prule{ons} node, or a \prule{mu} node, 
or a \prule{nu} node, then $s$ has exactly one child $s'$. We select $s'$ and 
let $a_{s'} = a_s$. 
\item If $s$ is an \prule{or} node whose label is $L(s) = \phi_1 \vee 
\phi_2,\Gamma$, then $s$ has two child nodes
$s_1$ and $s_2$, whose labels are
$L(s_1) = \{\phi_1\} \cup \Gamma$ and 
$L(s_2) = \{\phi_2\} \cup \Gamma$, respectively. 
Let $i = \argmin_i \SigD(\phi_i,a_s)$.
We can prove that $a_i \in \evaluation{\expan{\phi_i}}$. 
We select the child node $s_i$ and define $a_{s_i} = a_i$.
\item If $s$ is an \appa{} node then we select all its child nodes.
\item If $s$ is an \appb{} node whose label is $L(s) = \Gamma \leadsto 
\sigma(\phi_1,\dots,\phi_n)$,
then we define 
$$(a_1,\dots,a_n) = \argmin_{(a_1,\dots,a_n) \in \bar{A}} \max_{i 
\in \{1,\dots,n\}} \SigD(\phi_i,a_i)$$
where $\bar{A} = \{(a_1,\dots,a_n) \mid a_1 \in \evaluation{\expan{\phi_1}},
\dots, a_n \in \evaluation{\expan{\phi_n}}, a_s \in 
\sigma_M(a_1,\dots,a_n) \}$. 
We define the witness function $\wit \colon \Gamma_{\bar\sigma} \to \{1,\dots,n\}$ 
as follows. 
For every $\bar\sigma(\psi_1,\dots,\psi_n) \in \Gamma_{\bar\sigma}$, 
since $a_s \in \evaluation{\expan{\bar\sigma(\psi_1,\dots,\psi_n)}}$
and $a_s \in \sigma_M(a_1,\dots,a_n)$, 
there exists $i \in \{1,\dots,n\}$ such  that $a_i \in \evaluation{\expan{\psi_i}}$,
and we define $\wit(\bar\sigma(\psi_1,\dots,\psi_n)) = i$.
We select $s'$ whose label $L(s')$ is $\Gamma \leadsto 
\sigma(\phi_1,\dots,\phi_n) \leadsto \wit$.
\item If $s$ is an \appc{} node whose label is $L(s) = \Gamma \leadsto 
\sigma(\phi_1,\dots,\phi_n) \leadsto \wit$ as defined in (5), we select all 
$n$ child nodes of $s$, written $s_1,\dots,s_n$, and define $a_{s_j} = a_j$
for every $j \in \{1,\dots,n\}$, where $a_1,\dots,a_n$ are defined in (5). 
We need to prove that $a_j \in \evaluation{\expan{L(s_j)}}$.
By definition, $L(s_j) = \{\phi_j\} \cup \Gamma^\wit_j$. 
We have $a_j \in \evaluation{\expan{\phi_j}}$ by construction. 
For any $\psi_j \in \Gamma^\wit_j$,
We have $a_j \in \evaluation{\expan{\psi_j}}$ by the definition of $\Gamma^\wit_j$.
\end{enumerate}

Let us denote the resulting sub-tree as $T_0$.
By construction, $(T_0,L)$ is a quasi-model for $\psi$.
Next, we show that $(T_0,L)$ is a pre-model for $\psi$.

Assume the opposite and suppose $(T_0,L)$ is not a pre-model.
Then there exists a $\mu$-trace $\Tr$ on a path $P$ of $T$.
Suppose $U_{k_i}$ is the oldest definition constant that regenerates infinitely 
often on $\Tr$.
Then there exists a node $s$ on $\Tr$ such that $U_{k_1},\dots,U_{k_{i-1}}$ do 
not regenerate after~$s$.

Consider the signature ordinals of the patterns on $\Tr$ after $s$.
Using Lemma~\ref{lem:osig}, we observe that the $i$-length prefixes of the 
signature ordinals never increase, and every regeneration of $U_{k_i}$ strictly 
decrease the signatures at the $i$th position.
Since ordinal sequences are well-founded, $\Tr$ cannot be infinite, which is a 
contradiction.
Therefore, $(T_0,L)$ contains no $\mu$-trace, and thus it is a pre-model for 
$\psi$.
\end{proof}

\begin{definition}
\label{def:pmc}
Given a pre-model $(T,L)$ for $\psi$, we define a corresponding canonical model
$M$ as follows:
\begin{enumerate}
\item The carrier set $M$ contains as elements all the leaves
and \appa{} nodes of $T$. For any $s \in \Nodes(T)$, we define by $\des_s$ its 
closest descendant node (may be itself) that belongs to $M$. 
Note that $\des_s$ is well-defined, because each infinite path in the pre-model 
must contain infinitely many \appa{} nodes, since all patterns are guarded.
\item $a \in \sigma_M(a_1,\dots,a_m)$ for every non-constant symbol $\sigma$, 
iff $a$ is an \appa{} node, and $L(a)$ contains a pattern of the form 
$\sigma(\phi_1,\dots,\phi_n)$, and $a$ has a child node $s$
with $L(s) = L(a) \leadsto \sigma(\phi_1,\dots,\phi_m)$, 
and $s$ has exactly one child node $s'$ with
$L(s') = L(a) \leadsto \sigma(\phi_1,\dots,\phi_m) \leadsto \wit$ for some $\wit 
\in \Wit(L(a),\sigma)$, 
and $s'$ has exactly $n$ child nodes denoted $s_1,\dots,s_n$,
and that $\des_{s_1} = a_1$, \dots, $\des_{s_n} = a_n$.
\item $c_M = \{ s \in \Nodes(T) \mid c \in L(s) \}$.
\end{enumerate}
\end{definition}

\begin{proposition}\label{prop:pmm}
If there exists a pre-model for a positive guarded sentence $\psi$
then $\psi$ is satisfiable in the corresponding canonical model. 
\end{proposition}
\begin{proof}
Suppose $\psi$ has a pre-model $(T,L)$
and $M$ is its corresponding canonical model as defined in 
Definition~\ref{def:pmc}. 
Let $s_0 =\rt(T)$ be the root of $T$.
Let $\deflist = \contr{\psi}$ and let $(V_{k_1} = \nu X \ldotp \psi_{k_1}) ; \dots ; 
(V_{k_d} = \nu X \ldotp \psi_{k_d})$ be the sub-list of $\nu$-constants in $\deflist$.
For the sake of contraction, we assume $\des_{s_0} \not\in \evaluation{\psi}$
for some (irrelevant) $\rho$.

Firstly, we define the notion of a $\nu$-signature, $\vmeasure(\phi,a)$, 
which is defined for a sentence $\phi$ and $a \in M$ such that
$a \not\in \evaluation{\expan{\phi}}$, as follows:
$$
\vmeasure(\phi,a) = \SignD(\mathit{not}(\phi), a)
$$
where the definition list $\nDD$ is obtained from $\deflist$ by replacing every 
definition $(U = \kappa X \ldotp \phi)$ with
$(U = \mathit{not}(\kappa X \ldotp \phi))$.
Recall that $\mathit{not}(\phi)$ is the equivalent positive guarded formula 
of $\neg \phi$, obtained by pushing in the negation.
Note that Lemma~\ref{lem:osig} translates to $\nu$-signatures after 
interchanging $\mu$ with $\nu$, $\bar\sigma$ with $\sigma$, and $\vee$ with 
$\wedge$. 

Next, we show that the assumption $\des_{s_0} \not\in \evaluation{\psi}$ implies 
that there exists a $\mu$-trace on some path $P$ of $T$, which contradicts the 
fact that $(T,L)$ is a pre-model.

In the following, we construct $P$ and a $\mu$-trace $\Tr$ on $P$, 
simultaneously. 
The first pattern $\Tr(s_0) = \psi$.   
Now, suppose we have constructed $\Tr$ up to $\Tr(s)$ for some node $s$ on $P$,
such that $\des_{s} \not\in \evaluation{\expan{\Tr(s)}}$.
We select the child node $s'$ and $\Tr(s')$ as follows:
\begin{enumerate}
\item If $s$ is an \prule{and}/\prule{or}/\prule{mu}/\prule{nu}/\prule{ons}
node, then $s$ has exactly one child node $s'$ and
\begin{enumerate}
\item if $L(s)$ is not reduced, then $\Tr(s') = \Tr(s)$;
\item if $L(s) = \phi_1 \wedge \phi_2$ or $L(s) = \phi_1 \vee 
\phi_2$ is reduced, we let
      $i = \argmin_i \vmeasure(\phi_i, \des_{s})$ and
      define $\Tr(s') = \phi_i$.
\item in other cases, let $\Tr(s')$ be the only resulting pattern. 
\end{enumerate}
\item If $s$ is an \appa{} node, and
\begin{enumerate}
\item if $L(s) = \{\sigma(\phi_1,\dots,\phi_n)\} \cup \Gamma$ and 
$\Tr(s) = 
\sigma(\phi_1,\dots,\phi_n)$,
then by the hypothesis,
$s \not\in \evaluation{\expan{\sigma(\phi_1,\dots,\phi_n)}}$.
Note that $s$ has a child node $s'$ with
$L(s') = L(s) \leadsto \sigma(\phi_1,\dots,\phi_n)$,
which has exactly one child node $s''$ with
$L(s'') = L(s) \leadsto \sigma(\phi_1,\dots,\phi_n) \leadsto \wit$
for some $\wit \in \Wit(L(s),\sigma)$, which has $n$ child nodes denoted
$s_1,\dots,s_n$.
By the construction of the canonical model, 
$s \in \sigma_M(\des_{s_1},\dots,\des_{s_n})$.
Therefore, there exists $i \in \{1,\dots,n\}$ such that
$\des_{s_i} \not\in \evaluation{\expan{\phi_i}}$.
Let $i = \argmin_i \SigD(\phi_i,\des_{s_i})$ and 
we select $\Tr(s_i) = \phi_i$.
\item if $L(s) = \{\bar\sigma(\phi_1,\dots,\phi_n)\} \cup \Gamma$ and 
$\Tr(s) = \bar\sigma(\phi_1,\dots,\phi_n)$, then by the hypothesis,
$s \not\in \evaluation{\expan{\bar\sigma(\phi_1,\dots,\phi_n)}}$.
Let 
$$\qquad\ \ 
(\des_{s_1},\dots,\des_{s_n}) = \argmin_{(a_1,\dots,a_n) \in \bar{A}} \max_{i 
\in \{1,\dots,n\}} \vmeasure(\phi_i, \des_{s_i})
$$
where $\bar{A} = \{ (a_1,\dots,a_n) \mid s \in \sigma_M(a_1,\dots,a_n) \}$.
We select any $i \in \{1,\dots,n\}$ and let $\Tr(s_i) = \phi_i$.
\item For any other cases, stop the construction of $\Tr$.
\end{enumerate}
\end{enumerate}

If the constructed trace $\Tr$ is finite, then
either the last pattern $\Tr(s_N)$ is a constant symbol or its negation, or 
$s_N$ is a leaf node and the pattern $\Tr(s_N)$ is a $\bar\sigma$-pattern.
From the definition of the canonical model, we have $\des_{s_N} \in \Tr(s_N)$, 
a contradiction.

If $\Tr$ is infinite, then by a similar argument to the one in 
Proposition~\ref{prop:mpm}, we can show that the oldest definition constant 
that regenerates infinitely often on $\Tr$ is a $\mu$-constant, which  
contradicts the fact that $(T,L)$ is a pre-model. 

Therefore, our assumption that $\des_{s_0} \not\in \evaluation{\psi}$ is incorrect, 
and thus $\psi$ is satisfiable in the canonical model.
\end{proof}

\begin{theorem}\label{thm:pm}
For any positive guarded sentence $\psi$, there exists a pre-model for $\psi$ 
iff $\psi$ is satisfiable.
\end{theorem}
\begin{proof}
By Propositions~\ref{prop:mpm} and~\ref{prop:pmm}. 
\end{proof}

\subsection{Decidability}

\begin{theorem}
For any positive guarded sentence $\psi$, determining whether $\psi$ is 
satisfiable is decidable.
\end{theorem}
\begin{proof}
\todo{Check details.}
By Theorem~\ref{thm:pm}, we can look for a pre-model for $\psi$.
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

\begin{theorem}
ML$^{\not\exists,\mu}$ is decidable.
\end{theorem}


* Example:
    *  $(\mu X \ldotp z \lor s(X)) \land \nu X \ldotp \lnot z \land \bar s(X)$
    *  this is an interesting example because it shows the need for alpha renaming in the implementation.

----

\begin{definition}
A \emph{quasi-model} for $\psi$ is defined as the tableau for $\psi$ given in 
Definition~\ref{def:tableau},
whereas the rule set $\SSSmod$ is used instead of $\SSS$, and no leaves are 
labeled with inconsistent sequents. 
\end{definition}

\begin{remark}\label{rmk:quasi-model}
A quasi-model for $\psi$ is a sub-tree of the tableau for $\psi$ by cutting off 
the child nodes of \prule{or} and \appb{} nodes and making them have exactly one 
child node.  
\end{remark}

