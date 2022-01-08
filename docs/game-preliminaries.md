## Definition Lists, Approximations and Parity games

For convenience, the derived semantics of $\bar\sigma(\bar \phi)$ is:
\begin{align*}
\evaluation{\bar\sigma(\phi_1,\ldots,\phi_n)} &= \{a \in M \mid 
                            \forall a_1,\ldots,a_n \text{ s.t. } a \in \sigma_M(a_1,\ldots,a_n)
\\&\qquad\qquad\limplies \exists i, 0 < i < n, \text{ s.t. } a_i \in \evaluation{\phi_i} \}
\end{align*}
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


        Intuitively, $\contr{\varphi}$ summaries all the fixpoint sub-patterns of 
        $\varphi$ in a top-down way. 
        The oldest (i.e., first) definition constant in $\contr{\varphi}$ corresponds 
        to the 
        topmost fixpoint sub-pattern of $\varphi$, say, $\mu X_1 \ldotp \varphi_1$.
        Then, the fixpoint sub-patterns of $\varphi_1[U_1 / X_1]$ are recursively 
        summarized, where all the (recursive) occurrences of $X_1$ 
        are replaced with $U_1$. 
        Therefore, 
        for every $(U_i = \varphi_i) \in \contr{\varphi}$,
        the subscript $i$ denotes the \emph{timestamp}
        that shows the time when $\varphi_i$ is summarized.
        If $U_i$ is \emph{older} than $U_j$, then the defining pattern 
        $U_i$ is summarized \emph{before} that of $U_j$ is summarized. 
        Since $\contr{\varphi}$ is computed in a top-down way,
        $U_1,\dots,U_n$ are listed 
        in the pre-order traversal of the parse tree of $\varphi$.


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

Definition (Parity game)

:   A *parity game* is a tuple $(\Pos_0, \Pos_1, E, \Omega)$
    where $\Pos = \Pos_0 \disjointunion \Pos_1$ is a possibly infinite set of positions;
    Each $\Pos_i$ is called the *winning set* for player $i$.
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

(cite: Infinite games on finitely coloured graphs with applicatiosn to automata on infinite trees)
(cite: Tree automata, mu-calculus and determinacy)

