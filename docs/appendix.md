\clearpage
\appendix
\addcontentsline{toc}{chapter}{Appendix}
# Correctness

Below, we define concepts that will be used later for proving the
above two theorems.

If a pattern is satisfiable in a model, it is satisfiable with finite unfoldings
of its least fixedpoint patterns.
We codify this using *approximations* of fixedpoints. 

Definition (Approximations)

:   For any ordinal $\tau$ and pattern $\alpha$, we define two new patterns:
    $\mu^\tau X\ldotp \alpha(X)$ and
    $\nu^\tau X\ldotp \alpha(X)$, with the following semantics:

    * $\evaluation{\mu^0 X\ldotp \alpha(X)}_{M,\rho} = \emptyset$
    * $\evaluation{\nu^0 X\ldotp \alpha(X)}_{M,\rho} = M$
    * $\evaluation{\kappa^{\tau + 1} X\ldotp \alpha(X)}_{M,\rho}
      = \evaluation{\alpha(X)}_{M,\rho[{\kappa^{\tau + 1} X\ldotp \alpha(X)}/X]}$
      where $\kappa$ is either $\mu$ or $\nu$.

    We extend the notion of definition lists by allowing mappings of the form
    $D \mapsto \mu^\tau X \ldotp \alpha$ and
    $D \mapsto \nu^\tau X \ldotp \alpha$.

A $\mu$-measure of a pattern in a satisfying model encodes the minimum number of unfoldings
of fixedpoints corresponding to each $\mu$-marker needed for the pattern to be satisfiable.

Definition ($\mu$-measure -- $\umeasure$)

:   Fix definition list $\deflist$, a dependency order $\dependson$, a model $M$, an evaluation $\rho$ and an assertion $\alpha$.
    Let $U_{k_1}, U_{k_2}, \ldots, U_{k_n}$ be the $\mu$-markers occuring in $\deflist$
    ordered by $\dependson$.
    For $\alpha = \matches{x}{\phi}$ with $\rho(x) \in \evaluation{\phi}^\deflist_{M,\rho}$,
    we define the *$\mu$-measure* of $\alpha$ in $M$ for $\rho$, $\umeasure_{M,\rho}(\alpha)$,
    to be the least tuple $(\tau_1,\ldots,\tau_n)$
    such that $\rho(x) \in \evaluation{\phi_\deflist}^{\deflist'}_{M,\rho}$
    where $\phi_\deflist$ is the pattern constructed by replacing
    each fixedpoint pattern in $\phi$ with its marker in $\deflist$,
    and $\deflist'$ is obtained by replacing each $\mu$-marker $(U_{k_i} \mapsto \mu X\ldotp \alpha_{k_i}(X))$
    with $(U_{k_i} \mapsto \mu^{\tau_i} X\ldotp \alpha_{k_i}(X))$.
    The $\mu$-measures for conjunctions (resp. disjunctions) of assertions
    is defined in the obvious way -- it is the least tuple such that every sub-assertion (resp. any sub-assertion)
    is matched in the model.

Remark

:   Observe that
    if an assertion is not satisfied by a model then its measure is not defined,
    and the measure of an assertion $\phi$ is $0$ in all positions corresponding to a $\nu$-marker$. 


Lemma ($\mu$-measures are (non-strictly) decreasing over edges in a pre-model)

:   \label{lemma:measures-decreasing}
    The following facts hold about signatures under a model $M$ and interpretation $\rho$:

    a. If $\matches{x}{\phi}\lor\matches{y}{\psi}$ has $\mu$-measure $\bar \tau$, then
       either $\matches{x}{\phi}$ or $\matches{y}{\psi}$
       has $\mu$-measure $\bar \tau$.

    b. If $\matches{x}{\phi}\land\matches{y}{\psi}$ has $\mu$-measure $\bar \tau$, then
       both $\matches{x}{\phi}$ and $\matches{y}{\psi}$
       have $\mu$-measure not larger than $\bar \tau$.

    c. If $\matches{x}{\bar\sigma(\bar\phi)}$ has $\mu$-measure $\bar \tau$, then
       for every tuple $\bar m \subset M$
       we have $\mu$-measure of $\matches{x}{\fnot{\sigma(\bar y)}}\lor\lOr_i\matches{x_i}{\phi_i}$ is not larger than $\bar \tau$
       for interpretation $\rho[\bar m/\bar x]$.

    d. If $\matches{x}{\forall \bar x \ldotp \phi}$ has $\mu$-measure $\bar \tau$, then
       for every tuple $\bar m \subset M$
       we have $\mu$-measure of $\matches{x}{\phi}$ is not larger than $\bar \tau$
       for interpretation $\rho[\bar m/\bar x]$.

    e. If $\matches{x}{\sigma(\bar \phi)}$ has $\mu$-measure $\bar \tau$, then
       there is a tuple $\bar m \subset M$
       such that
       the $\mu$-measure of $\matches{x}{\sigma(\bar x)}\land\lAnd_i\matches{x_i}{\phi_i}$ is equal to $\bar \tau$
       for interpretation $\rho[\bar m/\bar x]$.

    f. If $\matches{x}{\exists \bar y \ldotp \phi}$ has $\mu$-measure $\bar \tau$, then
       there is a tuple $\bar m \subset M$
       with $\mu$-measure of $\matches{x}{\phi}$ equal to $\bar \tau$
       for interpretation $\rho[\bar m/\bar y]$.

    g. If $\matches{x}{\kappa X\ldotp \phi}$ has $\mu$-measure $\bar \tau$,
       and $\deflist(D_i) = \kappa X\ldotp \phi$ then
       $\matches{x}{D_i}$ also has $\mu$-measure $\bar \tau$.

    h. If $\matches{x}{D_i}$ has $\mu$-measure $\bar \tau$,
       and $\deflist(D_i) = \mu X\ldotp \phi$ then
       $\matches{x}{\phi[D_i/X]}$ has $\mu$-measure identical on the first $i - 1$ positions,
       with the $i$th strictly less.

    i. If $\matches{x}{D_i}$ has $\mu$-measure $\bar \tau$,
       and $\deflist(D_i) = \nu X\ldotp \phi$ then
       $\matches{x}{\phi[D_i/X]}$ also has $\mu$-measure $\bar \tau$.

Proof

:   Same as for guarded fixedpoint logic

## Satisfiability implies a pre-model

Lemma (Satisfiable patterns have pre-models)

: Given a pattern $\phi$ and an element $m$ in $M$ such that
$e \in \evaluation{\phi}$, then for any tableau $\mathcal T$, the game
$\mathcal G(\mathcal T)$ contains a pre-model.

Proof

:   We will build a strategy for the game
    by selecting positions from the game
    and associating each free element variable in each position $p = (\alpha, v)$
    in the selected subtree with an element in the model
    through a valuation $\rho_p$, while maintaining three invariants:

    1. Under this valuation, the assertions in $\Basic(v)$ are satisfied.
    2. Every free element variable in a sequent has distinct interpretations.
    3. The measure does not increase between along any edge.

    We will then show
    that the strategy must be a pre-model -- i.e. it is winning for player $0$.

    The root position of the game is labeled with  
    $(\matches{x}{\phi}, \sequent{\matches{x}{\phi}, \emptyset, \emptyset, \{x\}})$.
    The invariants hold for the root position.
    Define $\rho_\mathrm{root}(x) = m$
    and select the root position as part of the strategy.

    Consider a selected position $p$:

    * Suppose the (resolve) rule was applied at that position
      on the assertion $\matches{x_0}{\sigma(x_1,\ldots,x_n)}$.
      Then if $\rho_p(x_0) \in \evaluation{\sigma(x_1,\ldots,x_n)}_{M,\rho_p}$
      we select the left child position, $l$,
      (that has $\matches{x_0}{\sigma(x_1,\ldots,x_n)} \in \Basic$)
      and define $\rho_l = \rho_p$.
      Otherwise, we select the right child position, $r$,
      (that has $\matches{x_0}{\bar\sigma(\lnot x_1,\ldots,\lnot x_n)} \in \Basic$).
      and define  $\rho_r = \rho_p$. The measure $\tau$ remains the same.

    * If the (or) rule was applied to assertion $\matches{x}{\psi_1} \lor \matches{y}{\psi_2}$
      we select the child with $\matches{x}{\psi_1}$
      if $\umeasure(\matches{x}{\psi_1}) \le \umeasure(\matches{y}{\psi_2})$.
      Otherwise, we select the child with $\matches{y}{\psi_2}$.
      As per Lemma \ref{lemma:measures-decreasing}, the signature remains the same.

    * Suppose the (app) rule was applied to assertion
      $\matches{x}{\sigma(\psi_1,\ldots,\psi_n)}$.
      From our invariants, we know that $\rho_p(x) \in \evaluation{\sigma(\psi_1,\ldots,\psi_n)}_{M,\rho_p}$.
      Therefore there must be some $m_1,\ldots,m_n \in M$
      such that $\rho_p(x) \in \sigma_M(\bar m)$ and $m_i \in \evaluation{\psi_i}_{M,\rho_p}$.

      Select a child of $p$,
      say $p' = \sequent{\matches{x}{\sigma(\bar y)} \land \matches{y_i}{\psi_i}; \Basic'; \Universals'}$,
      such that:

      *   Let $\mathcal E := \{ x \} \union \Union_i \free{\psi_i}$, and
      *   if for some $i$, $m_i = \rho_p(x)$ where $x \in \mathcal E$ then $y_i = x$.
      *   if $m_i = m_j$, then $y_i = y_j$.

      Define: $\rho_{p'} = \begin{cases}x   \mapsto \rho_p(x) & \text{when $x \in \mathcal E$} \\
                                       y_i \mapsto  m'_i \\ \end{cases}$  
      As per Lemma \ref{lemma:measures-decreasing}, the signature remains the same.

    * Suppose the (exists) rule was applied to assertion
      $\matches{c}{\exists \bar x \ldotp \phi}$.
      We know that $\rho_p(c) \in \evaluation{\exists \bar x \ldotp \phi}_{M,\rho_p}$.
      Therefore there must be some $m_1,\ldots,m_n \in M$
      such that $\rho_p(c) \in \evaluation{\phi}_{M,\rho_p[\bar m/\bar x]}$
      with measure $\tau$.

      Select a child of $p$,\newline
      say $p' = \sequent{\matches{e}{\phi[\bar k/\bar x]}; \Basic'; \Universals'}$,
      such that:

      * $\mathcal E$ is the free element variables of the node
      * if for some $i$, $m_i = \rho_p(e)$ where $e \in \mathcal E$ then $k'_i = e$.
      * if $m_i = m_j$, then $k_i = k_j$.

      Define: $\rho_{p'} = \begin{cases}e_{\phantom{i}}   \mapsto \rho_p(e) & \text{when $e \in \mathcal E$} \\
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
    It cannot be a (mu) node since (mu) nodes strictly decrease the $\umeasure$,
    a well-founded measure.
    Suppose it is a (exists) or (app)-node (for sake of contradiction).
    Let us consider an (infinite) suffix of the trace that doesn't have any (nu) or (mu) nodes.
    This must exist, otherwise (mu) or (nu), with lower priority would repeat infinitely.
    Now, every the remaining rules (i.e. excluding (mu) and (nu)) reduce the depth of the pattern.
    So, (exists) or (app) cannot infinitely occur without a (mu) or (nu) rule also appearing infinitely often.


From the definition of parity games and winning strategies,
it is clear that a tableau may not contain both a pre-model and a refutation.
It is less clear that either one must exists.
This follows from determinacy of the more general Borel Games, as shown in [@martin75-borel-determinacy], giving us:

Lemma (Either pre-model or refutation)

: For a game $\mathcal G(\mathcal T)$ either a pre-model or a refutation exists (but not both).

From this two lemma, one of our two main theorems, Theorem \ref{theorem:validity} follows.
Restated:

\todo{fix theorem number}
Theorem

:   \label{theorem:validity}
    If a guarded pattern has a tableau with a refutation, then it is unsatisfiable
    and its negation is valid.

Remark

:   Notice that this proof only relies on Property \ref{item:fixedpoint-no-elements} of guarded patterns.
    Therefore, this result holds for any pattern
    (guarded or not) that meets just this condition.

## Pre-models imply satisfiability

Next we want to show that for any guarded pattern,
if player $0$ wins, then the pattern is indeed satisfiable
-- i.e. for every pre-model, there is a satisfying model.
To do so, we will construct a model from the pre-model.

Let $\mathcal T$ be a tableau
where $V$ is the set of vertices and $L : V \to \Sequent$ is its labeling function.
Let $S$ be a pre-model for the game $\mathcal G(\mathcal T)$.
For an element variable $x$, we say that two nodes $v, w \in V$ are $x$-equivalent if
$x$ is free in some assertion in each node (i.e. $x \in \free{\Gamma \union \Universals \union \Basic}$) in the path from $v$ to $w$, inclusive.
This relation defines an equivalence class.
Notice that each equivalence class is a subtree of the tableau.

\newcommand{\var}  {\mathsf{var}}
\newcommand{\nodes}{\mathsf{nodes}}

From a pre-model $S$, we define a model $M(S)$.
Let $V_{\equiv_x}$ be the set of equivalence classes in $T$ for a constant $x$.
Let $M = \{ (x, v) \mid
\text{ where $v \in V_{\equiv_x}$ and $v \intersection S \ne \emptyset$ }\}$
be the universe of the constructed model.
For an element $e = (x, v) \in M$ we define $\var(e) = x$ and $\nodes(e) = v$.

We define the interpretation of each symbol, $\sigma_{S(M)}$,as follows:

*   $e_0 \in \sigma_M(e_1,\ldots,e_n)$
    if $\matches{\var(e_0)}{\sigma(\var(e_1),\ldots,\var(e_n))}$
    is in the basic assertions $\Basic$ for some vertex in $\Intersection_{0\leq i \leq n} \nodes(x_i)$.
*   $e_0 \not\in \sigma_M(e_1,\ldots,e_n)$
    if $\matches{\var(e_0)}{\fnot{\sigma(\var(e_1),\ldots,\var(e_n))}}$
    is in the basic assertions $\Basic$ for some vertex in $\Intersection_{0\leq i \leq n} \nodes(x_i)$.
*   otherwise, it is not important which one holds.
    Arbitarily, we choose $m_0 \not\in \sigma_M(m_1,\ldots,m_n)$
    if neither of the above hold.

This is well-defined since whenever a new element is created in the tableau (resolve) is applied immediately.
Further, a pre-model may only include one child of each (resolve) node.
From this definition we immediately get the following lemma:

Lemma

:   Let $m_0, m_1, \ldots, m_n \in M$.
    If $m_0 \in \sigma_M(m_1, \ldots, m_n)$ then,
    for every vertex $v \in \Intersection_{0\le i\le n} \nodes(m_i)$
    besides an initial linear prefix of (resolve) applications
    we have $\matches{\var(m_0)}{\sigma(\var(m_1), \ldots, \var(m_n)}$ in the label of $v$.

Lemma

:   \label{lemma:guards}
    Let $\alpha = \matches{y_0}{\phi}$, where $\phi$ is the guard of some existential pattern.
    That is, let $\bar x \subset \free{\phi}$, and:

    a) $\phi = \phi_1 \land \cdots \land \phi_n$ where each $\phi_i$ is an application of the form $\sigma(\bar w)$ where $\bar w$ are element variables.
    b) every $x \in \bar x$ appears in some $\phi_i$
    c) for every pair $x \in \bar x$ and $z \in \free{\phi}$ we have $x$ coexists with $z$ in some $\phi_i$.

    Then, if there is a valuation
    $\rho: \{y_0\} \union \free{\phi} \to M(S)$ such that
    $\rho(y_0) \in \evaluation{\alpha}_{M(S),\rho}$ and
    $\Intersection_{y\in\{y_0\}\union \bar y} \nodes(\rho(y)) \neq \emptyset$
    we have $\Intersection_{z\in\{y_0\}\union\free{\phi}}\nodes(\rho(z)) \neq \emptyset$.

Proof

:   By definition, each element $m$ in $M(S)$, $\nodes(m)$ is a subtree of $S$.
    The element is introduced by either the root node or some (exists) or (app) node followed by
    a linear sequence of (resolve) nodes.
    As we decend the tree the asssertions in $\Basic$ that mention the $\var(m)$
    increase until the last (resolve) node in that sequence and then does not change.

    Let $\bar y = \free{\phi} \setminus \bar x$.
    We will show that for each pair of variables in $w_1, w_2 \in \{y_0\}\union\free{\phi}$,
    we have $\nodes(w_1) \intersection \nodes(z_2) \ne \emptyset$.
    Then, using a well-known graph theory result saying that any collection of pairwise intersection
    subtrees of a tree share a common edge.

    Suppose $w_1, w_2 \in \{ y_0 \} \union \bar y$. Then by assumption, they have a non empty intersection.
    If $w_1 = y_0$ and $w_2 \in \bar x$ then by point (b) they must coexist in some assertion.
    If $w_1 \in \free{\phi}$ and $w_2 \in \bar x$ then by point (c) they must coexist in some assertion.
    By definition of $M(S)$ they must co-exist in some assertion.

Lemma

:   \label{lemma:app-guards}
    Let $\alpha = \matches{y_0}{\sigma(\phi)}$, where $\phi$ is the guard of some existential pattern.
    That is, let $\bar x \subset \free{\phi}$, and:


Definition ($\nu$-measure -- $\vmeasure$)

:   Suppose, $\rho(m) \not\in \evaluation{\phi}_{M,\rho}$.
    Then $\rho(m) \in \evaluation{\lnot\phi}_{M,\rho}$
    and the $\mu$-measure of $\matches{m}{\lnot\phi}$ is defined
    (after converting to positive-normal form).
    We call this the $\nu$-measure of $\matches{m}{\phi}$ in $M,\rho$.

Lemma

:   \label{lemma:vmeasure} For a $\nu$-measure, the dual of Lemma \ref{lemma:measures-decreasing} holds.


Lemma (Pre-model implies satisfiability)

:   For a *guarded* pattern $\phi$ and a pre-model $S$, we have $M(S) \satisfies \phi$.

Proof

:   Suppose, by way of contradiction, $\psi$ is not satisfied in $M(S)$.
    We will use this to prove that there must by a play conforming to $S$ such that player $1$ wins
    -- i.e. $S$ is not a winning strategy for player 0, and therefore not a pre-model.
    Along this play we maintain these invariants:

    * At each position $p = (\matches{x}{\phi}, s)$,
      we define a evaluation $\rho_p$ such that $\rho_p(x) \not\in \evaluation{\phi}_{M,\rho_p}$.
    * The $\nu$-measure at each position is decreasing.

    The root of the play is $(\matches{x}{\psi}, \sequent{\matches{x}{\phi}; ...; \{x\};})$.
    By our assumptions, $\vmeasure(\psi)$ is defined.
    We define $\rho_p(x)$ to be the $x$-equivalence defined by the root node.

    Consider a paritally constructed play until position $p = (\matches{y}{\phi}, s)$:

    * (conflict)/(ok): $\phi$ cannot be a basic application or an element variable
        by definition of $M(S)$ and by our invariants and the definition of the model $M(S)$.
    * (resolve): Application of this rule does not affect the $\nu$-measure.
        We use the same $\rho_p$ for the child node.
        Since it is player $1$'s turn, there is no choice to make.
    * (or): if $\phi = \zeta \lor \eta$ then by Lemma \ref{lemma:vmeasure},
        $\vmeasure(\phi) \leq \vmeasure(\zeta)$ and $\vmeasure(\phi) \leq \vmeasure(\eta)$.
        Since it is player $1$'s turn, there is no choice to make.
        We use the same $\rho_p$ for the child node.
    * (and): if $\phi = \zeta \land \eta$ then by Lemma \ref{lemma:vmeasure},
             for some $\theta \in \{\zeta, \eta\}$
             we have $\vmeasure(\phi) = \vmeasure(\theta)$.
             We select the child corresponding to $\theta$ as the next position in the play.
             We use the same $\rho_p$ for the child node.
    * (exists): if $\phi = \exists \bar x\ldotp \gamma$,
                then by Lemma \ref{lemma:vmeasure}, the measure doesn't increase.
                We extend $\rho_p$ to evaluate each constant to its corresponding equivalence class.
                Since $\exists \bar x\ldotp \gamma$ is not satisfied by $\rho_p$, there is no evaluation
                extension that satisfies $\gamma$.
    * (app):    Similar to (exists).

    * (forall): if $\phi = \forall \bar x\ldotp \alpha \limplies \xi$
        then, to continue the play, we may choose between an immediate instantiation,
        or postponing instantiation and keeping $\phi$ the same
        until after the application of (exists) or (app) introduces additional elements that we use in the instantiation.

        Since $\rho_p(y) \not\in \evaluation{\phi}_{M,\rho_p}$
        we know that there is some extension $\rho'$ of $\rho_p$ for variables $\bar x$
        such that $\rho'(y) \in \evaluation{\alpha}_{M,\rho'}$
        but       $\rho'(y) \not\in \evaluation{\xi}_{M,\rho'}$
        and by Lemma \ref{lemma:vmeasure} that $\nu$-measure
        of the corresponding assertion is not larger than the current $\nu$-measure.

        Since $\alpha$ is a guard satisfied by $M,\rho'$, by Lemma \ref{lemma:guards},
        there is a position $q$ in the intersection of equivalence classes
        corresponding to each of the variables in $\free{\xi} \union \{ y \}$.
        That is $q \in \Intersection_{z\in\{y\}\union\free{\xi}}\nodes{\rho'(z)}$.
        If $p = q$ then we choose the corresponding instantiation.
        If $p \neq q$ then choose the child the $p$ on the path to $q$.

    * (\dapp): if $\phi = \bar\sigma(\bar \xi)$, then,
        again, to continue the play, we may choose between in immediate instantiation, or
        postpone instantiation until some (app) or (exists) introduces additional elements
        that we may use in the instantiation.
        Once an instantiation is chosen,
        the strategy $S$ may choose any one branch from the subsequent (or) nodes
        corresponding to the assertion $\matches{z}{\fnot{\sigma(\bar x)}} \lor \lOr_i \matches{x_i}{\xi_i}$.

        Since $\rho_p(y) \not\in \evaluation{\phi}_{M,\rho_p}$
        we know that there is some extension $\rho'$ of $\rho_p$ to include some fresh variables $\bar x$,
        such that $\rho'(y) \in \evaluation{\sigma(\bar x)}_{M,\rho'}$
        and for all  $i$, $\rho'(x_i) \not\in \evaluation{\xi_i}$.

        Since $\phi$ is part of a guarded pattern, each $\xi_i$
        of the form $\fnot{\lAnd_{y \in \bar y} y \land \xi'_i}$,
        -- i.e. of the form: $\lOr_{y \in \bar y} \lnot y \lor \xi'_i$
        where $\bar y$ is a tuple of free element variables
        and all free variables of each $\xi_i$ are in some $\bar y$.

        Suppose $\bar y$ has two or more distinct element variables for some argument.
        For $w$ and $z$ with distinct evaluations,
        we have $\lnot w \lor \lnot z$ is always satisfiable.
        This contradicts with the invariant that $\rho_p(y) \not\in \evaluation{\phi}_{M,\rho}$.
        This is means that $w$ and $z$ must therefore have the same evaluation
        and so $\phi$ and $\phi[w/z]$ are equisatisfiable.
        We may thus assume the each $\bar y$ has size zero or one.

        Consider the case where the tuple has size one.
        Since $\rho'(x_i)\not\in\evaluation{\xi_i}$
        so for $\xi_i \equiv \lnot y \lor \xi'$, then we must have $\rho'(x_i) = \rho'(y)$.
        This means that we must choose an instantiation where $x_i = y$.

        The pattern $\sigma(\bar x_i)$ meets the criteria for  Lemma \ref{lemma:guards}
        and every free variable in $\phi$ either occurs in $x_i$ or has the same interpretation as one.
        So, we know that there must be a position $q$ corresponding to this instantiation.
        If $p = q$ then we choose the corresponding instantiation.
        If $p \neq q$ then choose the child the $p$ on the path to $q$.

        By Lemma \ref{lemma:vmeasure} that $\nu$-measure
        of the corresponding assertion is not larger than the current $\nu$-measure.

    *   In the remaining cases there is no choice, and the invariants are maintained.

    We must show that the trace constructed above is winning for player $1$.
    First, note that the above trace is infinite.
    If the node with least parity occuring infinitely often is an existential, then player $1$ wins.
    If cannot be a universal, because of the way we build the trace -- we know that
    there is a finite path to a node with an instantiation that contradicts the quantifier.
    $\mu$ patterns are winning for player $1$ while $\nu$ patterns decrease the $\nu$-measure.
    So, the trace must be winning for player $1$ constradicting that $S$ is a pre-model and the pattern is satisfiable.

\newpage
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

\onecolumn
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


