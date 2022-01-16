# Matching Logic Preliminaries {#sec:ml-prelims}

Matching logic was first proposed in [@matchinglogiclmcs] as a unifying logic
for specifying and reasoning about programming languages.
An important feature of matching logic is that it makes no distinction between terms and formula.
This flexibility makes many important concepts easily definable in matching logic,
and allows for awkwardness free encodings of various abstractions and logics possible.
For example,
LTL formulae have identical syntax to their embedding in matching logic,
and  unification may be characterized by conjuncting two pattern built from constructors.

Matching logic formulae are called *patterns*
and have a "pattern matching" semantics,
in the sense that each pattern represents the set of elements that "match" it.
For example, $\mathsf{cons}(42, x)$ matches lists whose first element is $42$,
while $\mathsf{prime} \land \mathsf{even}$ matches the natural $2$,
assuming correct axiomatizations for $\mathsf{cons}$, $\mathsf{prime}$, and $\mathsf{even}$.

## Matching Logic Syntax

For a set $\EVar$ of *element variables*, denoted $x, y, z, \ldots$, 
and a set $\SVar$ of *set variables*,     denoted $X, Y, Z, \ldots$, we define the syntax of matching logic below.

Definition (Matching logic signatures)

:   A matching logic \emph{signature}, $\Sigma$ is a set of symbols with an associated arity.
    Symbols with an arity of zero are called \emph{constants}.

Definition (Patterns)
: 
    Given a signature $\Sigma$, a countable set of element variables $\EVar$ and of set variables $\SVar$,
    a matching logic \emph{pattern} is built recursively using the following grammar:
    \begin{align*}
    \phi:=  \underbrace{\sigma(\phi_1, \dots, \phi_n)}      _\text{\structure{}}
      \mid  \underbrace{\phi_1 \land \phi_2 \mid \lnot \phi}_\text{\logic{}}
      \mid  \underbrace{x \mid \exists x \ldotp \phi}       _\text{\quantification}
      \mid  \underbrace{X \mid     \mu X \ldotp \phi}       _\text{\fixedpoint{}}
    \end{align*}
    where $x \in \EVar$, $X \in \SVar$ and $\sigma \in \Sigma$ has arity $n$, and $X$ occurs only positively in $\mu X\ldotp \phi$. That is, $X$ may only occur under an even number of negations in $\phi$. 

We assume the standard notions for free variables, $\alpha$-equivalence, and capture-free substitution $\phi[\psi/x]$
and allow the usual syntactic sugar:
\begin{align*}
                       \top &\equiv \exists x \ldotp x &
                       \bot &\equiv \lnot \top \\
         \phi_1 \lor \phi_2 &\equiv \lnot(\lnot\phi_1 \land \lnot\phi_2) &
    \phi_1 \limplies \phi_2 &\equiv \lnot \phi_1 \lor \phi_2 \\
      \forall x \ldotp \phi &\equiv \lnot \exists x \ldotp \phi &
      \nu X \ldotp \phi &\equiv \lnot \mu X \ldotp \lnot \phi[\lnot X/X]
\end{align*}
$\sigma(\phi_1, \dots, \phi_n)$ are called applications. 
Nullary applications are called constants, are denoted by using $\sigma$ instead of $\sigma()$.

## Semantics of Matching Logic {#sec:semantics-of-matching-logic}

Unlike in FOL, matching logic patterns are interpreted as a set of elements in a model rather than a single element.
Intuitively, the interpretation is the set of elements that match a pattern.
For example, the constant $\mathsf{even}$ might have as interpretation the set of all even naturals,
while $\mathsf{greaterThan}(3)$ may be interpreted as all integers greater than $3$.
Function symbols may be considered a special case of this, where when applied to an argument the interpretation is a singleton set.
Logical constructs are thought of as set operations over matched elements
-- for example, $\phi \land \psi$ is interpreted as the intersection of elements matched by $\phi$ and $\psi$,
while $\lnot \phi$ matches all elements \emph{not} matched by $\phi$.
An existential $\exists x \ldotp \phi(x)$ is interpreted as the union of all patterns matching $\phi(x)$ for all valuations of $x$.
$\mu X \ldotp \phi(X)$ matches the \emph{least} set $X$ such that $X$ and $\phi(X)$ match the same elements.
An important point to note here is that element variables have as evaluation exactly a single element,
whereas set variables may be interpreted as any subset of the carrier set.

Definition ($\Sigma$-models)

:   Given a signature $\Sigma$, a $\Sigma$-model is a tuple $(\mathbb M, \{ \sigma_M \}_{\sigma \in \Sigma} )$
    where $\mathbb M$ is a set of elements called the carrier set,
      and $\sigma_M : M^n \to \powerset(M)$ is the interpretation of the symbol $\sigma$ with arity $n$ into the powerset of $M$.

We use $M$ to denote both the model $M$, and it's carrier set, $\mathbb M$.
We also tacitly use $\sigma_M$ to denote the pointwise extension, $\sigma_M : \powerset(M)^n \to \powerset(M)$,
defined as $\sigma_M(A_1,\dots,A_n) \mapsto \Union_{a_i\in A_i} \sigma_M(a_1,\dots,a_n)$
for all sets $A_i \subseteq M$.

Definition def:semantics (Semantics of matching logic)

:   Let $\rho : \EVar{} \union \SVar{} \to \powerset(M)$ be a function such that $\rho(x)$ is a singleton set when $x \in \EVar$,
    called an evaluation.
    Then, the evaluation of a pattern $\phi$, written $\evaluation{\phi}_{M,\rho}$ is defined inductively by:
    \begin{align*}
    \evaluation{\sigma(\phi_1, \ldots, \phi_n)}_\rho &= \sigma_M(\evaluation{\phi_1}, \ldots, \evaluation{\phi_n}) \text{ for $\sigma$ of arity $n$} \\
    \evaluation{\phi_1 \land \phi_2}_\rho            &= \evaluation{\phi_1}_\rho \intersection \evaluation{\phi_2}_\rho \\
    \evaluation{\lnot \phi}_\rho                     &= M\setminus \evaluation{\phi}_\rho \\ 
    \evaluation{x}_\rho                              &= \rho(x) \text{ for } x \in \EVar \\
    \evaluation{\exists x \ldotp \phi}_\rho          &= \bigcup_{a \in M}  \evaluation{\phi}_{\rho[a/x]}\\
    \evaluation{X}_\rho                              &= \rho(X) \text{ for } X \in \SVar  \\
    \evaluation{\mu X \ldotp \phi}_\rho              &= \mathsf{LFP}(\FF)
    \end{align*}
    \begin{align*}
    \text{where }&&
        \FF(A) &= \evaluation{\phi}_{\rho[A/X]} \text{ for } A \subseteq M, \\
    \text{and} &&
        \mathsf{LFP}(f) &\mapsto \Intersection\left\{A \in \powerset{M} \mid f(A) \subset A \right\}
    \end{align*}
    takes a monotonic function to its least fixedpoint [@matching-mu-logic].


As seen, $\sigma$ is interpreted as a relation. 
Its interpretation $\sigma_M$ is not a function in the standard FOL sense.
We say that $\sigma_M$ is \emph{functional}, if:
\begin{equation}\tag{functional-symbol}
\label{eq:functional-symbol}
\size{\sigma_M(a_1,\dots,a_n)} = 1  \quad \text{for all $a_1 \in  M_{s_1}, \dots, a_n \in M_{s_n}$}
\end{equation}

## Satisfiability and Validity

In this subsection, formally define satisfiability and validity in matching logic\footnote{
Note that our definitions differ from [@matchinglogiclmcs] where only validity in a model is defined (but referred to as satisfiability).
We avoid using the $\models$ notation to avoid confusion between the two.
}.
Because of the powerset interpretation of patterns, the notions of satisfiability and validity differ
subtly from those in FOL.
The interpretations of FOL sentences are two-valued---they must be true or false.
This means that the notions of satisfiability and validity in a model coincide.
However, in Matching logic patterns evaluate to a subset of the carrier set.
We say a pattern is satisfiable in a model when its evaluation is non-empty,
and that it is valid when its evaluation is the entire carrier set.
In particular, even for closed patterns both a pattern and its negation may be satisfiable.
For example, the model $\mathbb N$ with the usual interpretations,
satisfies both $\mathsf{even}$ and $\lnot \mathsf{even}$ (i.e. the set of odd naturals) but neither are valid.

\begin{definition}[Satisfiability in a model]
We say a $\Sigma$-model $M$ \emph{satisfies} a $\Sigma$-pattern
iff there is some evaluation $\rho$ and an element $m$
such that $m \in \evaluation{\phi}_{M,\rho}$.
A $\Sigma$-pattern $\phi$ is \emph{satisfiable} iff there is a model $M$ that satisfies $\phi$.
\end{definition}

\begin{definition}[Validity in a model]
We say a $\Sigma$-pattern is \emph{valid} in a $\Sigma$-model $M$
iff for all evaluations $\rho$, $\evaluation{\phi}_{M,\rho} = M$.
\end{definition}

Analogously to FOL, we may define theories in  matching logic.
Essentially, a theory is a set of patterns, called axioms, that are valid in a model.
A pattern is satisfiable modulo a theory if it is satisfiable in some model where all axioms are valid.

\begin{definition}[Satisfiability modulo theories]
Let $\Gamma$ be a set of $\Sigma$-patterns called \emph{axioms}.
We say $\phi$ is satisfiable modulo theory $\Gamma$ if there is a model $M$
such that each $\gamma$ in $\Gamma$ is valid and $M$ satisfies $\phi$.
\end{definition}

Definition (Validity modulo theories)
:   Let $\Gamma$ be a set of $\Sigma$-patterns called \emph{axioms}.
    We say $\phi$ is satisfiable modulo theory $\Gamma$
    if for all models $M$
    such that each $\gamma$ in $\Gamma$ is valid we have $\phi$ is valid in $M$.

Remark (A note about variants of matching logic)

:   In its original formulation, matching logic had a many-sorted flavor where each symbol and pattern had a fixed sort.
    While it is convenient to define models that are also many-sorted,
    in [@applicative-matching-logic] the authors point out that 
    the many-sorted setting actually becomes an obstacle when it comes to 
    more complex sort structures.
    Therefore, they proposed a much simpler, unsorted variant of matching logic called applicative matching logic (AML),
    where the many-sorted infrastructure is dropped and sorts are instead defined axiomatically.
    This also treated multi-arity applications, as syntactic sugar for nested applications.
    In this work, to maximize the expressivity of the fragment defined here
    while still avoiding the complexity of multiple sorts,
    we use a version of matching logic that sits between the two,
    allowing multi-arity applications, but without sorts.
    When we need to be explicit about this distinction, we will refer to this as \emph{polyadic matching logic}.
    <!--
    In Section~\ref{sec:examples}, we show that the results presented here also apply to the many-sorted variant,
    and to AML as well.
    -->
    For the rest of this document unless explicitly mentioned,
    we will use pattern, model, etc, to refer to those concepts in polyadic matching logic
    although the same terms may be used in other variants of matching logic.

## Fragments and Meta-Properties

In general, matching logic's power and expressivity entails
that the logic as a whole does not have some desirable properties.
For example, because it subsumes first-order logic, the satisfiability problem must be undecidable.
Further, because we can precisely pin down the standard model of the natural
numbers using the fixedpoint operator, by `G\"odel`{=tex}'s incompleteness theorem, it
must also be incomplete.

When studying such properties in the context of matching logic, we must thus restrict ourselves to subsets of matching logic.
In this section, we shall formally define what we mean by a "fragment" of matching logic,
and define some properties we care about.

Definition (Fragments of matching logic)
:   A *fragment of matching logic* is a pair $(\PP, \TT)$
    where $\PP$ is a set of patterns and $\TT$ is a set of theories.
    We say a pattern $P$ is in a fragment if $P \in \PP$,
    and a theory $\Gamma$ is in a fragment if $\Gamma \in \TT$

Fragments may be defined with any number of criteria,
including the restrictions on
the use of quantifiers and fixedpoints,
number and arity of symbols,
the number of axioms,
quantifier alternation and so on.

We will now define the properties of fragments of matching logic that we will study in this document.

Definition (Decidable fragment)

:   A fragment of matching logic, $(\PP, \TT)$, is *decidable*
    if there is an algorithm for deterimining the satisfiability of any pattern $P \in \PP$ in any theory $\Gamma \in \TT$ in the fragment.

Notice that if $\PP$ is closed under negation, then the validity problem for a decidable fragment is also decidable.

For proving the decidability of some fragments in this paper, we rely on a more specific property called the small-model property.
This property says that every $\Gamma$-satisfiable pattern in a fragment has a model bound by a computable function on the size of the pattern.
Formally:

Definition (Small-model property)
:   A fragment of matching logic, $(\PP, \TT)$, has the small-model property iff for every pattern $P \in \PP$ in every theory $\Gamma \in \TT$
    if $P$ is $\Gamma$-satisfiable then, there is some model $M \satisfies \phi$ whose size is bound by a computable function $f$ on the size of $\phi$.
    That is, $\size{M} \le f(\size{\phi})$.

The small-model property implies that a fragment is decidable since one may simply
enumerate all models of size up to $f(\size{\phi})$ and evaluations
and check satisfiablility in each of them.
The small-model property is a stonger version of another interesting property, called the finite-model property:

Definition (Finite-model property)
:   A fragment of matching logic, $(\PP, \TT)$, has the finite-model property iff for every pattern $P \in \PP$ in every theory $\Gamma \in \TT$
    if $P$ is $\Gamma$-satisfiable then, there is some model $M \satisfies \phi$ with finite size.

The finite-model property and decidablity are independent in the sense that a
fragment may have the finite model property and yet be undecidable, or be
decidable despite being infinite.

In the next sections,
we will define some fragments and prove some properties about them.

<!--
Finally, for the sake of completeness,
we also define fixedpoint-free matching logic,
and full matching logic that include all matching logic patterns.
Both these fragments subsume first-order logic and so are neither decidabile,
nor have the small- or finite-model properties.

Definition (The fixedpoint-free fragment)

:   The *fixedpoint-free fragment* of matching logic has:

    \begin{align*}
    \PP &= \left\{\begin{array}{l}\text{ patterns built from \structure{}, } \\
                \text{\logic{} and \quantification{}}
                  \end{array}\right\}\\
    \TT &= \{\emptyset\}
    \end{align*}

Definition (Full matching logic)

:   The fragment *full matching logic* has:

    \begin{align*}
    \PP &= \left\{\text{any matching logic pattern}\right\}\\
    \TT &= \{\emptyset\}
    \end{align*}

Let us consider, in addition, variants of these fragments that allow different cardinalites of axioms.
For a fragment $\FF$ that only allows empty theories,
we define the fragment $\FF$\fin{} (resp. $\FF$\inf{}) to mean the fragment $(\PP, \TT)$
with $\PP$ the same as in $\FF$ and $\TT$ the set of theories with axioms in $\PP$
and finite (resp. recursively enumerable) axioms.

In the example below, we show that even the most basic fragment with infinite axioms
do not possess the finite-model property (and therefore the small-model property).

\begin{example}\label{ex:modal-inf-infinite}
Consider a signature that contains one sort,
one constant symbol $z$, and two unary symbol $s$ and $f$.
We write $s^0(z)$ to mean $z$ and $s^{n+1}(z)$ to mean $s(s^n(z))$ for $n \ge 1$.
Let
$\Gamma = \{ f(s^n(z)) \mid n \in \N{} \} \union \{ \neg ( s^n(z) \wedge s^m(z) ) \mid m,n \in \N{}, m \neq n \}$
be an infinite theory.
Then there exists a model $M_0$ satisfying $\Gamma$
and for any $M$ satisfying $\Gamma$, we have that $M$ is infinite.
\end{example}
Proof

:   We first prove that $M$ is infinite for any $M$ satisfying $\Gamma$.
    Let $z_M \subseteq M$ and $s_M,f_M \colon M \to \PP{M}$ be the 
    interpretations of $z$, $s$, and $f$ in $M$. 
    Since $M$ satisfies $f(s^n(z))$ for every $n \in \N$,
    and $f(s^n(z))$ is a sentence, we have $\evaluation{f(s^n(z))} = M$.
    This implies that $\evaluation{s^n(z)} \neq \emptyset$.
    Because $M$ satsfies $\neg (s^m(z) \wedge s^n(z))$ for every $m,n$ with $m \neq n$,
    we have $\evaluation{\neg (s^m(z) \wedge s^n(z))} = M \setminus (\evaluation{s^m(z)} \cap 
    \evaluation{s^n(z)})$ = M, which implies that
    $\evaluation{s^m(z)} \cap \evaluation{s^n(z)} = \emptyset$ for every $m,n$ with $m \neq n$.
    Therefore, $\evaluation{s^0(z)}, \evaluation{s^1(z)}, \evaluation{s^2(z)},\dots$ is a sequence of
    nonempty, pairwisely distinct subsets of $M$.
    And thus, $M$ is infinite.

    Now, we construct a model $M_0$ satisfying $\Gamma$.
    Let $\N$ be domain of $M_0$.
    Let $z_{M_0} = \{ 0 \}$,  $s_{M_0}(n) = \{ n+1 \}$, and $f_{M_0}(n) = \N$ for
    $n \in \N$.
    By mathematical induction, we can prove that
    $\evaluation{s^m(z)} = \{ m \}$ for all $m \in \N$.
    By [@def:semantics], we conclude that $M_0$ satisfies $\Gamma$.
-->

We summarize the meta properties of these fragments in Table \ref{table:status-quo}.

\begin{table*}
\small
\begin{tabular} {|r||l|l|l||l|l|l||l|l|l|}
\hline
              & \multicolumn{3}{c||}{Empty theories}                                                                                    &\multicolumn{3}{c||}{Finite theories}                                                                                                  & \multicolumn{3}{c|}{Recursively enumerable theories}  \\
\hline
\diagbox[height=2em,width=9em]{Property}{Fragment}
              &  Modal                                  & Quant. free                       & Guarded                                   &  Modal                                      & Quant. free                                 & Guarded                                   &  Modal                                  & Quant. free & Guarded                                   \\
\hline\rule{0pt}{3ex}
Small-model   & \cmark[Sec.\ref{sec:modal-fragment}]    & \cmark[Sec.\ref{sec:qf-fragment}] & \xmark                                    & \qmark                                      & \qmark                                      & \xmark                                    & \xmark                                  & \xmark      & \xmark                                    \\
Finite-model  & \cmark                                  & \cmark                            & \xmark[Ex.\ref{ex:naturals-are-guarded}]  & \qmark                                      & \qmark                                      & \xmark                                    & \xmark[Ex. \ref{ex:modal-inf-infinite}] & \xmark      & \xmark                                    \\
Decidability  & \cmark                                  & \cmark                            & \cmark                                    & \cmark[Sec.\ref{sec:guarded-fragment}]      & $\dagger$[Sec.\ref{sec:guarded-fragment}]   & \cmark[Sec.\ref{sec:guarded-fragment}]    & \xmark\cite{urquhart1981}               & \xmark      & \xmark                                    \\
\hline
\end{tabular}
\caption{
  \emph{The status quo:} Fragments of matching logic and their meta-prorties. \newline
  $\dagger$ This result has only been proved when there are no free set variables in axioms. \newline
}
\label{table:status-quo}
\end{table*}

