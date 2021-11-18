\section{Matching Logic Preliminaries}\label{sec:ml-prelims}

Matching logic was first proposed in \cite{matchinglogiclmcs} as a unifying logic for specifying and reasoning about programming languages.
Matching logic formulae are called \emph{patterns}
and have a ``pattern matching'' semantics,
in the sense that each pattern represents the set of elements that "match" it.
For example, $\mathsf{cons}(42, x)$ matches lists whose first element is $42$,
while $\mathsf{prime} \land \mathsf{even}$ matches the natural $2$ (assuming axiomatizations for $\mathsf{cons}$, $\mathsf{prime}$, and $\mathsf{even}$).
Patterns are built using four components:
\structure{} for building terms,
\logic{} for the usual logical connectives, 
\quantification{} for first-order quantification, and
\fixedpoint{} for building least and greatest fixedpoints.

\subsection{Matching Logic Syntax}

An important feature of matching logic is that it makes no distinction between terms and formula.
This flexibility makes many important concepts easily definable in matching logic,
and allows for awkwardness free encodings of various abstractions and logics possible.
For example, unification may be characterized by conjuncting two pattern built from constructors.


For a set, $\EVar$ of \emph{element variables} ($x, y, z, \ldots$), 
and        $\SVar$ of \emph{set variables} ($X, Y, Z, \ldots$), we define the syntax of matching logic below.

\begin{definition}[Matching logic signatures]
A matching logic \emph{signature}, $\Sigma$ is a set of symbols with an associated arity.
Symbols with an arity of zero are called \emph{constants}.
\end{definition}

\begin{definition}[Patterns]
Given a signature $\Sigma$, a countable set of element variables $\EVar$ and of set variables $\SVar$,
a matching logic \emph{pattern} is built recursively using the following grammar:
\begin{align*}
\phi:=  \underbrace{\sigma(\phi_1, \dots, \phi_n)}      _\text{\structure{}}
  \mid  \underbrace{\phi_1 \land \phi_2 \mid \lnot \phi}_\text{\logic{}}
  \mid  \underbrace{x \mid \exists x \ldotp \phi}       _\text{\quantification}
  \mid  \underbrace{X \mid     \mu X \ldotp \phi}       _\text{\fixedpoint{}}
\end{align*}
where $x \in \EVar$, $X \in \SVar$ and $\sigma \in \Sigma$ has arity $n$, and $X$ occurs only positively in $\mu X\ldotp \phi$. That is, $X$ may only occur under an even number of negations in $\phi$. 
\end{definition}
We assume the standard notions for free variables, $\alpha$-equivalence, and capture-free substitution $\phi[\psi/x]$
and allow the usual syntactic sugar:
\begin{align*}
                       \top &\equiv \exists x \ldotp x &
         \phi_1 \lor \phi_2 &\equiv \lnot(\lnot\phi_1 \land \lnot\phi_2) &
      \forall x \ldotp \phi &\equiv \lnot \exists x \ldotp \phi \\
                       \bot &\equiv \lnot \top &
    \phi_1 \limplies \phi_2 &\equiv \lnot \phi_1 \lor \phi_2 &
      \nu X \ldotp \phi &\equiv \lnot \mu X \ldotp \lnot \phi[\lnot X/X]
\end{align*}
$\sigma(\phi_1, \dots, \phi_n)$ are called applications. 
We will use $\sigma$ instead of $\sigma()$ for constants.
\hypertarget{semantics-of-polyadic-matching-logic}{%
\subsection{Semantics of Matching Logic}\label{semantics-of-matching-logic}}

Unlike in FOL, matching logic patterns are interpreted as a set of elements in a model rather than a single element.
Intuitively, the interpretation is the set of elements that match a pattern.
For example, the constant $\mathsf{even}$ might have as interpretation the set of all odd naturals,
while $\mathsf{greaterThan}(3)$ may be interpreted as all integers greater than $3$.
Function symbols may be considered a special case of this, where the interpretation is a singleton set.
Logical constructs are thought of as set operations over matched elements
-- for example, $\phi \land \psi$ is interpreted as the intersection of elements matched by $\phi$ and $\psi$,
while $\lnot \phi$ matches all elements \emph{not} matched by $\phi$.
An existential $\exists x \ldotp \phi(x)$ is interpreted as the union of all patterns matching $\phi(x)$ for all valuations of $x$.
$\mu X \ldotp \phi(X)$ matches the \emph{least} set $X$ such that $X$ and $\phi(X)$ match the same elements.
An important point to note here is that element variables have as denotation exactly a single element,
whereas set variables may be interpreted as any subset of the carrier set.

\begin{definition}[$\Sigma$-models]
Given a signature $\Sigma$, a $\Sigma$-model is a tuple $(\mathbb M, \{ \sigma_M \}_{\sigma \in \Sigma} )$
where $\mathbb M$ is a set of elements called the carrier set,
  and $\sigma_M : M^n \to \powerset(M)$ is the interpretation of the symbol $\sigma$ with arity $n$ into the powerset of $M$.
\end{definition}

We use $M$ to denote both the model $M$, and it's carrier set, $\mathbb M$.
We also tacitly use $\sigma_M$ to denote the pointwise extension, $\sigma_M : \powerset(M)^n \to \powerset(M)$,
defined as $\sigma_M(A_1,\dots,A_n) \mapsto \Union_{a_i\in A_i} \sigma_M(a_1,\dots,a_n)$
for all sets $A_i \subseteq M$.

\begin{definition}[Semantics of matching logic]
\label{def:semantics}
Let $\rho : \EVar{} \union \SVar{} \to \powerset(M)$ be a function such that $\rho(x)$ is a singleton set when $x \in \EVar$,
called an evaluation.
Then, the denotation of a pattern $\phi$, written $\denotation{\phi}_{M,\rho}$ is defined inductively by:
\begin{align*}
\denotation{\sigma(\phi_1, \ldots, \phi_n)}_\rho &= \sigma_M(\denotation{\phi_1}, \ldots, \denotation{\phi_n}) \text{ for $\sigma$ of arity $n$} \\
\denotation{\phi_1 \land \phi_2}_\rho            &= \denotation{\phi_1}_\rho \intersection \denotation{\phi_2}_\rho \\
\denotation{\lnot \phi}_\rho                     &= M\setminus \denotation{\phi}_\rho \\ 
\denotation{x}_\rho                              &= \rho(x) \text{ for } x \in \EVar \\
\denotation{\exists x \ldotp \phi}_\rho          &= \bigcup_{a \in M}  \denotation{\phi}_{\rho[a/x]}\\
\denotation{X}_\rho                              &= \rho(X) \text{ for } X \in \SVar  \\
\denotation{\mu X \ldotp \phi}_\rho              &= \mathsf{LFP}(\FF) \text{ where } \FF(A) = \denotation{\phi}_{\rho[A/X]} \text{ for } A \subseteq M
\end{align*}
\end{definition}

As seen, $\sigma$ is interpreted as a relation. 
Its interpretation $\sigma_M$ is not a function in the standard FOL sense.
We say that $\sigma_M$ is \emph{functional}, if:
\begin{equation}\tag{functional-symbol}
\size{\sigma_M(a_1,\dots,a_n)} = 1  \quad \text{for all $a_1 \in  M_{s_1}, \dots, a_n \in M_{s_n}$}\label{functional}
\end{equation}

\hypertarget{satisfiability-and-validity}{%
\subsection{Satisfiability and
Validity}\label{satisfiability-and-validity}}

In this subsection, formally define satisfiability and validity in matching logic\footnote{
Note that our definitions differ from \cite{matchinglogiclmcs} where only validity in a model is defined (but referred to as satisfiability).
We avoid using the $\models$ notation to avoid confusion between the two.
}.
Because of the powerset interpretation of patterns, the notions of satisfiability and validity differ
subtly from those in FOL.
Because the interpretations of FOL sentences are two-valued -- they must be true
or false -- the notions of satisfiability and validity in a model coincide.
Matching logic patterns evaluate to a subset of the carrier set.
We say a pattern is satisfiable in a model when its evaluation is non-empty,
and that it is valid when its evaluation is the entire carrier set.
For example, the model $\mathbb N$ with the usual interpretations,
satisfies both $\mathsf{even}$ and $\lnot \mathsf{even}$ (i.e. the set of odd naturals) but neither are valid.

\begin{definition}[Satisfiability in a model]
We say a $\Sigma$-model $M$ \emph{satisfies} a $\Sigma$-pattern
iff there is some evaluation $\rho$ and an element $m$
such that $m \in \denotation{\phi}_{M,\rho}$.
A $\Sigma$-pattern $\phi$ is \emph{satisfiable} iff there is a model $M$ that satisfies $\phi$.
\end{definition}

\begin{definition}[Validity in a model]
We say a $\Sigma$-pattern is \emph{valid} in a $\Sigma$-model $M$
iff for all evaluations $\rho$, $\denotation{\phi}_{M,\rho} = M$.
\end{definition}

Analogously to FOL, we may define theories in  matching logic.
Essentially, a theory is a set of patterns, called axioms, that are valid in a model.
A pattern is satisfiable modulo a theory if it is satisfiable in some model where all axioms are valid.

\begin{definition}[Satisfiability modulo theories]
Let $\Gamma$ be a set of $\Sigma$-patterns called \emph{axioms}.
We say $\phi$ is satisfiable modulo theory $\Gamma$ if there is a model $M$
such that each $\gamma$ in $\Gamma$ is valid and $M$ satisfies $\phi$.
\end{definition}

\subsection{Fragments and Meta-Properties}

In general, matching logic's power means that the logic as a whole does not have several desirable properties.
For example, because it subsumes first-order logic, the satisfiability problem must be undecidable.
Further, because we can precisely pin down the standard model of the natural
numbers using the fixedpoint operator, by G\"odel's incompleteness theorem, it
must also be incomplete.
When studying such properties in the context of matching logic, we must thus restrict ourselves to subsets of matching logic.
In this section, we shall formally define what each of these properties mean within a subsets, or "fragment", of matching logic.

\begin{definition}[Fragments of matching logic]
A \emph{fragment of matching logic} is a pair $(\PP, \TT)$
where $\PP$ is a set of patterns and $\PP$ is a set of theories.
We say a pattern $P$ is in a fragment if $P \in \PP$,
and a theory $\Gamma$ is in a fragment if $\Gamma \in \TT$
\end{definition}

Fragments may be defined with any number of criteria,
including the restrictions on
the use of quantifiers and fixedpoints,
number and arity of symbols,
the number of axioms,
quantifier alternation and so on.

We will now define the properties of fragments of matching logic that we will study in this document.

\begin{definition}[Decidable fragments]
A fragment of matching logic, $(\PP, \TT)$, is \emph{decidable} if deterimining the
satisfiability of any pattern $P \in \PP$ in any theory $\Gamma \in \TT$ is decidable.
\end{definition}

Notice that if the $\PP$ is closed under negation, then the validity problem for a decidable fragment is also decidable.

For proving the decidability of some fragments in this paper, we rely on a more specific property called the small-model property.
This property says that every $\Gamma$-satisfiable pattern in a fragment has a model bound by a computable function on the size of the pattern.
Formally,
\begin{definition}[Small-model property]
A fragment of matching logic, $(\PP, \TT)$, has the small-model property iff for every pattern $P \in \PP$ in every theory $\Gamma \in \TT$
if $P$ is $\Gamma$-satisfiable then, there is some model $M \satisfies \phi$ whose size is bound by a computable function $f$ on the size of $\phi$ -- $\size{M} \le f(\size{\phi})$.
\end{definition}

The small-model property implies that a fragment is decidable since one may simply enumerate all models and evaluations for models up to a particular size to prove its decidablity.
The small-model property is a stonger version of another interesting property, called the finite-model property:

\begin{definition}[Finite-model property]
A fragment of matching logic, $(\PP, \TT)$, has the finite-model property iff for every pattern $P \in \PP$ in every theory $\Gamma \in \TT$
if $P$ is $\Gamma$-satisfiable then, there is some model $M \satisfies \phi$ with finite size.
\end{definition}

The finite-model property and decidablity are independent in the sense that a fragment may have the finite model property and yet be undecidable,
or be decidable despite being infinite.

\subsection{The Status-Quo}\label{the-status-quo}

We will now define some important fragments and enumerate the know results about their meta-properties.

\begin{definition}[The modal fragment]
The \emph{modal fragment} of matching logic has \\$\PP = \{\text{ patterns built from \structure and \logic }\}$,
and $\TT = \{\{\}\}$.
\end{definition}

That is, the modal fragment of matching logic only allows quantifier- and fixedpoint-free patterns and the empty theory.
This fragment may be regarded as a polyadic multi-arity variant of modal logic.
In Section~\ref{sec:decidable-modal-fragment}, we show that this fragment has the small-model property (and therefore is also decidable and has the finite-model property).

The quantifier free fragment is less restrictive, allowing fixedpoints in patterns as well:

\begin{definition}[The quantifier-free fragment]
The \emph{quantifier-free fragment} of matching logic has \\$\PP = \{\text{ patterns built from \structure, \logic and \fixedpoint }\}$,
and $\TT = \{\{\}\}$.
\end{definition}

This fragment also exhibits the small-model property as proved in Section~\ref{sec:decidable-qf-fragment}.

We shall only define the next fragment, called guarded matching logic, informally here. We shall describe it in more depth in Section~\ref{sec:decidable-guarded-fragment}.
This fragment allows both quantification and fixedpoints. However, quantifiers must be of the form:
\begin{align*}
\forall \bar x \ldotp \alpha(\bar x, \bar y) &\implies \phi(\bar x, \bar y) \\
\exists \bar x \ldotp \alpha(\bar x, \bar y) &\land    \phi(\bar x, \bar y)
\end{align*}
where $\alpha$ is a conjunction of applications and every pair of free variables in $\phi$ are arguments of some application in $\alpha$.
This fragment possesses neither the small-model property nor the less strict finite-model property and yet is decidable.

Finally, for the sake of completeness,
we also define fixedpoint-free matching logic,
and full matching logic, that includes all matching logic patterns and theories.
Both these fragments subsume first-order logic and so are neither decidabile,
nor have the small- or finite-model properties.

Let us consider, in addition, variants of these fragments that allow different cardinalites of axioms.
For a fragment $\FF$ that only allows empty theories,
we define the fragment $\FF$\fin (resp. $\FF$\inf) to mean the fragment $(\PP, \TT)$
with $\PP$ the same as in $\FF$ and $\TT$ the set of theories with axioms in $\PP$
and finite (resp. recursively enumerable) axioms.
For a fragment $\FF$ that allows axioms, we define $\FF_\emptyset$ to only allow empty theories.
Similarly, $\FF$\inf and $\FF$\fin place or loosen the restrictions on the cardinality of the axioms.

In the example below, we show that even the most basic fragment with infinite axioms
do not possess any of the properties we consider.

\begin{example}\label{ex:modal-inf-infinite}
Consider a signature that contains one sort,
one constant symbol $z$, and two unary symbol $s$ and $f$.
We write $s^0(z)$ to mean $z$ and $s^{n+1}(z)$ to mean $s(s^n(z))$ for $n \ge 1$.
Let
$\Gamma = \{ f(s^n(z)) \mid n \in \N{} \} \union \{ \neg ( s^n(z) \wedge s^m(z) ) \mid m,n \in \N{}, m \neq n \}$
be an infinite theory.
Then there exists a model $M_0$ such that $M_0 \vDash \Gamma$ and for any $M 
\vDash \Gamma$, we have that $M$ is infinite.
\end{example}
\begin{proof}
We first prove that $M$ is infinite for any $M \vDash \Gamma$.
Let $z_M \subseteq M$ and $s_M,f_M \colon M \to \PP{M}$ be the 
interpretations of $z$, $s$, and $f$ in $M$. 
Since $M \vDash f(s^n(z))$ for every $n \in \N$,
and $f(s^n(z))$ is a sentence, we have $\denotation{f(s^n(z))} = M$.
This implies that $\denotation{s^n(z)} \neq \emptyset$.
Because $M \vDash \neg (s^m(z) \wedge s^n(z))$ for every $m,n$ with $m \neq n$,
we have $\denotation{\neg (s^m(z) \wedge s^n(z))} = M \setminus (\denotation{s^m(z)} \cap 
\denotation{s^n(z)})$ = M, which implies that
$\denotation{s^m(z)} \cap \denotation{s^n(z)} = \emptyset$ for every $m,n$ with $m \neq n$.
Therefore, $\denotation{s^0(z)}, \denotation{s^1(z)}, \denotation{s^2(z)},\dots$ is a sequence of
nonempty, pairwisely distinct subsets of $M$.
And thus, $M$ is infinite.

Now, we construct a model $M_0$ such that $M_0 \vDash \Gamma$.
Let $\N$ be domain of $M_0$.
Let $z_{M_0} = \{ 0 \}$,  $s_{M_0}(n) = \{ n+1 \}$, and $f_{M_0}(n) = \N$ for
$n \in \N$.
By mathematical induction, we can prove that
$\denotation{s^m(z)} = \{ m \}$ for all $m \in \N$.
By Definition~\ref{def:semantics}, we conclude that $M_0 \vDash \Gamma$.
\end{proof}

We summarize the meta properties of these fragments in Table \ref{table:status-quo}.

\begin{table*}
\small
\begin{tabular} {|r||l|l|l|l|l|}
\hline
\diagbox[height=2em,width=9em]{Property}{Fragment}
              &  Modal                                            & Quantifier-free                                   & Guarded                                                & Fixedpoint-free      & Full    \\
\hline
\multicolumn{5}{c}{Empty theories}\\
\hline
\rule{0pt}{3ex}Small-model
              & \cmark[Sec.\ref{sec:decidable-modal-fragment}]    & \cmark[Sec.\ref{sec:decidable-qf-fragment}]       & \xmark                                                 & \xmark               & \xmark  \\
Finite-model  & \cmark                                            & \cmark                                            & \xmark[Ex.\ref{ex:naturals-are-guarded}]               & \xmark               & \xmark  \\
Decidability  & \cmark                                            & \cmark                                            & \cmark                                                 & \xmark               & \xmark  \\
\hline
\multicolumn{5}{c}{Finite theories}\\
\hline
Small-model   & ?                                                 & ?                                                 & \xmark                                                 & \xmark               & \xmark  \\
Finite-model  & ?                                                 & ?                                                 & \xmark                                                 & \xmark               & \xmark  \\
Decidability  & \cmark[Sec.\ref{sec:decidable-guarded-fragment}]  & \cqmark$\dagger$[Sec.\ref{sec:decidable-guarded-fragment}] & \cmark[Sec.\ref{sec:decidable-guarded-fragment}]       & \xmark               & \xmark  \\
\hline
\multicolumn{5}{c}{Recursively enumerable theories}\\
\hline
Small-model   &  \xmark                                           & \xmark                                            & \xmark                                                 & \xmark               & \xmark  \\
Finite-model  &  \xmark[Ex. \ref{ex:modal-inf-infinite}]          & \xmark                                            & \xmark                                                 & \xmark               & \xmark  \\
Decidability  &  \xmark\cite{urquhart1981}                        & \xmark                                            & \xmark                                                 & \xmark               & \xmark  \\
\hline
\end{tabular}
\caption{
  \emph{The status quo:} Fragments of matching logic and their meta-prorties. \newline
  $\dagger$ This result has only been proved when there are no free set variables in axioms. \newline
}
\label{table:status-quo}
\end{table*}

\subsection{A note about variants of matching logic}
In its original formulation, matching logic had a many-sorted flavor where each symbol and pattern had a fixed sort.
While it is convenient to define models
that are also many-sorted, the authors of \cite{applicative-matching-logic} pointed out that 
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
In Section~\ref{sec:examples}, we show that the results presented here also apply to the many-sorted variant,
and to AML as well.
For the rest of this document unless explicitly mentioned,
we will use pattern, model, etc, to refer to those concepts in polyadic matching logic
although the same terms may be used in other variants of matching logic.

