# The Modal Fragment {#sec:modal-fragment}

Our goal is to show the *small model property* of the modal fragment of matching logic,
which states that if $\psi$ is *satisfiable*,
then there exists a (finite) model $M$ with size bounded by a computable
function $f(\size{\psi})$ on the size of $\psi$
such that $\evaluation{\phi}_M \neq \emptyset$
(or equivalently, there is an element 
$a \in M$ such that $a \vDash \psi$ in $M$).

The SMP implies decidability,
because one can exhaustively  search for a model for $\psi$
up to the size bound $f(\size{\psi})$.

Definition (Closure)
:   Given $\psi$, let its *closure* $C(\psi)$ be the smallest set
    that contains all its sub-patterns and their negations.

The size of $C(\psi)$, written $\size{C(\psi)}$,
is defined in the usual way and smaller than twice the size of $\psi$.

Definition ($\Gamma$-indistinguishable)

:   Given $\Gamma$ and $M$, we say that two elements $a,b \in M$ are
    *$\Gamma$-indistinguishable*, written $a \cong_\Gamma b$ or simply
    $a \cong b$ when $\Gamma$ is understood, 
    if $a \vDash \psi$ iff $b \vDash \psi$ for all $\psi \in \Gamma$.

Lemma
:   $\cong_\Gamma$ is an equivalence relation on $M$.

Proof
:   By directly applying the definition.

Definition ($\Gamma$-equivalence classes){#def:eqclass}

:   We use $[a]_\Gamma = \{b \in M \mid a \cong_\Gamma b\}$ to denote the 
    equivalence class of $a \in M$. 
    We use $[A]_\Gamma = \{ [a]_\Gamma \mid a \in A \}$ to denote the set of 
    equivalence classes of all elements in $A \subseteq M$.

In the following, we drop $\Gamma$ when it is understood.

\begin{definition}\label{def:filtered}
Given $\psi$ and $M$, 
we consider $C(\psi)$-indistinguishability $\cong_{C(\psi)}$ or simply $\cong$.
Let $[a]$ be the equivalence class of 
$a \in M$.
Let the \emph{filtered model}
$[M]$ contain the following:
\begin{itemize}
\item the carrier set $[M]$;
\item the interpretation $\sigma_{[M]}\left([a_1],\dots,[a_n]\right) = 
[\sigma_M([a_1],\dots,[a_n])]$ for symbol $\sigma$ whose arity is $n$.
\end{itemize}
For any pattern $\phi$, we write $\phi_{[M]}$ to denote the 
interpretation of $\phi$ under any (irrelevant) valuation in $[M]$.  
\end{definition}

\begin{remark}
Note that $\sigma_{[M]}$ may not be functional, in the sense 
of~\eqref{functional}.
It can even evaluate to a set of more than one equivalent classes, 
even when $\sigma_M$ is functional.
\end{remark}

\begin{remark}
We emphasize that $[M]$ is indeed an ML model,
for which all it requires is a powerset interpretation of the symbols, 
as done in Definition~\ref{def:filtered}.
In fact, it is the nature of ML that makes this elegantly possible, because it 
allows symbols to be interpreted in the powerset.
The above construction would not work for FOL, for example, 
if $\sigma$ were a function symbol.
\end{remark}

\begin{remark}
We point out that $\sigma_{[M]}([a_1],\dots,[a_n])$ is not necessarily
equal to $[\sigma_M(a_1,\dots,a_n)]$. 
In general, $\phi_{[M]}$
is not necessarily equal to $[\phi_M]$ for arbitrary $\phi$.
Later, in Lemma~\ref{lem:filter}, we show that $\phi_{[M]} = [\phi_M]$ 
holds for a selection of patterns, namely those which are in $C(\psi)$.
\end{remark}


\begin{lemma}\label{lem:filter_size}
$[M]$ has at most $\sqrt{2^{\size{C(\psi)}}}$ elements.
\end{lemma}
\begin{proof}
For $a \in M$, define its \emph{indicator set}
$I(a) = \{\phi \in C(\psi) \mid a \vDash \phi \}$
as the set of patterns in $C(\psi)$ that are matched by $a$.
Enumerate all patterns in $C(\psi)$ as follows:
$\phi_1,\neg \phi_1,\dots,\phi_{\size{C(\psi)}/2},\neg 
\phi_{\size{C(\psi)}/2}$.
For any indicator set $I$ and for any $1 \le i \le \size{C(\psi)}/2$, 
one of the following holds:
\begin{enumerate}
\item $\phi_i \in I$ and $\neg \phi_i \not\in I$;
\item $\phi_i \not\in I$ and $\neg \phi_i \in I$.
\end{enumerate}
Therefore, the number of all indicator sets is bounded by
$2^{\size{C(\psi)}/2} = \sqrt{2^{\size{C(\psi)}}}$. 
By definition, $[a] = [b]$ iff $I(a) = I(b)$.
Therefore, the size of $[M]$ is bounded by
$\sqrt{2^{\size{C(\psi)}}}$.
\end{proof}

Note that $\size{C(\psi)} \le  2{\size{\psi}}$ under a reasonable choice of the 
size function.
Therefore,the space size of the filtered model $[M]$ is bounded by 
$\sqrt{2^{2\size{\psi}}} = 2^{\size{\psi}}$.

\begin{lemma}\label{lem:fl}
For any $\phi \in C(\psi)$, the following propositions are equivalent:
\begin{enumerate}
\item $\phi_{[M]} = [\phi_M]$;
\item $[a] \vDash \phi_{[{M}]}$ iff $a \vDash \phi_M$, for all $a \in M$.
\end{enumerate}
\end{lemma}
\begin{proof}
We first prove the easier direction, which is (2) implies (1).
We prove both $\phi_{[M]} \subseteq [\phi_M]$ and
$[\phi_M] \subseteq \phi_{[M]}$.
For $\phi_{[M]} \subseteq [\phi_M]$, let $[a] \in \phi_{[M]}$, i.e., 
$[a] \vDash \phi_{[M]}$.
By (2), $a \vDash \phi_M$, i.e., $a \in \phi_M$.
Therefore, $[a] \in [\phi_M]$.
This shows that $\phi_{[M]} \subseteq [\phi_M]$.
For $[\phi_M] \subseteq \phi_{[M]}$, 
let $[a] \in [\phi_M]$.
This means that there exists $a' \in \phi_M$, i.e., $a' \vDash \phi_M$, 
such that $[a] = [a']$.
By (2), $[a'] \vDash \phi_{[M]}$, and therefore
$[a] \vDash \phi_{[M]}$, i.e., $[a] \in \phi_{[M]}$.
This shows that $[\phi_M] \subseteq \phi_{[M]}$.
In conclusion, we prove that
$[\phi_M] = \phi_{[M]}$. Therefore, (2) implies (1).

We now prove (1) implies (2).
For the ``if'' direction, let $a \vDash \phi_M$, i.e., $a \in \phi_M$.
Therefore, $[a] \in [\phi_M]$, and by (1), $[a] \in \phi_{[M]}$.
Therefore, $[a] \vDash \phi_{[M]}$.
For the ``only if'' direction, let $[a] \vDash \phi_{[M]}$, i.e.,
$[a] \in \phi_{[M]}$.
By (1), $[a] \in [\phi_M]$, which means that there exists $a' \in \phi_M$,
i.e., $a' \vDash \phi_M$, 
such that $[a] = [a']$.
Since $\phi \in C(\psi)$, and $a,a'$ are $C(\psi)$-indistinguishable, 
we have $a \vDash \phi_M$.
Therefore, (1) implies (2).
\end{proof}

\begin{remark}
The condition $\phi \in C(\psi)$ is necessary in Lemma~\ref{lem:fl}.
It is used in proving that (1) implies (2), for the ``only if'' direction.
\end{remark}

The following is the key lemma that links the semantics 
between the original and the filtered models.

\begin{lemma}\label{lem:filter}
For every $\phi \in C(\psi)$,  we have 
$\phi_{[M]} = [\phi_M]$.
\end{lemma}
\begin{proof}
We do structural induction on $\phi$, where the only nontrivial case
is the last case, when $\phi$ is a symbol application.

($\phi$ is $c$).
We have that $c_{[M]} = \{ [a] \mid a \in c_M \} = [c_M]$.

($\phi$ is $\phi_1 \wedge \phi_2$).
By Lemma~\ref{lem:fl}, we need to prove that
$[a] \vDash (\phi_1 \wedge \phi_2)_{[M]}$ iff $a \vDash (\phi_1 \wedge 
\phi_2)_M$ for all $a \in M$.
We have the following reasoning:
\begin{align*}
& [a] \vDash (\phi_1 \wedge \phi_2)_{[M]} \\
\text{iff}\quad & [a] \vDash (\phi_1)_{[M]} \cap (\phi_2)_{[M]}\\
\text{iff}\quad & [a] \vDash (\phi_1)_{[M]} \text{ and } 
[a] \vDash (\phi_2)_{[M]} \\
\text{iff}\quad & a \vDash (\phi_1)_M \text{ and } a \vDash (\phi_2)_M
&&\text{by inductive hypotheses} \\
&&&\text{and Lemma~\ref{lem:fl}} \\
\text{iff}\quad & a \vDash (\phi_1)_M \cap (\phi_2)_M \\
\text{iff}\quad & a \vDash (\phi_1 \wedge \phi_2)_M
\end{align*}

($\phi$ is $\neg \phi_1$).
By Lemma~\ref{lem:fl}, we need to prove that
$[a] \vDash (\neg \phi_1)_{[M]}$ iff
$a \vDash (\neg \phi_1)_M$ for all $a \in M$.
We have the following reasoning:
\begin{align*}
& [a] \vDash (\neg \phi_1)_{[M]} \\
\text{iff}\quad & [a] \not\vDash (\phi_1)_{[M]} \\
\text{iff}\quad & a \not\vDash (\phi_1)_M
&&\text{by inductive hypotheses} \\
&&&\text{and Lemma~\ref{lem:fl}} \\
\text{iff}\quad & a \vDash (\neg \phi_1)_M
\end{align*}

($\phi$ is $\sigma(\phi_1,\dots,\phi_n)$).
This is the only nontrivial case. 
Note that by induction hypotheses, we have
$(\phi_i)_{[M]} = [(\phi_i)_M]$ for every $1 \le i \le n$.
We prove $(\sigma(\phi_1,\dots,\phi_n))_{[M]}
= [(\sigma(\phi_1,\dots,\phi_n))_M]$ by deriving both sides.
Firstly, we have
\begin{align}
[(\sigma(\phi_1,\dots,\phi_n))_M]
&= [\sigma_M((\phi_1)_M,\dots,(\phi_n)_M)] \\
&= \left[\bigcup_{a_i \in (\phi_i)_M, 1 \le i \le 
n}\sigma_M(a_1,\dots,a_n)\right] \label{n}
\end{align}
Secondly, we have
\begin{align}
(\sigma(\phi_1,\dots,\phi_n))_{[M]}
&= \sigma_{[M]}((\phi_1)_{[M]},\dots,(\phi_n)_{[M]}) \\
&= \sigma_{[M]}([(\phi_1)_M],\dots,[(\phi_n)_M]) \\
&= \bigcup_{a_i \in (\phi_i)_M, 1 \le i \le n}
   \sigma_{[M]}([a_1],\dots,[a_n]) \\
&= \bigcup_{a_i \in (\phi_i)_M, 1 \le i \le n}
   \left[ \sigma_M([a_1],\dots,[a_n]) \right] \\
&= \left[  \bigcup_{a_i \in (\phi_i)_M, 1 \le i \le n} 
\sigma_M([a_1],\dots,[a_n]) \right] \label{push}
\end{align}
For any $\phi$, we use $a \cong a' \in (\phi)_M$ to mean that
$a,a' \in (\phi)_M$ and $a \cong a'$.
Then, we continue the above reasoning from~\eqref{push}
\begin{align}
\cdots &= \left[ \bigcup_{a_i \cong a'_i\in (\phi_i)_M, 1 \le i 
\le n} \sigma_M(a'_1,\dots,a'_n) \right] \\
&= \left[ \bigcup_{a'_i\in (\phi_i)_M, 1 \le i 
\le n} \sigma_M(a'_1,\dots,a'_n) \right]
\end{align}
which is equal to~\eqref{n}.
\end{proof}

\begin{theorem}\label{thm:ooosmp}
ML$^{\not\exists,\not\mu}$ has small model property (SMP). Formally, 
every satisfiable pattern $\psi$, without variables, $\exists$, or $\mu$,
has a model with at most ${2^{\size{\psi}}}$ 
elements.
\end{theorem}
\begin{proof}
Let $M$ and $a$ satisfy $a \vDash \psi$.
Applying Lemma~\ref{lem:filter} on $\psi$ and $a$,
we have that $[a] \vDash \phi$, in the filter model $[M]$,
which has at most ${2^{\size{\psi}}}$ 
elements, by Lemma~\ref{lem:filter_size}.
\end{proof}

\begin{theorem}\label{thm:ooodec}
ML$^{\not\exists,\not\mu}$ is decidable.
Formally, given a pattern $\psi$ without element variables, $\exists$, or 
$\mu$, determining whether $\psi$ is satisfiable is decidable.
\end{theorem}
\begin{proof}
By Theorem~\ref{thm:ooosmp}, $\psi$ is satisfiable iff
there exist a model of size at most ${2^{\size{\psi}}}$.
Given any finite size $s$, there are only finitely many models of size $s$,
if we consider only the interpretations of the finitely many symbols that do 
occur in $\psi$.
Therefore, we can use a brute force procedure to enumerate
all possible models (with interpretations of symbols occur in $\psi$)
up to size ${2^{\size{\psi}}}$ and to check the satisfiability.
\end{proof}

We can extend Theorems~\ref{thm:ooosmp} and~\ref{thm:ooodec}
to patterns that also have \emph{set variables},
by replacing them by constant symbols.
Note that all set variables are free variables, because there is no binder 
$\mu$ in the fragment.

\begin{theorem}\label{thm:ooosmp_sv}
Every satisfiable pattern $\phi$, without element variables, $\exists$, or 
$\mu$,
has a model $M$ with at most ${2^{\size{\phi}}}$ elements,
i.e., there exists $\rho$ such that $\evaluation{\phi}_{M,\rho} \neq \emptyset$.
\end{theorem}
\begin{proof}
Let $X_1,\dots,X_k$ be all the set variables in $\psi$.
We define $k$ new constant symbols $c_1,\dots,c_k$
and let $\psi' \cong \psi[c_1/X_1]\cdots[c_k/X_k]$.
Note that $\size{C(\psi')} = \size{C(\psi)}$.
By Theorem~\ref{thm:ooosmp}, $\psi'$ has a model $M$ with at most 
${2^{\size{\psi}}}$ elements, such that there exists $a \in M$
satisfying $a \vDash \psi'$.
We define a valuation $\rho$ such that $\rho(X_i) = (c_i)_{M'}$, for
every $1 \le i \le k$.
By ML semantics, $\evaluation{\psi'}_{\rho} = \evaluation{\psi}_{\rho}$,
so $a \in \evaluation{\psi}_{\rho}$.
Therefore, $\evaluation{\psi}_{\rho} \neq \emptyset$.
\end{proof}

\begin{theorem}\label{thm:ooodec_sv}
Given a pattern $\psi$, without element variables, $\exists$, or 
$\mu$,
determining whether $\psi$ is satisfiable is decidable.
\end{theorem}
\begin{proof}
The same as Theorem~\ref{thm:ooodec}.
\end{proof}


