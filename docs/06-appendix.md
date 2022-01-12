\clearpage
\appendix

# Proofs for Section "The Modal Fragment"

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

\begin{lemma}\label{lemma:filter}
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
\addcontentsline{toc}{chapter}{Appendix}

\clearpage
# Proofs for Section "Quantifier-free Fragment" {#sec:qf-proofs}

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
\item If $s$ is an \appb{} node whose label is $L(s) = \sigma(\phi_1,\dots,\phi_n) \leadsto \Gamma$,
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
We select $s'$ whose label $L(s')$ is
$\leadsto\sigma(\phi_1,\dots,\phi_n) \leadsto \wit \leadsto \Gamma$.
\item If $s$ is an \appc{} node whose label is
$L(s) = \sigma(\phi_1,\dots,\phi_n) \leadsto \wit \leadsto \Gamma$ as defined in (5), we select all 
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
with $L(s) = \sigma(\phi_1,\dots,\phi_m) \leadsto L(a)$, 
and $s$ has exactly one child node $s'$ with
$L(s') = \sigma(\phi_1,\dots,\phi_m) \leadsto \wit \leadsto L(a)$ for some
$\wit  \in \Wit(L(a),\sigma)$, 
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
$L(s') = \sigma(\phi_1,\dots,\phi_n) \leadsto L(s)$,
which has exactly one child node $s''$ with
$L(s'') = \sigma(\phi_1,\dots,\phi_n) \leadsto \wit \leadsto L(s)$
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

\renewcommand{\hideunlessappendix}[1]{#1}
\renewcommand{\hideinappendix}[1]{}
\input{figs/guarded-tableau.tex}
\clearpage

# Proofs for Section "Guarded Fragment"

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

    a) $\phi = \phi_1 \land \cdots \land \phi_n$
       where each $\phi_i$ is either an application of the form $\sigma(\bar w)$ where $\bar w$ are element variables.
    b) every variable $x \in \bar x$ appears in some conjunct,
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
    increase until the last (resolve) node in that sequence and then does not change
    the variable is removed from the sequent (by the (app) or (exists) rule).

    Let $\bar y = \free{\phi} \setminus \bar x$.
    We will show that for each pair of variables in $w_1, w_2 \in \{y_0\}\union\free{\phi}$,
    we have $\nodes(w_1) \intersection \nodes(z_2) \ne \emptyset$.
    Then, using a well-known graph theory result saying that any collection of pairwise intersection
    subtrees of a tree share a common edge.
    \todo{cite}

    Suppose $w_1, w_2 \in \{ y_0 \} \union \bar y$. Then by assumption, they have a non empty intersection.
    If $w_1 = y_0$ and $w_2 \in \bar x$ then by point (b) they must coexist in some conjunct.
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

## Notes

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


