# Cheng–Keevash, key-lemma sections — verbatim excerpt

**Source:** Qingyi Cheng and Peter Keevash, *A note on long directed
paths in digraphs with large minimum outdegree*, arXiv:2402.16776v4
(21 Aug 2024); journal version SIAM J. Discrete Math. 38(4), 3134–3139,
DOI 10.1137/24M1648375. © the authors.

This file reproduces, for scholarly reference during the formalization
(see `docs/ck3_dossier.md` and `docs/PLAN_CK3.md`), the two sections of
the paper that the CK3 development re-proves formally: "The key lemma"
(statement, Lemma 7 = `\label{lem1}`) and "Proof of the key lemma"
(Claims 10–12 = `\label{clm1}`, `\label{clma}`, `\label{claim2}`, and
the closing count). Figures are omitted. The full paper is at
https://arxiv.org/abs/2402.16776.

```latex
\section{The key lemma}

Here we show that Theorems \ref{thm1} and \ref{thm2} follow directly from
known results on the Caccetta-H\"{a}ggkvist conjecture and the following key lemma.

\begin{lemma}\label{lem1}
If $D$ is an oriented graph with $\delta^+(D) \geq \delta$ 
then $D$ either contains a directed path of length  $2\delta$ 
or an induced subgraph $S$ such that $|S|\leq \delta$ and $\delta^+(S) \geq 2\delta-\ell(D)$.
\end{lemma}

We use the following bounds on Caccetta-H\"{a}ggkvist in general by  Chv\'{a}tal and Szemer\'{e}di \cite{Chvatal} 
and in the case of directed triangles by  Hladk\'{y}, Kr\'{a}l, and Norin \cite{Norin}.

\begin{theorem}\label{thm0}
Every digraph $D$ with order $n$ and $\delta^+(D) \geq \delta$ contains a directed cycle of length at most $\lceil \frac{2n}{\delta+1}\rceil$.
\end{theorem}

\begin{theorem}\label{thm00}
Every oriented graph with order $n$ and minimum out-degree $0.3465n$ contains a directed triangle.
\end{theorem}

Now we deduce Theorems \ref{thm1} and \ref{thm2}, assuming the key lemma.

\begin{proof}[Proof of Theorem \ref{thm1}]
Suppose that $D$ is an oriented graph with $\delta^+(D)\geq \delta$ and girth $g$. 
By Lemma \ref{lem1}, $D$ contains a directed path of length $2\delta$ or an induced subgraph $S$ with $|S|\leq \delta$ and $\delta^+(S) \geq 2\delta-\ell(D)$. We assume the latter case holds.
According to Theorem \ref{thm0}, $S$ contains a directed cycle of length at most $\frac{2\delta}{2\delta-\ell(D)+1}$. 
Therefore, $g\leq \frac{2\delta}{2\delta-\ell(D)+1}$, so $\ell(D) \geq 2\delta(1-\frac{1}{g})+1\geq 2\delta(1-\frac{1}{g})$.
\end{proof}

\begin{proof}[Proof of Theorem \ref{thm2}]
First, suppose that $D$ is an oriented graph with $\delta^+(D)\geq \delta$. 
By Lemma \ref{lem1}, either $D$ contains a directed path of length $2\delta$ 
or $D$ contains an induced subgraph $S$ such that $|S|\leq \delta$ and $\delta^+(S) \geq 2\delta-\ell(D)$. 
Since $D$ is oriented, for some vertex $b\in S$, we have $d^+(b,S)\leq \frac{|S|-1}{2}$, 
which means that $\delta^+(S)\leq \frac{|S|-1}{2} \leq \frac{\delta-1}{2}$ and so $\ell(D) \geq 2\delta-\delta^+(S)\geq \frac{3}{2}\delta$.
Similarly, if $D$ has girth at least $4$ then substituting the bound $\delta^+(S)< 0.3465 \delta$ from Theorem \ref{thm00}
we obtain $\ell(D)>1.6535\delta$.
\end{proof}

In fact, by Lemma \ref{lem1}, any improved bound towards the Caccetta-H\"{a}ggkvist conjecture 
can be used to get a better bound for $\ell(D)$ when $\delta^+(D)\geq \delta$ and girth $g$. For example, the main result in \cite{shen2002caccetta} will give the bound $\ell(D) \ge (2-\frac{1}{g-73})\delta$. 
The Caccetta-H\"{a}ggkvist conjecture itself would imply $\ell(D) \ge (2-\frac{1}{g})\delta$.

\section{Proof of the key lemma}

Suppose that $D$ is an oriented graph with $\delta^+(D)\geq \delta$ 
and no directed path of length $2\delta$.
We can assume that $D$ is strongly-connected,
as there is a strong component of $D$ with minimum out-degree at least $\delta$.
By deleting arcs, we can also assume that all out-degrees are exactly $\delta$.
Note that $|V(D)|\geq 2\delta+1$, since $D$ is oriented and $\delta^+(D)\geq \delta$. 

\begin{claim} \label{clm1}
$D$ does not  contain two disjoint directed cycles of length at least $\delta+1$. 
\end{claim}
\begin{proof}
Suppose on the contrary that $C_1$ and $C_2$ are two such cycles. By strong connectivity, 
there exists a path $P$ from $u_1\in C_1$ to $u_2\in C_2$ with $V(P)$ internally disjoint from $V(C_1) \cup V(C_2)$. 
Writing $u_1 u_1^{\prime}$ for the out-arc of $u_1$ in $C_1$ and $u_2^{\prime} u_2$ for the in-arc of $u_2$ in $C_2$, 
the path $\{C_1-u_1 u_1^{\prime} \}+P+\{C_2-u_2^{\prime} u_2 \}$ has length at least $2\delta+1$, a contradiction.
\end{proof}

Now let $P=v_0v_1 \cdots v_{\ell(D)}$ be a directed path of maximum length, where $\ell(D)<2\delta$.
By maximality of $P$, the out-neighbours $N^+(v_{\ell(D)})$ of $v_{\ell(D)}$ must lie on $P$. 
Let $v_a \in N^+(v_{\ell(D)})$ such that the index $a$ is minimum among all the out-neighbours of $v_{\ell(D)}$. 
Thus $C=v_av_{a+1}\cdots v_{\ell(D)}v_a$ is a directed cycle; we call $|C|$ the \emph{cycle bound} of $P$.
For future reference, we record the consequence
\begin{equation} \label{cyc}
\ell(D) \ge g(D) \text{ for any digraph } D.
\end{equation}

Choose $P$ such that the cycle bound of $P$ is also maximum subject to that $P$ is a directed path of length $\ell(D)$. 
Clearly $a\neq 0$, otherwise using $|V(D)|\geq 2\delta+1$ and strong connectivity, 
we can easily add one more vertex to $C$ and get a longer path, contradiction.

\begin{claim} \label{clma}
Every vertex in $N^+(v_{a-1})$ must be on $P$.
\end{claim}
\begin{proof}
Suppose on the contrary that there exists an out-neighbour $w_1$ of $v_{a-1}$ such that $w_1\in V(D)\setminus V(P)$. 
Let $D_1$ be the induced graph of $D$ on $V(D)\setminus V(P)$. We extend the vertex $w_1$ to a maximal directed path $P_1=w_1w_2\cdots w_m$ in $D_1$. 
Since $P_1$ is maximal in $D_1$, all the out-neighbours of $w_m$ must be on $V(P)\cup V(P_1)$, see Figure \ref{fig1}(a).

[figure omitted]

We cannot have $w\in N^+(u_m)$ such that $w\in V(C)$. Indeed, writing $w^-$ for the in-neighbour of $w$ in $C$,
the directed path $P^{\prime}=v_0\ldots v_{a-1}P_1w+(C-w^-w)$ would be longer than $P$, a contradiction.
Thus we conclude that $N^+(w_m)\subseteq V(P_1)\cup \{v_0,...,v_{a-1}\}$. 
Choose a vertex $z\in N^+(w_m)$ that has the largest distance to $w_m$ on the path $P_2=v_0\ldots v_{a-1}w_1 \ldots w_m$. 
Then $P_2\cup w_mz$ contains a cycle $C_1$ of length at least $\delta +2$. 
Now $C_1$ and $C$ are two disjoint directed cycles of length at least $\delta+2$, 
which contradicts Claim \ref{clm1}.
\end{proof}

Let $A=N^+(v_{a-1})\cap \{v_0,\ldots, v_{a-1}\}$ and $B=N^+(v_{a-1})\cap V(C)$. 
Also, let $B^-=\{u: u\in V(C), uv\in A(C)$ for some $v \in B\}$.


\begin{claim} \label{claim2}
$N^+(B^-)\subseteq V(C)$.
\end{claim}

\begin{proof}
Suppose not, then there exists a vertex $w\in V(D)\setminus V(C)$ such that $bw\in A(D)$ for some $b\in B^-$. 
By definition of $B$, there exists some vertex $b^+\in B$ such that $v_{a-1}b^+\in A(D)$ and $bb^+ \in A(C)$. 
We cannot have $w\in V(D)\setminus V(P)$, as then the path $v_0v_1\ldots v_{a-1}b^++(C-bb^+)+bw$ has  length $\ell(D)+1$, a contradiction.

It remains to show that we cannot have $w\in V(P)\setminus V(C)$. Suppose that we do, with $w=v_i$ for some $0\leq i\leq a-1$. 
Then the cycle $v_iv_{i+1}\ldots v_{a-1}b^++ (C-bb^+)+bv_i$ is longer than $C$. 
However, $P_1=v_0\ldots v_{a-1}b^++(C-bb^+)$ has length $\ell(D)$ and cycle bound larger than $P$, which contradicts our choice of $P$,
see Figure \ref{fig1}(b).
\end{proof}

Now let $S$ be the induced digraph of $D$ on $B^-$. 
Fix $x\in B^-$ with $N^+_{S}(x)=\delta^+(S)$. 
Then $N^+(x)\subseteq V(C)$ by Claim \ref{claim2}.
As $|N^+(x)|=\delta$ we deduce  $|C|\geq |S|-\delta^+(S)+\delta$.

Note that $|P|\geq |A|+1+|C|\geq |A|+1+|B|-\delta^+(S)+\delta$,
as $|S|=|B^-|=|B|$ and $A\subseteq \{v_0,\ldots,v_{a-1}\}$.
But $|A|+|B|=|N^+(v_{a-1})|=\delta$, so
$\ell(D)=|P|\geq 2\delta+1-\delta^+(S)$ and $\delta^+(S)\geq 2\delta+1-\ell(D)$.

This completes the proof of Lemma \ref{lem1}.

```
