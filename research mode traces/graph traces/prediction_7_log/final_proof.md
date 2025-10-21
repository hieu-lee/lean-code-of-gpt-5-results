Assume for contradiction that there exists an absolute c>0 such that for every family of nice graphs G with Δ(G)→∞ and |V(G)|≤Δ(G)^{O(1)}, if p≥c·(log Δ(G))/Δ(G), then a.a.s. G_p is nice.

Fix this c>0. For each sufficiently large integer Δ, define
$$
G_Δ:=K_{1,Δ}\sqcup Δ\cdot K_3,
$$
where $\sqcup$ denotes disjoint union. Then $G_Δ$ is nice (it has no $K_2$-component), $\Delta(G_Δ)=Δ$, and
$$
|V(G_Δ)|=(Δ+1)+3Δ=4Δ+1\le Δ^2,
$$
so the family $\{G_Δ\}_{Δ\ge1}$ satisfies $\Delta(G_Δ)\to\infty$ and $|V(G_Δ)|\le \Delta(G_Δ)^{O(1)}$.

Let $p:=c\,\dfrac{\log Δ}{Δ}$ and form $H\sim (G_Δ)_p$ by retaining each edge independently with probability $p$. For each of the $Δ$ triangle components $T$ of $G_Δ$, let $A_T$ be the event that $T$ contributes a $K_2$-component to $H$. Since the triangles are edge-disjoint and have no edges to the rest of $G_Δ$, the events $\{A_T\}$ are mutually independent and depend only on the edges inside $T$.

In a triangle, $A_T$ occurs if and only if exactly one of its three edges is retained, hence
$$
\mathbb P(A_T)=3p(1-p)^2.
$$
Therefore
$$
\mathbb P\Big(\bigcap_T \overline{A_T}\Big)=(1-3p(1-p)^2)^{Δ}
\le\exp\big(-3p(1-p)^2\,Δ\big)
\le\exp\Big(-\tfrac{3}{4}\,p\,Δ\Big)
=\exp\Big(-\tfrac{3}{4}\,c\log Δ\Big)
=Δ^{-3c/4},
$$
where we used $1-x\le e^{-x}$ and, for all large $Δ$, $p\le\tfrac12$ so that $(1-p)^2\ge\tfrac14$. Hence
$$
\mathbb P\Big(\exists\text{ a $K_2$-component inside the triangles of }H\Big)
=1-\mathbb P\Big(\bigcap_T \overline{A_T}\Big)
\ge 1-Δ^{-3c/4}\xrightarrow[Δ\to\infty]{}1.
$$
Thus a.a.s. $H=(G_Δ)_p$ is not nice, contradicting the assumption that for this family and this $p\ge c\,(\log Δ)/Δ$, a.a.s. $G_p$ is nice. This contradiction proves the statement.