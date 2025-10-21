\begin{proof}
Fix $n\ge 3$. By the lattice packing result (Klartag), there exists an absolute $c_0>0$ and a lattice $L_0\subset\R^n$ with
$$\Delta(L_0)\ \ge\ c_0\,n^2\,2^{-n}.$$
Rescale to unimodularity: let $s:=\det(L_0)^{-1/n}$ and $L_1:=sL_0$. Then $\det(L_1)=1$ and, since $\Delta$ is scale-invariant, $\Delta(L_1)=\Delta(L_0)\ge c_0 n^2 2^{-n}$.

For $t\ge0$ define
$$P_t:=\operatorname{diag}\big(e^{t},e^{-t/(n-1)},\ldots,e^{-t/(n-1)}\big)\in \mathrm{SL}_n(\R),$$
and for $U\in\mathrm{SO}(n)$ set $L_{U,t}:=P_t\,U\,L_1$ (still unimodular).

1) Density stability under $P_t$. The smallest singular value of $P_t$ equals $e^{-t/(n-1)}$, hence for all $U\in\mathrm{SO}(n)$,
$$\lambda(L_{U,t})\ =\ \min_{v\in L_1\setminus\{0\}}\|P_t U v\|\ \ge\ e^{-t/(n-1)}\,\lambda(L_1).$$
Therefore, since $\det(L_{U,t})=1$,
$$\Delta(L_{U,t})\ =\ \omega_n\Big(\tfrac{\lambda(L_{U,t})}{2}\Big)^n\ \ge\ e^{-\tfrac{n}{n-1}t}\,\omega_n\Big(\tfrac{\lambda(L_1)}{2}\Big)^n\ \ge\ e^{-2t}\,\Delta(L_1),$$
because $\tfrac{n}{n-1}\le 2$ for $n\ge2$.

2) Making the minimum simple by a rotation and a one-parameter anisotropy. For $v,w\in L_1\setminus\{0\}$ with $w\ne\pm v$ and for $U\in\mathrm{SO}(n)$, define
$$h_{v,w,U}(t):=\|P_t U v\|^2-\|P_t U w\|^2\ =\ a_{v,w}(U)e^{2t}+b_{v,w}(U)e^{-\tfrac{2}{n-1}t},$$
where
$$a_{v,w}(U):=((Uv)_1)^2-((Uw)_1)^2,\qquad b_{v,w}(U):=\sum_{i=2}^n\Big(((Uv)_i)^2-((Uw)_i)^2\Big).$$
Note that $h_{v,w,U}\equiv0$ iff $a_{v,w}(U)=b_{v,w}(U)=0$, which is equivalent to $\|v\|=\|w\|$ and $((Uv)_1)^2=((Uw)_1)^2$.

Fix $v,w\in L_1\setminus\{0\}$ with $w\ne\pm v$ and $\|v\|=\|w\|$. Consider the real-analytic function on $\mathrm{SO}(n)$
$$F_{v,w}(U):=((Uv)_1)^2-((Uw)_1)^2.$$
This function is not identically zero: choose $U_0\in\mathrm{SO}(n)$ with $U_0\tfrac{v}{\|v\|}=e_1$ and $U_0\tfrac{w}{\|w\|}=\cos\theta\,e_1+\sin\theta\,e_2$ where $\theta\in(0,\pi)$ since $w\ne\pm v$. Then $F_{v,w}(U_0)=1-\cos^2\theta=\sin^2\theta>0$. Hence the zero set $Z_{v,w}:=\{U\in\mathrm{SO}(n):F_{v,w}(U)=0\}$ is a proper real-analytic subset of $\mathrm{SO}(n)$ and thus has empty interior. For pairs with $\|v\|\ne\|w\|$, $h_{v,w,U}$ is never identically zero for any $U$.

Since $L_1\setminus\{0\}$ is countable, the union
$$Z\ :=\ \bigcup_{\substack{v,w\in L_1\setminus\{0\}\\ w\ne\pm v}}\{U\in\mathrm{SO}(n):\ h_{v,w,U}\equiv0\}$$
is a countable union of nowhere dense sets. By the Baire category theorem, $\mathrm{SO}(n)\setminus Z$ is dense and nonempty; fix $U\in\mathrm{SO}(n)\setminus Z$.

For this $U$ and each $v\ne\pm w$, the function $t\mapsto h_{v,w,U}(t)$ is not identically zero and, being of the form $ae^{2t}+be^{-\tfrac{2}{n-1}t}$ with $(a,b)\ne(0,0)$, has at most one real zero (multiplying by $e^{\tfrac{2}{n-1}t}>0$ shows zeros correspond to those of $ae^{\tfrac{2n}{n-1}t}+b$). Hence the set
$$T\ :=\ \bigcup_{\substack{v,w\in L_1\setminus\{0\}\\ w\ne\pm v}}\{t\in(0,\tfrac{1}{10}):\ h_{v,w,U}(t)=0\}$$
is countable. Choose $t\in(0,\tfrac{1}{10})\setminus T$. Then $\|P_t U v\|\ne\|P_t U w\|$ for all $w\ne\pm v$, so the minimum of $L_{U,t}$ is attained by a unique pair $\pm v_{\min}$, i.e. $\tau(L_{U,t})=2$.

3) Conclusion. With this $U$ and $t$, combining the bounds from step 1 and the choice of $L_1$ gives
$$\Delta(L_{U,t})\ \ge\ e^{-2\cdot(1/10)}\,c_0\,n^2\,2^{-n}\ =:\ c\,n^2\,2^{-n}$$
for the absolute constant $c:=e^{-1/5}c_0>0$. Moreover $\tau(L_{U,t})=2$. Setting $L:=L_{U,t}$ completes the proof.
\end{proof}