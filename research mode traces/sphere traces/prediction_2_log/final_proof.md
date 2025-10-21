Proof. Fix $n$ sufficiently large. By the stated existence (Klartag 2025 together with transference), there is a unimodular lattice $L_0\subset\mathbb{R}^n$ such that
$$\Delta(L_0)\ \ge\ c_0\,n^2\,2^{-n}\quad\text{and}\quad c_1 n\ \le\ \rho(L_0)\,\lambda(L_0)\ \le\ C_1 n,$$
for some absolute $c_0,c_1,C_1>0$. Since for a unimodular $L$ one has $\Delta(L)=\omega_n(\lambda(L)/2)^n$, and $\omega_n^{1/n}\asymp n^{-1/2}$, we obtain an absolute $\kappa>0$ (all large $n$) with
$$\lambda(L_0)\ \ge\ \kappa\,\sqrt{n}.$$
Consequently
$$\rho(L_0)\ \le\ \frac{C_1 n}{\lambda(L_0)}\ \le\ \frac{C_1}{\kappa}\,\sqrt{n}=:K\sqrt{n},$$
whence the Voronoi second moment satisfies
$$\frac{1}{\operatorname{vol}_n(V(L_0))}\int_{V(L_0)}\!\|x\|^2\,dx\ \le\ \rho(L_0)^2\ \le\ K^2 n.$$

For $A\in\mathrm{GL}_n(\mathbb{R})$ let $s_{\min}(A)\le s_{\max}(A)$ denote its extremal singular values. For any lattice $L$ one has
$$\lambda(AL)\ \ge\ s_{\min}(A)\,\lambda(L),\qquad \rho(AL)\ \le\ s_{\max}(A)\,\rho(L).$$
For the packing density, recalling $\Delta(L)=\omega_n(\lambda(L)/2)^n/\det(L)$, one gets the scaling inequality
$$\Delta(AL)\ =\ \frac{\omega_n\bigl(\lambda(AL)/2\bigr)^{\!n}}{\det(A)\det(L)}\ \ge\ \frac{s_{\min}(A)^{\!n}}{|\det A|}\,\Delta(L).$$

Let $G:=\mathrm{SL}_n(\mathbb{R})$, $\Gamma:=\mathrm{SL}_n(\mathbb{Z})$, and choose $A_0\in G$ with $L_0=A_0\mathbb{Z}^n$. Since $\Gamma$ is discrete in $G$, there exists a symmetric neighborhood $\mathcal{N}$ of $I\in G$ with $\mathcal{N}\cap\Gamma=\{I\}$. Conjugation by $A_0$ is a homeomorphism, so there exists $\sigma_*>0$ such that
$$A_0^{-1}\,\mathcal{D}_{2\sigma}\,A_0\ \subset\ \mathcal{N}\qquad(0<\sigma\le \sigma_*),$$
where
$$\mathcal{D}_{\sigma}:=\Big\{\operatorname{diag}(e^{t_1},\ldots,e^{t_n})\in G:\ \sum_{i=1}^n t_i=0,\ \max_i|t_i|\le\sigma\Big\}.$$
For $A=\operatorname{diag}(e^{t_1},\ldots,e^{t_n})\in\mathcal{D}_{\sigma}$ one has $s_{\min}(A)\ge e^{-\sigma}$ and $s_{\max}(A)\le e^{\sigma}$.

Fix an absolute $\alpha\in(0,1)$ and set $\sigma:=\min\{\sigma_*/2,\ \alpha/n\}$. For each integer $m\ge2$, consider the grid
$$\mathcal{T}_m:=\Big\{t=(t_1,\ldots,t_n):\ t_n=-(t_1+\cdots+t_{n-1}),\ t_i\in \Big\{-\tfrac{\sigma}{n-1},-\tfrac{\sigma}{n-1}+\tfrac{2\sigma}{(n-1)m},\ldots,\tfrac{\sigma}{n-1}\Big\}\ (1\le i\le n-1)\Big\}.$$
Then $|\mathcal{T}_m|\ge m^{n-1}$ and every $t\in\mathcal{T}_m$ satisfies $\max_i|t_i|\le\sigma$, hence $A(t):=\operatorname{diag}(e^{t_1},\ldots,e^{t_n})\in\mathcal{D}_{\sigma}$ and $\det A(t)=e^{\sum t_i}=1$. Define lattices $L_t:=A(t)L_0$ (still unimodular).

We claim that the $L_t$ with $t\in\mathcal{T}_m$ are pairwise non–$\mathrm{SL}_n(\mathbb{Z})$–equivalent (i.e., represent distinct points of $G/\Gamma$). Indeed, suppose $L_t$ and $L_{t'}$ are $\Gamma$–equivalent, so there is $\gamma\in\Gamma$ with $A(t')A_0=A(t)A_0\gamma$. Then
$$A_0^{-1}A(t')^{-1}A(t)A_0\ =\ \gamma\ \in\ \Gamma.$$
But $A(t')^{-1}A(t)\in\mathcal{D}_{2\sigma}$, hence $A_0^{-1}A(t')^{-1}A(t)A_0\in A_0^{-1}\mathcal{D}_{2\sigma}A_0\subset\mathcal{N}$. Since $\mathcal{N}\cap\Gamma=\{I\}$, we get $A(t')^{-1}A(t)=I$, i.e. $t=t'$. Thus the $L_t$ are pairwise distinct in $G/\Gamma$.

For each $t\in\mathcal{T}_m$, using $\det A(t)=1$ and the scaling inequalities,
$$\Delta(L_t)\ =\ \Delta\bigl(A(t)L_0\bigr)\ \ge\ s_{\min}(A(t))^{\!n}\,\Delta(L_0)\ \ge\ e^{-n\sigma}\,\Delta(L_0)\ \ge\ e^{-\alpha}\,c_0\,n^2\,2^{-n}.$$ 
Also,
$$\frac{1}{\operatorname{vol}_n(V(L_t))}\int_{V(L_t)}\!\|x\|^2dx\ \le\ \rho(L_t)^2\ \le\ s_{\max}(A(t))^2\,\rho(L_0)^2\ \le\ e^{2\sigma}\,K^2 n\ \le\ e^{2\alpha/n}K^2 n\ \le\ C n$$
for all large $n$, where $C>0$ is an absolute constant (e.g. $C=2K^2$).

Finally, choosing $m=\lfloor n\rfloor$ yields
$$|\{L_t:\ t\in\mathcal{T}_m\}|\ \ge\ m^{n-1}\ \ge\ \exp\big((1+o(1))\,n\log n\big)\ \ge\ \exp(c\,n\log n)$$
for some absolute $c>0$ and all sufficiently large $n$.

Taking $c:=e^{-\alpha}c_0$ and the above $C$ completes the proof. $\square$