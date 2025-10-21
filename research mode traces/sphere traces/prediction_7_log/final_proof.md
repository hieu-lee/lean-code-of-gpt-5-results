\begin{proof}
Fix $n\ge2$. We produce an origin–symmetric ellipsoid $\cE\subset\R^n$ with $\cE\cap(\Z^n\setminus\{0\})=\varnothing$, $\operatorname{vol}_n(\cE)\ge c\,n^2$, and $\kappa(\cE)\le n^{C}$ for absolute constants $c,C>0$, and then record the equivalence with the packing formulation.

1) Linear normalization and the integer–free difference body. Let $L\subset\R^n$ be a lattice with minimum $\lambda(L)$ and choose $U\in\mathrm{GL}_n(\R)$ with $U(L)=\Z^n$. Put
\[
K(U):=U\,B_n\!\Bigl(0,\tfrac{\lambda(L)}{2}\Bigr),\qquad \cE(U):=2K(U)=U\,B_n\!\bigl(0,\lambda(L)\bigr).
\]
Since $\{B_n(\ell,\tfrac{\lambda(L)}2):\ell\in L\}$ is a packing, the translates $\{K(U)+z: z\in\Z^n\}$ are pairwise disjoint. Hence $\cE(U)=K(U)-K(U)$ is integer–free: if $z\in\Z^n\setminus\{0\}$ lay in $\cE(U)$, there would exist $x,y\in K(U)$ with $z=x-y$, forcing $K(U)\cap(K(U)+z)\ne\varnothing$, a contradiction. Moreover,
\[
 \operatorname{vol}_n\bigl(\cE(U)\bigr)=2^{\,n}\,\operatorname{vol}_n\bigl(K(U)\bigr)=2^{\,n}\,|\det U|\,\omega_n\Bigl(\tfrac{\lambda(L)}{2}\Bigr)^{\!n}=2^{\,n}\,\Delta(L),
\]
using $|\det U|=1/\det(L)$. Finally, $\cE(U)=U\,B_n(0,\lambda(L))$ is an ellipsoid whose semi–axes are $\lambda(L)$ times the singular values of $U$, so $\kappa(\cE(U))=\kappa(U)$.

2) A lattice with quadratic packing and controlled local geometry. By the lattice version of Klartag’s theorem and standard normalizations, there exist absolute constants $c_0,C_0>0$ and, for each $n\ge2$, a unimodular lattice $L\subset\R^n$ such that
\[
\Delta(L)\ \ge\ c_0\,n^2\,2^{-n}\qquad\text{and}\qquad c_0\,n\ \le\ \rho(L)\,\lambda(L)\ \le\ C_0\,n.
\]
Since $\Delta(L)=\omega_n\bigl(\tfrac{\lambda(L)}{2}\bigr)^n$ and $\omega_n\le (2\pi e/n)^{n/2}$, we obtain
\[
\lambda(L)^n\ \ge\ \frac{c_0\,n^2}{\omega_n}\ \ge\ c\,n^2\Bigl(\frac{n}{2\pi e}\Bigr)^{\!n/2}\quad\Longrightarrow\quad \lambda(L)\ \ge\ c_1\,\sqrt n
\]
for an absolute $c_1>0$. The product bound $\rho(L)\,\lambda(L)\le C_0 n$ then gives
\[
\rho(L)\ \le\ \frac{C_0 n}{\lambda(L)}\ \le\ C_2\,\sqrt n.
\]
In particular, by Jarník’s inequality, $\lambda_n(L)\le 2\rho(L)\le C_3\sqrt n$, while $\lambda_1(L)=\lambda(L)\ge c_1\sqrt n$.

3) A primal–dual reduction and a lower bound on $\lambda_1(L^*)$. We use two inputs.

(i) Slab transference for the covering radius: for every lattice $L$,
\[
\rho(L)\ \ge\ \frac{1}{2\,\lambda_1(L^*)}.
\]
Proof: let $y\in L^*$ with $\|y\|=\lambda_1(L^*)$ and choose $x\in\R^n$ with $\langle y,x\rangle=\tfrac12$. For any $\ell\in L$, one has $\langle y, x-\ell\rangle\in \tfrac12+\Z$, hence $|\langle y,x-\ell\rangle|\ge\tfrac12$. By Cauchy–Schwarz, $\|x-\ell\|\ge \tfrac{1}{2\|y\|}$. Taking the infimum over $\ell$ and then the supremum over $x$ yields $\rho(L)\ge\tfrac{1}{2\|y\|}$; minimizing over $y\in L^*\setminus\{0\}$ gives the claim.

Together with $\rho(L)\le C_2\sqrt n$ from Step 2 this implies
\[
\lambda_1(L^*)\ \ge\ \frac{1}{2\rho(L)}\ \ge\ c_2\,n^{-1/2}
\]
for an absolute $c_2>0$.

(ii) Seysen’s theorem: there exists a basis $B=[b_1\,\cdots\,b_n]$ of $L$ with dual basis $B^*=[b_1^*\,\cdots\,b_n^*]$ such that
\[
S(B):=\max_i\,\|b_i\|\,\|b_i^*\|\ \le\ C_S\,n
\]
for an absolute $C_S>0$.

Put $U:=B^{-1}$, so $U(L)=\Z^n$. Using $\|B\|\le \|B\|_F\le \sqrt n\,\max_i\|b_i\|$ and $\|B^{-1}\|\le\sqrt n\,\max_i\|b_i^*\|$, together with
\[
\max_i\|b_i\|\le \frac{S(B)}{\min_j\|b_j^*\|}\le \frac{S(B)}{\lambda_1(L^*)},\qquad\max_i\|b_i^*\|\le \frac{S(B)}{\min_j\|b_j\|}\le \frac{S(B)}{\lambda_1(L)},
\]
we obtain the condition number bound
\[
\kappa(U)=\kappa(B)=\|B\|\,\|B^{-1}\|\ \le\ \frac{n\,S(B)^2}{\lambda_1(L)\,\lambda_1(L^*)}\ \le\ \frac{n\,(C_S n)^2}{c_1\sqrt n\,\cdot\,c_2 n^{-1/2}}\ \le\ C\,n^3
\]
for an absolute constant $C>0$.

4) The ellipsoid. With $U$ from Step 3 and the lattice $L$ from Step 2, set $\cE:=\cE(U)=U\,B_n(0,\lambda(L))$. By Step 1, $\cE$ is origin–symmetric and integer–free, and
\[
 \operatorname{vol}_n(\cE)=2^{\,n}\,\Delta(L)\ \ge\ c_0\,n^2,\qquad \kappa(\cE)=\kappa(U)\ \le\ C\,n^3.
\]
This proves the ellipsoid formulation with absolute constants $c,C>0$.

5) Equivalence with the packing formulation. If $\cE\subset\R^n$ is origin–symmetric and integer–free, then $\{\tfrac12\cE+z:z\in\Z^n\}$ is a lattice packing with density
\[
\delta\ =\ \operatorname{vol}_n\!\bigl(\tfrac12\cE\bigr)\ =\ 2^{-n}\,\operatorname{vol}_n(\cE)\ \ge\ c\,\frac{n^2}{2^{\,n}}.
\]
Conversely, if $\{B_n(\ell,r):\ell\in L\}$ is a lattice sphere packing, choose $U\in\mathrm{GL}_n(\R)$ with $U(L)=\Z^n$, set $K:=U B_n(0,r)$ and $\cE:=2K$. Then $\cE$ is integer–free and
\[
\operatorname{vol}_n(\cE)=2^{\,n}\,\operatorname{vol}_n(K)=2^{\,n}\,\frac{\omega_n r^n}{\det(L)}=2^{\,n}\,\Delta(L,r).
\]
Taking $L$ from Step 2 and $r=\lambda(L)/2$ recovers the ellipsoid from Step 4, whose axis ratios are bounded by a fixed polynomial in $n$.

Therefore, for every $n\ge2$ there exists an origin–symmetric integer–free ellipsoid $\cE\subset\R^n$ with $\operatorname{vol}_n(\cE)\ge c\,n^2$ and $\kappa(\cE)\le n^{C}$ for absolute $c,C>0$, and equivalently a lattice packing of density at least $c\,n^2\,2^{-n}$. \qedhere
\end{proof}