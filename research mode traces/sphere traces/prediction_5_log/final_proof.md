By a theorem of Klartag, there exists an absolute constant $c_\ast>0$ such that for every $n\ge2$ there is a lattice $L_0\subset\R^n$ and a radius $r\in(0,\lambda_1(L_0)/2]$ with packing density
$$\Delta(L_0,r)\ =\ \frac{\omega_n r^n}{\det(L_0)}\ \ge\ c_\ast\,n^2\,2^{-n}.$$
Since $r\le\lambda_1(L_0)/2$, the critical packing density
$$\Delta(L_0)\ :=\ \frac{\omega_n}{\det(L_0)}\Bigl(\tfrac{\lambda_1(L_0)}{2}\Bigr)^{\!n}$$
satisfies $\Delta(L_0)\ge\Delta(L_0,r)\ge c_\ast n^2 2^{-n}$. Scale $L_0$ by $s=\det(L_0)^{-1/n}$ to obtain a unimodular lattice $L=sL_0$. The critical density is scale-invariant, hence
$$\Delta(L)\ =\ \Delta(L_0)\ \ge\ c_\ast\,n^2\,2^{-n}.$$
For unimodular $L$,
$$\Delta(L)\ =\ \omega_n\Bigl(\tfrac{\lambda_1(L)}{2}\Bigr)^{\!n},$$
so
$$\lambda_1(L)\ =\ 2\Bigl(\tfrac{\Delta(L)}{\omega_n}\Bigr)^{\!1/n}\ \ge\ 2\Bigl(\tfrac{c_\ast n^2 2^{-n}}{\omega_n}\Bigr)^{\!1/n}.$$
Using $\omega_n\le(2\pi e/n)^{n/2}$, we get
$$\lambda_1(L)\ \ge\ c_\ast^{1/n}\,n^{2/n}\,\Bigl(\tfrac{n}{2\pi e}\Bigr)^{\!1/2}\ \ge\ \frac{\min\{1,\sqrt{c_\ast}\}}{\sqrt{2\pi e}}\,\sqrt{n},$$
where we used $n^{2/n}\ge1$ and $c_\ast^{1/n}\ge\min\{1,\sqrt{c_\ast}\}$ for $n\ge2$. By monotonicity of successive minima, $\lambda_k(L)\ge\lambda_1(L)$ for all $1\le k\le n$, hence
$$\lambda_k(L)\ \ge\ \frac{\min\{1,\sqrt{c_\ast}\}}{\sqrt{2\pi e}}\,\sqrt{n}\ \ge\ \frac{\min\{1,\sqrt{c_\ast}\}}{\sqrt{2\pi e}}\,\sqrt{k}.$$
Finally, set
$$c_0:=\min\Bigl\{c_\ast,\ \frac{\min\{1,\sqrt{c_\ast}\}}{\sqrt{2\pi e}}\Bigr\},\qquad c_1:=1.$$
Then $\Delta(L)\ge c_0 n^2 2^{-n}$ and, for all $1\le k\le\lfloor c_1 n\rfloor$, $\lambda_k(L)\ge c_0\sqrt{k}$.