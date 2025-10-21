Assign independently to each edge of K_n a weight from {1,2,3} uniformly at random. For an edge uv, the difference of vertex sums is
$$
S_{uv}:=s_\omega(u)-s_\omega(v)=\sum_{w\in V\setminus\{u,v\}}\big(\omega(uw)-\omega(vw)\big)=\sum_{i=1}^{m}X_i,\qquad m:=n-2,
$$
where the X_i are i.i.d., each distributed as X=U_1-U_2 with U_1,U_2\overset{\text{i.i.d.}}\sim\mathrm{Unif}({1,2,3}). Thus
$$
\mathbb P(X=\pm2)=\tfrac19,\quad \mathbb P(X=\pm1)=\tfrac29,\quad \mathbb P(X=0)=\tfrac13,
$$
so in particular \(\mathbb E[X]=0\) and \(\mathrm{Var}(X)=\tfrac43\).

Claim (anti-concentration). There exists an absolute C>0 such that for all integers m≥1,
$$
\sup_{k\in\mathbb Z}\,\mathbb P\big(S_m=k\big)\le \frac{C}{\sqrt m}.
$$
Proof of the claim. Let \(\varphi(\theta)=\mathbb E[e^{i\theta X}]\) be the characteristic function of X. A direct computation gives
$$
\varphi(\theta)=\tfrac13+\tfrac49\cos\theta+\tfrac29\cos(2\theta)=\frac{4}{9}\big(\cos\theta+\tfrac12\big)^2.
$$
Hence \(0\le\varphi(\theta)\le1\) for all \(\theta\). Using \(\cos\theta=1-2\sin^2(\tfrac\theta2)\) and \(\cos2\theta=1-2\sin^2\theta\) yields
$$
1-\varphi(\theta)=\tfrac89\sin^2\!\Big(\tfrac\theta2\Big)+\tfrac49\sin^2\theta.
$$
For |\theta|≤1, concavity of sin implies \(\sin(\tfrac{|\theta|}{2})\ge \tfrac{|\theta|}{\pi}\), hence
$$
|\varphi(\theta)|\le e^{-c\theta^2}\quad\text{for }|\theta|\le1,\qquad c:=\tfrac{8}{9\pi^2}.
$$
For |\theta|\in[1,\pi], the previous identity gives \(1-\varphi(\theta)\ge \tfrac89\sin^2(\tfrac12)=:\delta>0\), so \(|\varphi(\theta)|\le\rho:=1-\delta<1\). By Fourier inversion for integer-lattice distributions,
$$
\mathbb P(S_m=k)=\frac{1}{2\pi}\int_{-\pi}^{\pi}\varphi(\theta)^m e^{-ik\theta}\,d\theta.
$$
Therefore,
$$
\mathbb P(S_m=k)\le\frac{1}{2\pi}\Big(\int_{-1}^{1}e^{-cm\theta^2}\,d\theta+\int_{[-\pi,\pi]\setminus[-1,1]}\rho^{m}\,d\theta\Big)
\le\frac{1}{2\pi}\sqrt{\frac{\pi}{c m}}+\rho^{m}
\le \frac{C}{\sqrt m}
$$
for some absolute C>0. This proves the claim. \(\square\)

Returning to K_n, for each edge uv we have
$$
\mathbb P\big(|s_\omega(u)-s_\omega(v)|\le1\big)=\mathbb P\big(S_{uv}\in\{0,\pm1\}\big)\le 3\sup_{k}\mathbb P(S_m=k)\le \frac{3C}{\sqrt{m}}=\frac{3C}{\sqrt{n-2}}.
$$
Let N=\binom{n}{2}. By linearity of expectation,
$$
\mathbb E\big[|\operatorname{Bad}_1(\omega)|\big]=\sum_{uv\in E(K_n)}\mathbb P\big(|s_\omega(u)-s_\omega(v)|\le1\big)\le \frac{3C\,N}{\sqrt{n-2}}.
$$
Thus there exists a (deterministic) 3–edge–weighting with
$$
|\operatorname{Bad}_1(\omega)|\le \frac{3C\,N}{\sqrt{n-2}}\le K\,n^{3/2}
$$
for some absolute constant K>0 (e.g., any K≥(3\sqrt{3}/2)C works for all n≥3). This proves the statement. \(\square\)