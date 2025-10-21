**Claim.** Let $f:\mathbb{R}^d\to\mathbb{R}$ be convex and differentiable. Consider the implicit (backward Euler / proximal point) scheme
$$
 x_{n+1}=x_n-\eta\,\nabla f(x_{n+1})\qquad(\eta>0),
$$
with $a_n:=f(x_n)$, $\Delta_n:=a_n-a_{n+1}$, and $\delta_n:=a_{n+2}-2a_{n+1}+a_n=\Delta_n-\Delta_{n+1}$. Then $\delta_n\ge 0$ for all $n$. Moreover, if $f$ is $\mu$-strongly convex, then $(\Delta_n)$ is strictly decreasing unless $x_n$ is optimal.

**Proof.** The optimality condition of the implicit step is
$$
\nabla f(x_{n+1})+\tfrac{1}{\eta}(x_{n+1}-x_n)=0.
$$
Set $s_n:=x_{n+1}-x_n$. Then $\nabla f(x_{n+1})=-\tfrac{1}{\eta}s_n$ and $x_{n+1}-x_{n+2}=-s_{n+1}$.

1) By convexity, for all $u,v$,
$$
 f(u)\ge f(v)+\langle\nabla f(v),u-v\rangle\quad\text{and}\quad f(v)-f(u)\le \langle\nabla f(v),v-u\rangle.
$$
Applying these with $(u,v)=(x_n,x_{n+1})$ and $(u,v)=(x_{n+2},x_{n+1})$ gives
$$
 \Delta_n=f(x_n)-f(x_{n+1})\ge \langle\nabla f(x_{n+1}),x_n-x_{n+1}\rangle = \tfrac{1}{\eta}\,\|s_n\|^2,
$$
$$
 \Delta_{n+1}=f(x_{n+1})-f(x_{n+2})\le \langle\nabla f(x_{n+1}),x_{n+1}-x_{n+2}\rangle = \tfrac{1}{\eta}\,\langle s_n,s_{n+1}\rangle.
$$
Therefore,
$$
 \delta_n=\Delta_n-\Delta_{n+1}\ge \tfrac{1}{\eta}\big(\|s_n\|^2-\langle s_n,s_{n+1}\rangle\big)
 \ge \tfrac{1}{\eta}\,\|s_n\|\big(\|s_n\|-\|s_{n+1}\|\big),
$$
where the last step uses Cauchy–Schwarz.

2) Since $f$ is convex, $\nabla f$ is monotone, hence
$$
 0\le \langle\nabla f(x_{n+1})-\nabla f(x_{n+2}),x_{n+1}-x_{n+2}\rangle 
 = \tfrac{1}{\eta}\langle s_n-s_{n+1},s_{n+1}\rangle,
$$
so $\langle s_n,s_{n+1}\rangle\ge \|s_{n+1}\|^2$. By Cauchy–Schwarz, $\|s_{n+1}\|\le\|s_n\|$. Plugging this into the bound in (1) yields $\delta_n\ge 0$ for all $n$, i.e., $n\mapsto f(x_n)$ is convex.

3) If, in addition, $f$ is $\mu$-strongly convex, then $\nabla f$ is $\mu$-strongly monotone:
$$
 \langle\nabla f(u)-\nabla f(v),u-v\rangle\ge \mu\,\|u-v\|^2\quad(\forall u,v).
$$
With $u=x_{n+1}$ and $v=x_{n+2}$ we get
$$
 \tfrac{1}{\eta}\langle s_n-s_{n+1},s_{n+1}\rangle\ge \mu\,\|s_{n+1}\|^2
 \;\Rightarrow\; \langle s_n,s_{n+1}\rangle\ge (1+\eta\mu)\,\|s_{n+1}\|^2.
$$
Hence $\|s_{n+1}\|\le \tfrac{1}{1+\eta\mu}\,\|s_n\|$, and if $s_n\ne 0$ then $\|s_{n+1}\|<\|s_n\|$. Using (1),
$$
 \delta_n\ge \tfrac{1}{\eta}\,\|s_n\|\big(\|s_n\|-\|s_{n+1}\|\big)
 \ge \tfrac{\mu}{1+\eta\mu}\,\|s_n\|^2>0.
$$
Thus $\Delta_{n+1}<\Delta_n$ strictly unless $s_n=0$, in which case the optimality condition gives $\nabla f(x_n)=0$ and $x_n$ is optimal, yielding $\Delta_n=\Delta_{n+1}=0$.

Therefore, $n\mapsto f(x_n)$ is convex for all $\eta>0$, and, under $\mu$-strong convexity, $(\Delta_n)$ is strictly decreasing unless $x_n$ is optimal. ∎