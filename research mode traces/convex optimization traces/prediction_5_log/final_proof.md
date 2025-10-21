Proof. Fix $L>0$ and $\theta\in(1.75,2)$, and set $\eta:=\theta/L\in(1.75/L,2/L)$. Suppose, for contradiction, that there exists a positive universal threshold $\bar\gamma(\theta)$ such that for every convex $L$-smooth $f$, every initialization $x_0$, and every $\gamma\in(0,\bar\gamma(\theta)]$, the sequence $n\mapsto e_\gamma(f)(x_n^{\rm GD})$ is convex in $n$, where $x_{n+1}=x_n-\eta\nabla f(x_n)$ and $$e_\gamma(f)(x):=\inf_{z}\Big\{f(z)+\tfrac{1}{2\gamma}\|z-x\|^2\Big\}.$$ By the even-index failure beyond $1.75/L$, there exist a convex $L$-smooth $f$ and an initialization $x_0$ such that, writing $x_{n+1}=x_n-\eta\nabla f(x_n)$ and $a_n:=f(x_n)$, one has $$\delta_0^0:=a_2-2a_1+a_0<0.$$

We claim that for every $x\in\mathbb{R}^d$ and $\gamma\in(0,1/L)$, $$0\le f(x)-e_\gamma(f)(x)\le \frac{\gamma}{2(1-\gamma L)}\,\|\nabla f(x)\|^2.$$ Indeed, by $L$-smoothness, for all $z$, $$f(z)\ge f(x)+\langle\nabla f(x),z-x\rangle-\tfrac L2\|z-x\|^2.$$ Hence, for $\gamma\in(0,1/L)$,
$$\begin{aligned}
e_\gamma(f)(x)
&=\inf_{z}\Big\{f(z)+\tfrac{1}{2\gamma}\|z-x\|^2\Big\}\\
&\ge f(x)+\inf_{t}\Big\{\langle\nabla f(x),t\rangle+\tfrac{1}{2}\Big(\tfrac1\gamma-L\Big)\|t\|^2\Big\}\\
&=f(x)-\frac{1}{2(\tfrac1\gamma-L)}\|\nabla f(x)\|^2
=f(x)-\frac{\gamma}{2(1-\gamma L)}\|\nabla f(x)\|^2,
\end{aligned}$$
while $e_\gamma(f)(x)\le f(x)$ by choosing $z=x$ in the infimum. In particular, $e_\gamma(f)(x)\to f(x)$ as $\gamma\downarrow0$ for each fixed $x$.

Apply this bound at $x_0,x_1,x_2$ and use the triangle inequality. With $g_n:=\nabla f(x_n)$ and $$\delta_0^\gamma:=e_\gamma(f)(x_2)-2e_\gamma(f)(x_1)+e_\gamma(f)(x_0),$$ we obtain, for $\gamma\in(0,1/L)$,
$$\big|\delta_0^\gamma-\delta_0^0\big|\le \frac{\gamma}{2(1-\gamma L)}\big(\|g_2\|^2+2\|g_1\|^2+\|g_0\|^2\big)\xrightarrow[\gamma\downarrow0]{}0.$$ Since $\delta_0^0<0$, there exists $\gamma_\star\in(0,1/L)$ such that $\delta_0^\gamma<0$ for all $\gamma\in(0,\gamma_\star]$. Choose $$\gamma\in\bigl(0,\min\{\bar\gamma(\theta),\gamma_\star,1/L\}\bigr].$$ Then $\delta_0^\gamma<0$, so the second forward difference at index $0$ of the sequence $n\mapsto e_\gamma(f)(x_n)$ is negative, contradicting the assumed convexity for all $\gamma\in(0,\bar\gamma(\theta)]$.

Therefore, no positive universal threshold $\bar\gamma(\theta)$ exists for $\theta\in(1.75,2)$, contradicting the supposition. In particular, the proposed scaling $\bar\gamma(\theta)=\Theta((2-\theta)/L)$ as $\theta\uparrow2$ cannot hold. ∎