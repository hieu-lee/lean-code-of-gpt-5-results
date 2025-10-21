\begin{proof}
Let $f:\mathbb{R}^d\to\mathbb{R}$ be convex and differentiable, and fix $\eta>0$. Define the explicit and implicit iterates by
$$x_{n+1}=x_n-\eta\nabla f(x_n),\qquad z_{n+1}=z_n-\eta\nabla f(z_{n+1}),$$
with arbitrary initial points $x_0,z_0$, and set $c_n:=\tfrac12\big(f(x_n)+f(z_n)\big)$. We prove $\delta^c_n:=c_{n+2}-2c_{n+1}+c_n\ge 0$ for all $n$.

Write the Bregman divergence $D_f(u,v):=f(u)-f(v)-\langle\nabla f(v),u-v\rangle\ge 0$. Denote $g_n:=\nabla f(x_n)$, $h_{n+1}:=\nabla f(z_{n+1})$, and the steps $\Delta x_n:=x_{n+1}-x_n=-\eta g_n$, $\Delta z_{n+1}:=z_{n+1}-z_n=-\eta h_{n+1}$. The identities (obtained from the definition of $D_f$) are
$$\Delta^x_n:=f(x_n)-f(x_{n+1})=\frac{1}{\eta}\|\Delta x_n\|^2- D_f(x_{n+1},x_n),\qquad
\Delta^z_n:=f(z_n)-f(z_{n+1})=\frac{1}{\eta}\|\Delta z_{n+1}\|^2+ D_f(z_n,z_{n+1}).$$
Since $\Delta^c_n:=c_n-c_{n+1}=\tfrac12(\Delta^x_n+\Delta^z_n)$, we have
$$2\,\delta^c_n=(\Delta^x_n-\Delta^x_{n+1})+(\Delta^z_n-\Delta^z_{n+1})=\eta\,S_g+S_B,$$
where
$$S_g:=\big(\|g_n\|^2-\|g_{n+1}\|^2\big)+\big(\|h_{n+1}\|^2-\|h_{n+2}\|^2\big),$$
$$S_B:=\big(D_f(x_{n+2},x_{n+1})-D_f(x_{n+1},x_n)\big)+\big(D_f(z_n,z_{n+1})-D_f(z_{n+1},z_{n+2})\big).$$
Use the three-point identity (valid for all $a,b,c$):
$$D_f(a,b)-D_f(b,c)=D_f(a,c)-\langle\nabla f(b)-\nabla f(c),\,a-b\rangle.$$
With $(a,b,c)=(x_{n+2},x_{n+1},x_n)$ and $(a,b,c)=(z_n,z_{n+1},z_{n+2})$, and $x_{k+1}-x_k=-\eta g_k$, $z_{k+1}-z_k=-\eta h_{k+1}$, this gives
\begin{align*}
S_B&=D_f(x_{n+2},x_n)-\langle g_{n+1}-g_n,\,x_{n+2}-x_{n+1}\rangle+ D_f(z_n,z_{n+2})-\langle h_{n+1}-h_{n+2},\,z_n-z_{n+1}\rangle\\
&=D_f(x_{n+2},x_n)+D_f(z_n,z_{n+2})+\eta\,\langle g_{n+1}-g_n,\,g_{n+1}\rangle+\eta\,\langle h_{n+2}-h_{n+1},\,h_{n+1}\rangle.
\end{align*}
Therefore
\begin{align*}
2\,\delta^c_n&=\eta\big(\|g_n\|^2-\|g_{n+1}\|^2\big)+\eta\big(\|h_{n+1}\|^2-\|h_{n+2}\|^2\big)+S_B\\
&=D_f(x_{n+2},x_n)+D_f(z_n,z_{n+2})+\eta\big(\|g_n\|^2-\langle g_n,g_{n+1}\rangle\big)+\eta\big(\langle h_{n+2},h_{n+1}\rangle-\|h_{n+2}\|^2\big)\\
&=D_f(x_{n+2},x_n)+D_f(z_n,z_{n+2})+\underbrace{\langle g_n-g_{n+1},\,x_n-x_{n+1}\rangle}_{\ge 0}+\underbrace{\langle h_{n+2}-h_{n+1},\,z_{n+2}-z_{n+1}\rangle}_{\ge 0},
\end{align*}
where we used $x_n-x_{n+1}=\eta g_n$ and $z_{n+2}-z_{n+1}=-\eta h_{n+2}$. The two inner products are nonnegative by the monotonicity of $\nabla f$ (convexity of $f$), and the Bregman divergences are nonnegative by convexity. Hence $2\,\delta^c_n\ge 0$, i.e., $\delta^c_n\ge 0$ for all $n$. Thus $n\mapsto c_n$ is convex.
\end{proof}