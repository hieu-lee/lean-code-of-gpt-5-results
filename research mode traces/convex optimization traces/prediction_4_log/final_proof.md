Proof. Fix any L>0 and any η∈(0,2/L). Choose any s>0 and define the continuous gradient field g:ℝ→ℝ by
\[
 g(x):=\begin{cases}
 s+L\,(x+η s), & x< -η s,\\
 s, & x\ge -η s.
 \end{cases}
\]
Set \(f(x):=\int_0^x g(t)\,dt\). Then \(f\) is differentiable with \(\nabla f=g\). Since \(g\) is nondecreasing (its a.e. derivative is \(g'(x)=L\mathbf{1}_{(-\infty,-η s)}(x)\ge 0\)), \(f\) is convex. Moreover, \(\nabla f=g\) is \(L\)-Lipschitz: if \(x,y< -η s\), then \(|g(x)-g(y)|=L|x-y|\); if \(x,y\ge -η s\), then \(|g(x)-g(y)|=0\le L|x-y|\); and if \(x< -η s\le y\), then
\[
 |g(x)-g(y)|=L|x+η s|\le L(y-x)=L|x-y|,
\]
because \(y-x\ge -η s - x=-(x+η s)=|x+η s|\). Thus \(f\) is convex and \(L\)-smooth on \(\mathbb R\).

Run gradient descent from \(x_0=0\) with stepsize \(η\). Since \(g(0)=s\), we have
\[
 x_1=x_0-η g(x_0)=-η s,\quad g(x_1)=s,\quad x_2=x_1-η g(x_1)=-2η s,\quad g(x_2)=s+L(-2η s+η s)=s(1-Lη).
\]
Therefore
\[
 \|\nabla f(x_2)\|^2-2\|\nabla f(x_1)\|^2+\|\nabla f(x_0)\|^2
 = s^2\big((1-Lη)^2-2+1\big)
 = s^2\big(L^2η^2-2Lη\big)
 = s^2 Lη\,(Lη-2)<0,
\]
since \(0<Lη<2\). Hence the sequence \(n\mapsto\|\nabla f(x_n)\|^2\) is not convex (its second difference at \(n=0\) is negative). ∎