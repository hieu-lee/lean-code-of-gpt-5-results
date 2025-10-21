Construct f on R by
$$
f(x)=\begin{cases}
 \tfrac12(x-b)^2+g_1(x-b), & x\le b,\\[2pt]
 g_1(x-b), & x\ge b,
 \end{cases}
\qquad b=\tfrac32,\quad g_1=\tfrac12.
$$
Then f is convex and C^1 with
$$
f'(x)=\begin{cases} g_1+(x-b), & x\le b,\\ g_1, & x\ge b,\end{cases}
\qquad f''(x)=\begin{cases}1,&x<b,\\0,&x>b.\end{cases}
$$
Hence \(|f''(x)|\le 1\) wherever it exists, and f' is globally 1-Lipschitz: if x\le b\le y, then
\(|f'(x)-f'(y)|=|[g_1+(x-b)]-g_1|=|x-b|\le|x-y|\); for x,y\le b the slope is 1; for x,y\ge b the derivative is constant. Thus f is convex and 1-smooth.

Run gradient descent with constant step \(\eta=2\) from \(x_0=0\):
$$
f'(0)=g_1+(0-b)=-1,\quad x_1=x_0-\eta f'(0)=2;\qquad f'(2)=g_1=\tfrac12,\quad x_2=x_1-\eta f'(x_1)=1.
$$
Moreover, \(f'(1)=g_1+(1-b)=0\), so \(x_n=1\) for all \(n\ge2\).

For the local curvature surrogates \(L_n=\sup_{t\in[0,1]}|f''(x_n+t(x_{n+1}-x_n))|\) (in 1D):
- On \([x_0,x_1]=[0,2]\), \(L_0=1\) since the segment intersects \((\! -\infty,b)\) where \(f''\equiv1\).
- On \([x_1,x_2]=[2,1]\), \(L_1=1\) for the same reason.
- For all \(n\ge2\), \(x_{n+1}=x_n=1<b\), so \(L_n=1\).
Thus \(L_n\equiv1=L_0\) is constant (hence nonincreasing) along the run, and \(\eta=2=2/L_0\) is the maximal admissible step.

Evaluate f at the first three iterates:
$$
f(0)=\tfrac38,\qquad f(2)=\tfrac14,\qquad f(1)=-\tfrac18.
$$
Therefore the discrete second difference at \(n=0\) is
$$
\delta_0=f(x_2)-2f(x_1)+f(x_0)=-\tfrac18-2\cdot\tfrac14+\tfrac38=-\tfrac14<0.
$$
Hence the GD loss curve is not convex even though f is convex and 1-smooth, the curvature surrogates are constant \(L_n\equiv L_0\), and the step size equals the upper bound \(\eta=2/L_0\). This proves the claim.