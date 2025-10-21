Setting and notation used in all statements:
- Space: $\mathbb{R}^d$ with Euclidean norm $\|\cdot\|$ and inner product $\langle\cdot,\cdot\rangle$.
- Function class: $f: \mathbb{R}^d\to\mathbb{R}$ is convex and $L$-smooth, i.e., $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for all $x,y$.
- Gradient descent (GD): $x_{n+1}=x_n-\eta\,\nabla f(x_n)$ with constant step size $\eta>0$; the “optimization curve” is the sequence $n\mapsto f(x_n)$. A sequence $(a_n)$ is called convex if the forward differences $\Delta_n:=a_n-a_{n+1}$ are non-increasing, equivalently $a_{n+2}-2a_{n+1}+a_n\ge 0$ for all $n$.
- Gradient flow (GF): $x'(t)=-\nabla f(x(t))$ with solution $t\mapsto x(t)$; the associated optimization curve is $t\mapsto f(x(t))$.
- Baillon–Haddad (cocoercivity): For convex $L$-smooth $f$, $\nabla f$ is $\tfrac1L$-cocoercive: $\langle\nabla f(x)-\nabla f(y),x-y\rangle\ge \tfrac1L\|\nabla f(x)-\nabla f(y)\|^2$.
- Unless otherwise stated, all results hold for every initialization $x_0\in\mathbb{R}^d$.
