Proof. Suppose, for contradiction, that there exist $C>0$ and a function $g$ with $\sup_\Delta g(\Delta)>C$ such that for every $G=C_n\sqcup K_{1,\Delta}$ and every weighting $\omega:E(G)\to\{1,2,3\}$ that assigns weight $2$ to each edge of $C_n$, if Stage 2 resamples exactly the edges in
$$\operatorname{Bad}_1(\omega):=\{uv\in E(G): |s_\omega(u)-s_\omega(v)|\le1\},$$
then the expected number resampled is at most $C\,|E(G)|/g(\Delta)$. Here $s_\omega(v)$ is the sum of weights on edges incident to $v$.

Choose $\Delta$ with $g(\Delta)>C$ (possible since $\sup_\Delta g(\Delta)>C$), and set $\alpha:=C/g(\Delta)\in(0,1)$. Then choose $n$ so large that
$$ n>\frac{\alpha\,\Delta}{1-\alpha}. $$
Consider $G=C_n\sqcup K_{1,\Delta}$ and a weighting $\omega$ that assigns weight $2$ to every edge of $C_n$ (and arbitrary weights in $\{1,2,3\}$ on the star).

- Cycle: every vertex of $C_n$ has weighted degree $4$, so for each cycle edge $uv$ we have $|s_\omega(u)-s_\omega(v)|=0\le1$. Hence all $n$ cycle edges lie in $\operatorname{Bad}_1(\omega)$, and therefore $|\operatorname{Bad}_1(\omega)|\ge n$.

Since Stage 2 resamples exactly the edges in $\operatorname{Bad}_1(\omega)$, the number resampled is deterministically at least $n$, so the expectation is at least $n$. The assumed bound would then give
$$ n\le \frac{C\,|E(G)|}{g(\Delta)}=\frac{C\,(n+\Delta)}{g(\Delta)}=\alpha(n+\Delta), $$
which contradicts the choice of $n$ (equivalently, $n(1-\alpha)>\alpha\Delta$). This contradiction shows that no such $C$ and $g$ exist. ∎