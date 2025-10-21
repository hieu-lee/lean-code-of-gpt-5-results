Proof. An NSD 3-edge-weighting is a map $\omega:E(C_4)\to\{1,2,3\}$ such that for each edge $uv$, the weighted degrees $s_\omega(u)$ and $s_\omega(v)$ (sums of incident edge weights) are distinct. A parity profile is a pair $(p_A,p_B)\in\{0,1\}^2$ such that $s_\omega(v)\equiv p_A\pmod2$ for all $v\in A$ and $s_\omega(v)\equiv p_B\pmod2$ for all $v\in B$.

Label the edges around the cycle by
$$e_1=a_1b_1,\ e_2=b_1a_2,\ e_3=a_2b_2,\ e_4=b_2a_1.$$
We exhibit NSD 3-edge-weightings for three distinct parity profiles and then exclude $(1,1)$.

- Profile $(0,1)$: set $\omega(e_1)=2,\ \omega(e_2)=1,\ \omega(e_3)=1,\ \omega(e_4)=2$. Then
  $$s_\omega(a_1)=2+2=4,\ s_\omega(b_1)=2+1=3,\ s_\omega(a_2)=1+1=2,\ s_\omega(b_2)=1+2=3,$$
  so parities are even on $A$ and odd on $B$, and along each edge the endpoint sums differ.

- Profile $(1,0)$: set $\omega(e_1)=2,\ \omega(e_2)=2,\ \omega(e_3)=1,\ \omega(e_4)=3$. Then
  $$s_\omega(a_1)=2+3=5,\ s_\omega(b_1)=2+2=4,\ s_\omega(a_2)=2+1=3,\ s_\omega(b_2)=1+3=4,$$
  giving odd on $A$ and even on $B$, with distinct sums across every edge.

- Profile $(0,0)$: set $\omega(e_1)=1,\ \omega(e_2)=1,\ \omega(e_3)=3,\ \omega(e_4)=3$. Then
  $$s_\omega(a_1)=1+3=4,\ s_\omega(b_1)=1+1=2,\ s_\omega(a_2)=1+3=4,\ s_\omega(b_2)=3+3=6,$$
  so both parts have even sums and adjacency sums differ.

It remains to rule out $(1,1)$. Since every vertex of $C_4$ has degree $2$, if all weighted degrees were odd, then at each vertex exactly one incident edge would have odd weight. Hence the odd-weight edges form a perfect matching $M$, and every non-matching edge must have even weight, i.e., weight $2$. For any $uv\in M$, both $u$ and $v$ are incident with $uv$ and one edge of weight $2$, so $s_\omega(u)=\omega(uv)+2=s_\omega(v)$, contradicting the NSD property. Thus $(1,1)$ is impossible.

Therefore the realized parity profiles on $C_4$ are exactly $(0,0),(0,1),(1,0)$. ∎