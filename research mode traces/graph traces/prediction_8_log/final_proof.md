Proof (by contradiction). Assume there exists c0>0 such that whenever G is a d-regular expander on n vertices with adjacency spectral gap at least c0 and n sufficiently large, then R_3(G) is connected and the single-edge resampling Markov chain on R_3(G) is rapidly mixing.

Fix c0>0. Choose an integer m'≥17 large enough that
$$\min\{\,m',\;2\big(m'-2\sqrt{m'-1}\big)\,\}\ge c_0.$$
Let N be large, and let P=P_N be an m'-regular bipartite Ramanujan graph on bipartition (L_0,R_0) with |L_0|=|R_0|=N (any family with \(\sigma_2(P)\le 2\sqrt{m'-1}\) suffices).

Construct a graph Y=Y_N as follows.
- Vertex set: for each coarse vertex x∈L_0∪R_0 create a fiber of 3 vertices (x,1),(x,2),(x,3). Thus |V(Y)|=6N. Write L_i:=\{(ℓ,i):ℓ∈L_0\} and R_i:=\{(r,i):r∈R_0\} for i∈\{1,2,3\}.
- H-edges (intra-fiber triangles): for every x∈L_0∪R_0, add the 3 edges of K_3 on \{(x,1),(x,2),(x,3)\}.
- B-edges (across L–R): for every coarse edge ℓr∈E(P) and every i∈\{1,2,3\}, add the two edges ((ℓ,i),(r,i)) and ((ℓ,i),(r,i+1 mod 3)).

Each vertex has 2m' B-neighbors and 2 H-neighbors; hence Y is d-regular with d=2m'+2. Connectivity of Y follows since P is connected and the B-edges change the index i by 0 or +1 mod 3, so B-edges alone connect all layers; adding H-edges preserves connectivity.

Spectral gap. Let A(Y)=B+A_H, where B is the adjacency of the B-edges and A_H that of the disjoint union of all intra-fiber triangles. Then \(\|A_H\|=2\). Order the vertices so that the bipartition is (L_1∪L_2∪L_3)∪(R_1∪R_2∪R_3) and write
$$B=\begin{pmatrix}0&C\\ C^\top&0\end{pmatrix},\qquad C=(I_3+S)\otimes P,$$
where S is the 3×3 cyclic shift. Since S is unitary, I_3+S is normal with eigenvalues 2,1,1, so its singular values are 2,1,1. Hence the nonzero eigenvalues of B are ±σ_j(C) with
$$\sigma(C)=\{\,2\sigma_j(P),\;\sigma_j(P),\;\sigma_j(P):\;j=1,\dots,N\,\}.$$
Because P is m'-regular bipartite, \(\sigma_1(P)=m'\) and \(\sigma_2(P)\le 2\sqrt{m'-1}\). Therefore
$$\lambda_1(B)=2m',\qquad \lambda_2(B)=\max\{2\sigma_2(P),\,m'\}.$$
For any unit x⊥1,
$$x^\top A(Y)x=x^\top Bx+x^\top A_Hx\le \lambda_2(B)+\|A_H\|\le \max\{2\sigma_2(P),m'\}+2.$$
Since \(\lambda_1(A(Y))=d=2m'+2\),
$$\operatorname{gap}(Y):=\lambda_1(A(Y)) - \lambda_2(A(Y))\ge (2m'+2) - (\max\{2\sigma_2(P),m'\}+2)=\min\{m',\,2(m'-\sigma_2(P))\}\ge c_0.$$
Thus Y is a d-regular expander with adjacency spectral gap at least c0, and |V(Y)|=6N grows with N.

Triangle gadget. On K_3, any NSD \{1,2,3\}-weighting uses weights 1,2,3 once and induces vertex sums \{3,4,5\}. Fix the canonical labeling of the three vertices by their H-sums 3,4,5 and set
$$w(3\text{--}4)=1,\quad w(4\text{--}5)=3,\quad w(5\text{--}3)=2.$$
Changing any one H-edge to either of its two other values adjusts the two endpoint sums by ±1 or ±2, while the third vertex is unchanged; a direct check shows that in each of the six possibilities one of the changed endpoints hits the unchanged third value, so that triangle acquires a bad edge.

Define two \{1,2,3\}-weightings ω,ω' of Y.
- For ω, give every B-edge weight 2. In each L-fiber use the canonical triangle; in each R-fiber use the canonical triangle cyclically shifted so that the H-sums at indices i=1,2,3 are (4,5,3) respectively (while on L they are (3,4,5)). Write B_x(i)∈\{3,4,5\} for the H-sum at (x,i). Because every vertex has exactly 2m' B-neighbors of weight 2, its B-contribution is 4m', so
$$s_\omega(x,i)=4m'+B_x(i).\tag{$\ast$}$$
- For ω', keep all H-edges as in ω, but give every B-edge weight 1. Then for all (x,i),
$$s_{\omega'}(x,i)=2m'+B_x(i).\tag{$\ast\ast$}$$

We now prove ω is NSD and isolated in R_3(Y), and ω' is NSD (hence R_3(Y) is disconnected).

NSD of ω.
- On every H-edge within a fiber x, by (\*) the two endpoint sums differ by \(B_x(i)-B_x(j)\in\{\pm1,\pm2\}\setminus\{0\}\).
- On every B-edge, edges join (ℓ,i)∈L_i to (r,j)∈R_j only for j∈\{i,i+1\}; with the chosen H-sums on L and R, the ordered pair (B_ℓ(i),B_r(j)) lies in
\{(3,4),(4,5),(5,3),(3,5),(4,3),(5,4)\},
so again \(s_\omega(\ell,i)-s_\omega(r,j)=B_\ell(i)-B_r(j)\in\{\pm1,\pm2\}\setminus\{0\}\). Thus ω is neighbor-sum distinguishing.

Isolation of ω in R_3(Y). Consider any single-edge resampling from ω.
- Case H (resampling an H-edge within a fixed triangle). Only the two incident vertex sums change (by ±1 or ±2), the third vertex in that triangle stays unchanged, and by the triangle blocking property one of the two changed endpoints assumes the third vertex’s H-sum. Since all three vertices in the triangle share the same B-contribution 4m' in (\*), this equality persists for the full sums; hence a bad H-edge is created.
- Case B (resampling a B-edge e=((ℓ,i),(r,j))). Here j∈\{i,i+1\} and only the two endpoints change, each by \(\delta\in\{\pm1\}\). Inspecting the six pairs above, in each case and for each sign of δ one changed endpoint matches the unchanged H-sum of one of its two triangle-neighbors, thereby creating a bad H-edge. Concretely:
  - (3,4): δ=+1 makes 3→4 on the left (collision with the left vertex of H-sum 4); δ=−1 makes 4→3 on the right.
  - (4,5): δ=+1 makes 4→5 on the left; δ=−1 makes 5→4 on the right.
  - (5,3): δ=+1 makes 3→4 on the right; δ=−1 makes 5→4 on the left.
  - (3,5): δ=+1 makes 3→4 on the left; δ=−1 makes 5→4 on the right.
  - (4,3): δ=+1 makes 4→5 on the left; δ=−1 makes 4→3 on the left.
  - (5,4): δ=+1 makes 4→5 on the right; δ=−1 makes 5→4 on the left.
In all cases the resampled weighting is not NSD, so ω has degree 0 in R_3(Y).

NSD of ω'. Using (\*\*) the same H- and B-edge checks as above (with 4m' replaced by 2m') show that ω' is NSD and ω'≠ω.

Conclusion and contradiction. For the fixed degree d=2m'+2, the graphs Y_N form an infinite family of d-regular expanders with adjacency spectral gap at least c0. Since ω is isolated in R_3(Y_N) while ω' is another NSD weighting, R_3(Y_N) is disconnected for all large N. This contradicts the assumption that for the universal constant c0, all sufficiently large d-regular expanders with adjacency spectral gap at least c0 have connected R_3(G) (and, in particular, an irreducible and rapidly mixing single-edge resampling chain). Therefore, no such c0 exists. ∎