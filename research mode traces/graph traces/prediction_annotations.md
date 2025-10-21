We retain all conventions from the literature annotations. Additional notation used below:
- For a real interval I, an edge-weighting ω:E(G)→I is called t-strong if |s_ω(u)−s_ω(v)|≥t for every edge uv∈E(G). We write Bad_t(ω):={uv∈E(G): |s_ω(u)−s_ω(v)|≤t}.
- For a graph class 𝒢, we say that NSD 3-edge-weightings are c-locally-reconfigurable in 𝒢 if for every G∈𝒢 and every NSD 3-edge-weighting ω there is a sequence of NSD 3-edge-weightings from ω to some canonical NSD 3-edge-weighting that changes at most c incident edges at any vertex at each step.
- For bipartite graphs with bipartition (A,B), let par_ω(v)=s_ω(v) mod 2. The parity profile of ω is (par_ω(A),par_ω(B)) where par_ω(X)=∑_{v∈X} par_ω(v) mod 2.
- For integers k≥1 and ℓ≥0, an NSD k-edge-weighting ω is ℓ-slack if |s_ω(u)−s_ω(v)|≥1+ℓ for all edges uv.
- For Δ≥1, let θ_{Δ}(G):=min_{ω:E(G)→{1,2,3}} |{uv∈E(G): |s_ω(u)−s_ω(v)|≤1}|/|E(G)|.
- For graphs G,H, write G□H for the Cartesian product; K_2□G is the “layered double” of G.
- A graph is triangle-sparse if tri(G)≤|E(G)|^2/|V(G)|.
- For a list assignment L:E(G)→2^{
{1,2,3}}, say L is α-dense if |L(e)|≥2 for all e and for every v, at most α·deg_G(v) incident edges e have |L(e)|=2.
- For p∈(0,1), G_p is the binomial random subgraph obtained by retaining each edge independently with probability p.
- All asymptotics “a.a.s.” are with respect to the natural size parameter indicated (e.g., Δ→∞ or n→∞ as specified in each statement).
