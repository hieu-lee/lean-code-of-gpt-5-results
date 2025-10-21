Conventions and notation (all graphs finite and simple unless noted):
- G=(V,E) is a graph; E(v) denotes the set of edges incident to v; d(v)=|E(v)|; Δ(G), δ(G) are the maximum and minimum degrees.
- A component isomorphic to K_2 is a K_2-component. A graph with no K_2-component (i.e., no isolated edge) is called nice.
- For k∈ℕ, write [k]:={1,2,…,k}. A k-edge-weighting is a map ω:E→[k]. The weighted degree (sum-color) of v under ω is s_ω(v):=∑_{e∈E(v)} ω(e).
- A k-edge-weighting ω is neighbor-sum distinguishing (NSD) if ∀uv∈E we have s_ω(u)≠s_ω(v).
- For hypergraphs H=(V,𝔈), s_ω(v):=∑_{e∈𝔈, v∈e} ω(e). We call ω edge-proper by sums if every e∈𝔈 contains u,v with s_ω(u)≠s_ω(v).
- Total weighting: φ:V∪E→ℝ with vertex-sum S_φ(v):=φ(v)+∑_{e∈E(v)} φ(e). A graph is (k,k′)-total weight choosable if for every list assignment L with |L(v)|=k (v∈V), |L(e)|=k′ (e∈E), there exists a proper total L-weighting φ (i.e., S_φ(u)≠S_φ(v) for all uv∈E).
- Multiplicative variant: p_ω(v):=∏_{e∈E(v)} ω(e). A weighting ω is multiplicative-NSD if ∀uv∈E, p_ω(u)≠p_ω(v).
- Logs are natural; constants c>0 are absolute unless specified.