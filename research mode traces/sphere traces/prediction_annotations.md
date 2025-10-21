We work in (R^n, ||·||) with Euclidean norm. For x in R^n and r>0, B_n(x,r) denotes the closed Euclidean ball; ω_n = vol_n(B_n(0,1)). For a lattice L = A Z^n (A in GL_n(R)), det(L)=|det A|, minimum λ(L)=min{||v||: v in L\{0}}, and Δ(L):=ω_n (λ(L)/2)^n / det(L). The space of unimodular lattices is 𝓛_n with Haar probability μ.

Additional notation used below:
- Dual lattice: L^* := { y in R^n : ⟨y,ℓ⟩ in Z for all ℓ in L }.
- Successive minima (Euclidean): for 1≤k≤n, λ_k(L) := inf{ r>0 : span{ L ∩ B_n(0,r) } has dimension ≥ k }.
- Voronoi cell: V(L) := { x in R^n : ||x|| ≤ ||x-ℓ|| for all ℓ in L }.
- Covering radius: ρ(L) := sup_{x in R^n} min_{ℓ in L} ||x-ℓ||.
- Kissing number of a lattice packing: τ(L) := |{ v in L\{0} : ||v|| = λ(L) }|.
- Ellipsoids: An origin-symmetric ellipsoid can be written as 𝔈 = { x : ||T x|| ≤ 1 } with T positive definite; its condition number is κ(𝔈):=σ_max(T)/σ_min(T) (equivalently, ratio of largest to smallest semi-axis).
- Spectral gap of the flat torus R^n/L: gap(L) := 4π^2 min_{w in L^*\{0}} ||w||^2 = 4π^2 λ(L^*)^2.
- For matrices, ||·||_{op} denotes the Euclidean operator norm; I is the identity matrix.
- Absolute constants (c,C,c_i,…) are positive and independent of n.