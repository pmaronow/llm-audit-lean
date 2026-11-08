# Blind reading of the Challenge

This file was written and saved before opening `claims.json` or `record.json`.
Only the copied Defs/Challenge sources and the Mathlib definitions they use informed this reading.
All 14 theorem stubs have no outer hypotheses: each asserts the conjunction described below.
The hypotheses inside the conjunctions matter and are recorded explicitly.

## Common objects and exact conventions

Indices are `Fin n`, identified with integers 0 through n−1. A graph is a symmetric Boolean
adjacency array with false diagonal: a finite, undirected, simple graph. Write A for its real
0–1 adjacency matrix, g_i(A) for its degree, B_A=I+A, and E(A) for its unordered edges i<j.
`Compatible R d A` means E(R) is a subset of E(A), and g_i(A)≤d_i for every i.
`Maximizes R d f A` means this compatibility AND f(B)≤f(A) for EVERY compatible B.
There is no connectedness requirement or lower degree requirement besides mandatory R.

For a real vector x, write x̄=Σ_i x_i/n, e=x−x̄1, s²(x)=Σ_i e_i²/n and q_M(x)=Σ_ij M_ij x_i x_j.
Thus s² uses denominator n, not n−1. Define

* V_M(x)=q_M(e)/n²; V₁(A;x)=V_{B_A}(x).
* V₂(A;x)=s²(x)/n · (1+Σ_ij A_ij/n).
* d̃_i=min(d_i,n−1); c_i=0 if d̃_i=0, and c_i=1−1/d̃_i otherwise.
* M⁺(d,A)=B_A+diag(c_i g_i(A)).
* V₁⁺(d,A;x)=V₁(A;x)+Σ_i c_i g_i(A)e_i²/n²=V_{M⁺(d,A)}(x).
* V_Y(d;x)=Σ_i(1+d̃_i)e_i²/n².
* V₂′(d;x)=s²(x)/n · (1+Σ_i d̃_i/n).
* `PSD M` means real symmetry AND q_M(x)≥0 for EVERY real vector x.
* ||x||₂=√Σ_i x_i²; ||M|| is the induced Euclidean operator norm, NOT the norm on plain Pi vectors.
* ||M||_F²=Σ_ij M_ij²; ||x||∞=max_i |x_i|, with value 0 for an empty index set.
* M_+ is Q diag(max(λ_i,0)) Qᵀ using Mathlib's orthonormal eigenbasis for symmetric M;
  for nonsymmetric M the definition instead returns 0. Every spectral application below is symmetric.
* V_+(A;x)=V_{(B_A)_+}(x).

A model m consists of a Borel probability law P on R^n, deterministic real θ_i, a true graph G,
a mandatory graph R, and natural degree caps d_i. Let Y be the coordinate vector, X_i=θ_iY_i,
β̂=X̄, β=Eβ̂, μ_i=EX_i, Σ_ij=E[(X_i−μ_i)(X_j−μ_j)], δ_i=μ_i−β,
b=q_{B_G}(δ)/n, h=Σ_i δ_i²/n, and v̄=Σ_i Σ_ii/n.
`var m f` is E[(f−Ef)²]. All expectations use the Bochner integral, which is defined as 0 for
nonintegrable functions; this totalization must be checked rather than interpreted as existence
of moments. P(E) is `Measure.real`: the real value of the measure/outer measure of E. Probability
laws have finite total mass, so conversion from extended nonnegative reals cannot discard infinity.
For nonmeasurable E this notation uses the measure's outer measure extension.

`Dependency` means: for EVERY pair of disjoint finite index subsets S,T with no graph edge between
them, the whole coordinate subvectors Y_S,Y_T are independent under P. Mathlib `IndepFun` uses
independence of their generated measurable sigma algebras. This is stronger than just pairwise
independence of nonneighbors. `Homoskedastic` means all diagonal entries of the WEIGHTED covariance
Σ are equal.

A family F has positive integer sizes n_k tending to infinity and one model at each k.
`Nested F` means n_k is nondecreasing and, for EACH k, there EXISTS an injection of its vertex set
into the next whose induced graph agrees with G_k. It does not require a coupling of laws or
agreement of θ or means along injections. `Scaling F c₁ c₂ c₃ c₄` means, jointly:

1. Nested F and all four real constants strictly positive;
2. Dependency at EVERY k;
3. at EVERY k, P_k-almost surely, for EVERY i, |X_i−β_k|≤c₁;
4. for EVERY k,i, g_i(G_k)≤c₂;
5. n_k Var(β̂_k)→c₃;
6. for EVERY k,i, |θ_i|<c₄.

`Valid F` is separately quantified: G_k is compatible with R_k,d_k at EVERY k. There is no boundedness
condition on supplied d. In the following use t_k=n_k Var(β̂_k), O_k=n_k V₁(G_k;X),
U=Σ_i(X_i−β)²/n, g=1+Σ_ij(G_k)_ij/n, and Rvar=s²(X)−v̄−h.

`T_k→p a_k` means: for EVERY real ε>0, P_k(|T_k−a_k|>ε)→0.
`Conservative V` means: for EVERY ε>0, P_k(t_k−n_k V_k>ε)→0.
`Tight T` means: for EVERY ε>0 there EXISTS B>0 and k₀ such that for EVERY k≥k₀,
P_k(|T_k|>B)≤ε. No measurability premise is built into these three predicates.
All limits run along natural k→∞, and each statement quantifies constants before its hypotheses.

Φ is the cdf of Mathlib `gaussianReal 0 1`, i.e. mean 0, VARIANCE 1. z_α is the infimum of
{t:1−α/2≤Φ(t)}. Every use of quantiles below restricts 0<α<1.
Cov(V;α)=P(|β̂−β|≤z_α√max(V,0)). `ConservativeCoverage V` means for EVERY α∈(0,1),
liminf_k Cov_k(V_k;α)≥1−α. This is a clipped symmetric normal interval.
Mathlib's real liminf is the supremum of eventual lower bounds (a conditionally complete order
operation). In these uses coverage lies in [0,1]; b_k is bounded under Scaling.

All finite probabilistic examples are pushforwards of uniform distributions on the displayed
finite sign arrays; their underlying sign coordinates are mutually independent fair ±1 variables.

* Cycle family C(a): n_k=4(k+1), θ=1, G=R the disjoint union of (k+1) four-cycles, d=2.
  Each independent block is (a+u₀+u₃, −a+u₀+u₁, a+u₁+u₂, −a+u₂+u₃).
* Path family P(t): n_k=3(k+1), θ=1, G=R the disjoint union of paths 0–1–2,
  d repeating (1,2,1). Each block is (t+U, −2t+3U/5+4V/5, t+V).
* Sign family S: n_k=k+1, independent Y_i=±1, θ=1, G=R empty, d=0.

## SAP.P011a.T1

This is an unconditional conjunction of the following assertions.

For C(3/2), Scaling holds with (c₁,c₂,c₃,c₄)=(7/2,2,4,2), and Valid holds. For EVERY k,
the model is homoskedastic, EY repeats (3/2,−3/2,3/2,−3/2), and Σ=2I+G. For EVERY k,
β=0, t_k=4, b=−9/4, the compatible graph set is EXACTLY {G},
EO_k=7/4−12/n_k, and Var(O_k)=44/n_k−96/n_k²−288/n_k³.
O_k→p7/4. For EVERY ε with 0<ε<9/4, both P(|O_k−4|>ε) and P(4−O_k>ε) tend to 1.
For EVERY real t, P(√n_k β̂_k≤t)→Φ(t/2).
For EVERY α∈(0,1), coverage of V₁(G;X) tends to
2Φ(z_α√(7/16))−1, and this limit is strictly below 1−α.

For C(3), Scaling holds with (5,2,4,2), Valid holds, and for EVERY k homoskedasticity,
β=0 and t_k=4 hold. Its O_k→p−5. In the ONE-block law at a=3,
P(Y=(5,−1,5,−1))=1/16 and V₁(C₄;(5,−1,5,−1))=−9/4.

For EVERY real a, with H having rows (1,0,0,1),(1,1,0,0),(0,1,1,0),(0,0,1,1),
HHᵀ=2I+A_{C₄}, q_{I+A_{C₄}}(a,−a,a,−a)=−4a², and Σ_ij(2I+A_{C₄})_ij=16.
Also the average of (5,−1,5,−1) is 2.

## SAP.P011a.T2

For EVERY real t, IF t=1 OR t=2, all of these hold. P(t) satisfies Scaling(6,2,29/15,2),
Valid, and homoskedasticity at every k. At EVERY k, β=0, t_k=29/15,
the compatible graph set is exactly {G}, and
EO_k=(29−10t²)/15−217/[135(k+1)]. O_k→p(29−10t²)/15.
IF t=1, for EVERY 0<ε<2/3 both P(|O_k−29/15|>ε) and P(29/15−O_k>ε) tend to 1;
for EVERY α∈(0,1), coverage tends to 2Φ(z_α√(19/29))−1<1−α.
IF t=2, P(V₁(G;X)<0)→1 and, for EVERY α∈(0,1), clipped coverage tends to 0.

For EVERY such t, in a single block the uniform four-sign-pair average and the actual expectation
of each coordinate equal (t,−2t,t). The covariance matrix is
[[1,3/5,0],[3/5,1,4/5],[0,4/5,1]], and q_{I+A_path}(t,−2t,t)=−2t².
Writing S=Σ_i Y_i, Q=q_{I+A_path}(Y), L=Σ_ij(I+A_path)_ij Y_j, the four-point expectations are
ES=0, ES²=29/5, EQ=29/5−2t², E[(Q−(29/5−2t²))²]=8t²+8836/625,
E[SL]=14, and q_{I+A_path}(1)=7.

For EVERY such t, THEN EVERY positive integer K, use the 3K×2 design D with intercept column 1
and second column repeating (t,−2t,t). Coordinates of Y are integrable,
EY=D(0,1)ᵀ, and for EVERY real outcome vector y the OLS intercept
[(DᵀD)⁻¹Dᵀy]_0 equals its arithmetic average. There is no theorem asserting the full pointwise
block polynomial expansions or a multiblock centering identity here.

## SAP.P011a.T3

For EVERY family F and real c₁,c₂,c₃,c₄ satisfying Scaling:

* n_k V₁(G_k;X)→p t_k+b_k.
* For EVERY k, |EO_k−t_k−b_k|≤3(1+c₂)²c₁²/n_k.
* s²(X)→p v̄_k+h_k.
* (O_k→p t_k) iff b_k→0.
* Conservative(V₁(G;X)) iff liminf b_k≥0.
* IF δ_i=0 for EVERY k,i, THEN O_k→p t_k.
* IF I+G_k is PSD for EVERY k, THEN V₁(G;X) is Conservative.

Separately, for EVERY positive n and graph A, I+A is PSD iff the relation
i=j OR i adjacent to j is transitive, equivalently every connected component is a clique.
For EVERY label map C:Fin n→N such that adjacency is equivalent to i≠j AND C_i=C_j,
and THEN EVERY vector x,
V₁(A;x)=Σ_{c in image C}(Σ_{i:C_i=c}(x_i−x̄))²/n².
No Valid premise is required for the oracle conclusions.

## SAP.P011a.T4

For EVERY F, real c₁,c₂,c₃,c₄,K, Scaling hypothesis, deterministic sequence of real square matrices M_k,
symmetry at EVERY k, and bound ||M_k||≤K at EVERY k:

* There EXISTS B≥0 and k₀ such that for EVERY k≥k₀,
  Var(q_{M_k}(centered X))≤B n_k.
* n_k V_{M_k}(X)−t_k converges in probability to
  [tr((M_k−B_{G_k})Σ_k)+q_{M_k}(δ_k)]/n_k.
* IF for EVERY k both M_k and M_k−B_{G_k} are PSD, THEN for EVERY k the mean quadratic
  and the preceding trace are nonnegative, AND V_{M_k}(X) is Conservative.

Independently, for EVERY F and c₁,...,c₄ under Scaling, THEN EVERY k and symmetric real M of size n_k,
with H=I−11ᵀ/n_k,
E q_M(centered X)=tr(HMHΣ)+q_M(δ)
=tr(MΣ)+q_M(δ)−(2/n_k)Σ_ij(MΣ)_ij+q_M(1)Var(β̂).
This finite identity is quantified only over models occurring in Scaling families; the separately
defined proposition `QuadraticExpectation` with a general L² premise is NOT a conjunct of T4.

For EVERY positive n and EVERY x∈{−1,1}^n, put M(x)=xxᵀ/n. Then ||M(x)||=1,
tr M(x)=1, n V_{M(x)}(x)=(1−x̄²)².
Under the sign family, n V_{M(Y)}(Y)−1→p0 whereas tr(M(Y)−I)/n→p−1.
The clique characterization and labeled-clique identity from T3 are included verbatim.
Also S satisfies Scaling(1,1,1,2), Valid, and for EVERY k, t_k=1 and β=0.

## SAP.P011a.T5

For EVERY positive n, mandatory graph R, graph A, natural caps d, compatibility hypothesis,
and real vector x, the following ALL hold (write a_i=g_i(A)):

* a_i≤d̃_i for every i;
  M⁺=diag(a)+A+diag(1−[0 if d̃_i=0, else a_i/d̃_i]).
* For EVERY z, q_{diag(a)+A}(z)=Σ_{i<j}A_ij(z_i+z_j)².
* M⁺ is PSD, M⁺−B_A is PSD, V₁⁺=V_{M⁺}, and V₁⁺≥0.
* I+diag(d̃), diag(d̃)−A, diag(d̃)−diag(a), and diag(a)−A are all PSD.
* (I+diag(d̃))−B_A=(diag(d̃)−diag(a))+(diag(a)−A).
* For EVERY z, q_{diag(a)−A}(z)=Σ_{i<j}A_ij(z_i−z_j)².
* V₁(A;x)≤V_Y(d;x), and
  n²V₁⁺=Σ_i e_i²+2Σ_{i<j}A_ij[e_i e_j+(c_i e_i²+c_j e_j²)/2].
* For EVERY natural D, IF d̃_i=D for EVERY i, THEN
  V_Y=V₂′=s²(x)(1+D)/n.
* For EVERY natural d₀,D, IF D≥1, a_i=d₀ and d̃_i=D for EVERY i, THEN
  V₁⁺=V₁+d₀(1−1/D)Σ_i e_i²/n².
* For EVERY natural d₀≥1 with a_i=d̃_i=d₀ for EVERY i,
  V₁⁺=V₁+(d₀−1)Σ_i e_i²/n².
* IF a_i=0 for EVERY i, THEN V₁⁺=V₁.

For EVERY Scaling family and constants, THEN Valid, THEN a graph-valued choice A_k(y),
IF at EVERY k,y it maximizes corrected V₁⁺ over compatible graphs, THEN
||M⁺(d_k,G_k)||≤1+2c₂ at EVERY k, corrected oracle≤corrected maximum at EVERY k,y,
and all FOUR of corrected oracle, corrected maximum, V_Y, and their minimum
min(corrected maximum,V_Y) are Conservative. IF d̃ is constant over vertices at EACH k
(the constant may depend on k), V₂′ is also Conservative. No uniform bound on supplied caps.
The conclusions about the oracle and V_Y occur under this same maximizer premise.

Finally, for EVERY positive n, R,A,d,x, IF A maximizes V₁⁺, THEN A maximizes the edge objective
W(A)=Σ_{i<j}A_ij[e_i e_j+(c_i e_i²+c_j e_j²)/2] among compatible graphs,
and n²V₁⁺=Σ_i e_i²+2W(A).

## SAP.P011a.T6

For EVERY positive n and graph A, (B_A)_+ and (B_A)_+−B_A are PSD,
||(B_A)_+||≤1+max_i g_i(A), and for EVERY x, max(V₁(A;x),0)≤V_+(A;x).
For EVERY PSD M, ||(B_A)_+−B_A||_F²≤||M−B_A||_F².
For EVERY n (including 0), A, and PSD M attaining equality of these distances,
M=(B_A)_+. For EVERY Scaling family and constants, V_+(G;X) is Conservative.

For the four-cycle, let D have rows
(17/20,−1/4,1/4,−17/20), (−1/4,3/20,−3/20,1/4),
(1/4,−3/20,3/20,−1/4), (−17/20,1/4,−1/4,17/20).
Both D and B_{C₄}+D are PSD. At x=(0,1,−1,0), q_{B+D}(x)=3/5 whereas q_{B_+}(x)=1.
For C(3/2), EVERY k has t_k=4 and E[n_k V_+(G;X)]=4−12/n_k;
also n_k V_+(G;X)→p4.

There do NOT EXIST c∈R and arbitrary real weights w_ij on three vertices such that for EVERY
graph A on three vertices, V_+(A;(1,−2,1))=c+Σ_{i<j}w_ij A_ij.

Let Q be the matrix with rows
(1/2,1/2,1/2,1/2), (1/2,1/2,−1/2,−1/2),
(1/2,−1/2,−1/2,1/2), (1/2,−1/2,1/2,−1/2).
Then QᵀQ=I and B_{C₄}=Q diag(3,1,1,−1)Qᵀ. For EVERY x,
q_{Q diag(3,1,1,0)Qᵀ}(x)=q_B(x)+(x₀−x₁+x₂−x₃)²/4;
the SAME formula holds with the actual (B_{C₄})_+ on the left, which also equals
3(x₀+x₁+x₂+x₃)²/4+[(x₀−x₂)²+(x₁−x₃)²]/2.
For EVERY n, real Hermitian M and its chosen Mathlib eigenbasis Q and eigenvalues λ,
M_+−M=Q diag(max(λ_i,0)−λ_i)Qᵀ.

## SAP.P011a.T7

For EVERY positive n, graph A, vector x,
q_A(e)=Σ_i g_i(A)e_i²−Σ_{i<j}A_ij(e_i−e_j)².
For EVERY positive n, caps d, natural D satisfying d̃_i≤D for EVERY i, THEN EVERY x:

* For EVERY A maximizing uncorrected V₁ with R empty,
  0≤n(V_Y−V₁(A))≤[Σ_{r=1}^D(3r²+2r)]||e||∞²/n.
* For EVERY A⁺ maximizing V₁⁺ with R empty,
  0≤Σ_i max(1,2d̃_i)e_i²/n−nV₁⁺(A⁺)
  ≤||e||∞²/n · Σ_{r=1}^D(4r²+r).

For EVERY Scaling family, constants, Valid, R_k empty for EVERY k, and choice A_k(y)
maximizing uncorrected V₁ for EVERY k,y, V₁(A_k;X) is Conservative.

For EVERY choice A_k(y) maximizing V₁ on k+1 vertices with empty R and caps d_i=k at EVERY k,y:
for EVERY k,y∈{−1,1}^{k+1}, V₁(A_k(y);y)=(1−ȳ²)²/2 and V_Y(k;y)=1−ȳ².
Under the sign LAW, these two unscaled statistics converge in probability to 1/2 and 1 respectively.
This uses new supplied caps k in the statistics/optimization; the predefined sign MODEL still has d=0.
Also the SignWitnessFacts stated in T4 hold. No coverage assertion is included in T7.

## SAP.P011a.T8

For EVERY F and real constants satisfying Scaling, THEN EVERY statistic V in the following union,
V is Conservative AND has ConservativeCoverage:

1. Valid holds, and V is corrected oracle V₁⁺, or V_Y, or there EXISTS a choice A_k(y)
   maximizing V₁⁺ at EVERY k,y and V is its value or min(its value,V_Y).
2. V is spectral oracle V_+(G;X); Valid is not required in this branch.
3. Valid holds, R is empty at EVERY k, and there EXISTS a choice maximizing V₁ at EVERY k,y,
   with V equal to its value.
4. Valid holds and liminf b_k≥0, and V is uncorrected oracle V₁, or there EXISTS a choice
   maximizing V₁ at EVERY k,y with V equal to its value.

Independently, for EVERY Scaling family and constants with Valid, IF E X_i=β for EVERY k,i
OR G_k is a union of cliques for EVERY k, THEN oracle V₁ is Conservative and has
ConservativeCoverage; THEN for EVERY choice maximizing V₁ at EVERY k,y its value has both properties.
All of CycleCounterexample (as expanded under T1) and PathCounterexample (the probabilistic first
paragraph of T2) are also conjuncts. The finite algebra/moment/OLS additions of T1/T2 are not
thereby included.

## SAP.P011a.T9

For residual assertions use deterministic designs D_k with a FIXED natural number p of columns,
fixed γ∈R^p and fitted maps γ̂_k:R^{n_k}→R^p. A mean model means coordinate Y_i is integrable
for EVERY i AND EY=Dγ. Write z_i=θ_i(Y_i−(Dγ)_i), r_i=θ_i(Y_i−(Dγ̂)_i),
and V_res(A;r)=q_{B_A}(r)/n² (there is NO further sample centering).

For EVERY Scaling family and constants, THEN p,D,γ,γ̂, assume EVERY γ̂_k is measurable,
EVERY model is this mean model, there EXISTS a finite B bounding the Euclidean norm of EVERY
row D_k i, and √n_k||γ̂_k−γ||₂ is Tight. THEN for EVERY choice A_k(y), under Valid and
the premise that it maximizes V_res(A;r) at EVERY k,y:

* E z_i=0 for EVERY k,i, and E(z_i z_j)=Σ_ij for EVERY k,i,j;
* √n_k||r−z||∞, ||r−z||₂, and ||z||₂/√n_k are all Tight;
* n_k V_res(G_k;r)→p t_k;
* V_res(A_k;r) is Conservative.

Separately, for EVERY Scaling family, constants, p,D,γ,γ̂ with measurable γ̂ and the mean model,
IF there EXISTS B bounding |z_i| almost surely uniformly in k,i AND ||r−z||₂/√n_k→p0,
THEN for EVERY choice A under Valid and the same maximization premise,
n_k V_res(G;r)→p t_k and the maximized residual statistic is Conservative.

Separately, for EVERY Scaling family, constants, p,D,γ*,γ̂ with measurable γ̂,
NO mean-model premise, IF z*=θ(Y−Dγ*) has a uniform almost-sure coordinate bound and
||r−z*||₂/√n_k→p0, THEN n_k V_res(G;r)−t_k→p q_{B_G}(m*)/n_k,
where m*_i=E X_i−θ_i(Dγ*)_i. No Valid or maximization is required here.

For EVERY n (including 0), symmetric real M, r,z,
|q_M(r)−q_M(z)|≤||M||·||r−z||₂·(2||z||₂+||r−z||₂).

The concrete unstable family has n=4(k+1), independent signs ε_i,
Y_i=ε_i for even i and Y_i=n ε_i for odd i, θ repeating (2,0,−2,0), G=R empty, d=0.
It satisfies Scaling(2,1,2,3). For EVERY k use D with intercept 1 and second column repeating
(1,0,−1,0). It is an integrable mean model with γ=0. The OLS intercept variance is
n/2+1/(2n), and E[n V_res(G; fitted weighted OLS residuals)]=n+2−7/n.
It is FALSE that these scaled residual statistics converge in probability to 2.
OLS is defined by the ordinary totalized matrix inverse (DᵀD)⁻¹Dᵀy; all concrete designs here
have independent columns for the positive sample sizes in use.

## SAP.P011a.T10

For a,b∈R and a fixed infinite Boolean sequence s, fixed-mean observations are independently
Y_i=a sign(s_i)+b ε_i. The mixture observations independently have Y_i=a S_i+b ε_i, with all
S_i,ε_i fair independent signs. In both models θ=1, G=R empty, d=0; families use n_k=k+1.

For EVERY a>0, THEN EVERY b>0:

* For EVERY infinite s, the fixed-mean family satisfies Scaling(2a+b,1,b²,2).
  The mixture family satisfies Scaling(a+b,1,a²+b²,2).
* For EVERY natural n, including 0, the mixture law is EXACTLY the sum over s∈{false,true}^n
  of 2^{−n} times the fixed-mean law, extending that finite s by false outside its prefix.
* There does NOT EXIST a single sequence of measurable statistics T_k:R^{k+1}→R such that
  for EVERY infinite s, T_k→p b² under that fixed-mean family, AND T_k→p a²+b² under the mixture.
  These T_k are already in units of SCALED variance; no n multiplier is present in this predicate.
* For EVERY sequence T_k of measurable statistics, IF for EVERY ε>0,
  P_mix(a²+b²−T_k>ε)→0, THEN it is FALSE that for EVERY infinite s,
  T_k→p b² under the fixed-mean family.

Independently, for EVERY real a,b (no sign restriction), EVERY infinite s, EVERY positive n:
in the fixed-mean law, EY_i=a sign(s_i) and Var(Y_i)=b² for EVERY i,
β=average_i a sign(s_i), and n Var(β̂)=b². In the mixture law, EY_i=0 and
Var(Y_i)=a²+b² for EVERY i, β=0, and n Var(β̂)=a²+b².

## SAP.P011a.T11

The alternating family has n=k+1, independent signs ε_i,
Y_i=2+ε_i at even i, Y_i=ε_i at odd i, θ_i=t=n/[2 ceil(n/2)], empty G,R and d=0.
It satisfies Scaling(2,1,1,2), Valid, and for EVERY k homoskedasticity, β=1,
and t_k=t². Its n V₂(G;X)−t_k→p1. Both
P(|nV₂−t_k|>1/2)→1 and P(|nV₂−t_k|<3/2)→1. V₂ is nevertheless Conservative.

For EVERY k (so n≥1): 1/2≤t≤1, β=1, Σ_ii=t² and δ_i=t(2 if i even, else 0)−1
for EVERY i. Put p_n=ceil(n/2)−floor(n/2). Then h=t²(1−p_n²/n²).
For EVERY sign realization ε,
s²(X)=t²+h+2tΣ_i δ_i ε_i/n−t²(Σ_i ε_i)²/n².
E Rvar=−t²/n and E Rvar²=4t²h/n+t⁴(3/n²−2/n³).
IF n is even, THEN t=h=1,
E(nV₂−2)²=4/n+3/n²−2/n³, and EACH of
P(|nV₂−1|>1/2), P(|nV₂−1|<3/2) is at least 1−4(4/n+3/n²−2/n³).

Define ρ_ij=0 if v̄=0, otherwise Σ_ij/v̄, and V₂*=s²(X)/n ·(1+Σ_ij G_ijρ_ij/n).
For EVERY k and EVERY outcome y, V₂*=V₂, nV₂=s²(X),
and nV₂*−t_k=h+Rvar. The zero-variance branch in ρ is unused in this positive-variance family;
the graph also has no edges.

## SAP.P011a.T12

For EVERY Scaling family and constants, IF homoskedasticity holds for EVERY k, THEN
at EVERY k (use n=n_k):

* For EVERY outcome y, s²(X)=U−(β̂−β)².
* EU=v̄+h; Var(U)≤(1+c₂)c₁⁴/n.
* E(β̂−β)²≤(1+c₂)c₁²/n and E(β̂−β)⁴≤(1+c₂)c₁⁴/n.
* E Rvar²≤4(1+c₂)c₁⁴/n.
* t_k≤v̄g and 1≤g≤1+c₂.
* For EVERY outcome y, nV₂=g s²(X), and t_k−nV₂≤(1+c₂)|Rvar|.
* For EVERY ε>0,
  P(t_k−nV₂>ε)≤4(1+c₂)³c₁⁴/(n ε²).

V₂(G;X) is Conservative.
Also, at EVERY k, v̄=Σ_ii for EVERY i, h≥0, t_k=Σ_ijΣ_ij/n, and for EVERY outcome y
t_k−nV₂≤g(v̄−s²(X))=−g(h+Rvar)≤(1+c₂)|Rvar|.
No Valid, supplied-cap bound, or coverage assertion is used or concluded.

## SAP.P011a.T13

For n vertices let E_n={(i,j):i<j}. A degree problem P is a mandatory finite edge set F,
natural caps d_i, and RATIONAL weights w_e. Feasible S means F⊆S and deg_i S≤d_i.
Write O=E_n\F, b_i=min(d_i,n−1)−deg_i F, using NATURAL truncated subtraction,
L=lcm_{e∈O} denominator(w_e), integer w̃_e=L numerator(w_e)/denominator(w_e),
M=1+max_{e∈O}|w̃_e|. The empty lcm is 1 and empty max is 0.
Gadget vertices are one vertex (i,s) for EACH 0≤s<b_i and two separate vertices (e,false),(e,true)
for EACH optional edge e. Gadget edges are the internal pair for each e (weight 4M),
and for each endpoint i of e all edges from its (e,side) vertex to slots (i,s) (weight 2M+w̃_e).
A matching is a finite set of gadget edges with no shared endpoint between distinct edges.
Decode(J) consists of optional e for which BOTH endpoint gadget vertices have a slot edge in J.

For EVERY positive n and degree problem P:

* There EXISTS feasible S iff for EVERY i, deg_i F≤min(d_i,n−1).
* IF this last feasibility condition holds, THEN for EVERY S, S is feasible iff there EXISTS
  T⊆O with deg_i T≤b_i for EVERY i and S=F∪T.
* Under that same feasibility condition, for EVERY gadget edge set J, IF J is a matching and
  for EVERY matching J′ its integer weight is ≤weight(J), THEN F∪Decode(J) is feasible,
  EVERY feasible S has objective ≤ its objective, and its objective equals
  Σ_{e∈F}w_e+[weight(J)−4M|O|]/(2L).
* Unconditionally, 2|O|+Σ_i b_i≤2n(n−1), and
  |O|+Σ_{e=(i,j)∈O}(b_i+b_j)≤|O|(2n−1).

For EVERY natural n (including 0) and P, the actual gadget cardinalities are EXACTLY
2|O|+Σ_i b_i vertices and |O|+Σ_{e=(i,j)∈O}(b_i+b_j) edges.

Two four-vertex instances use residual vector (3/2,1/2,−1/2,−3/2) and weights its pair products.
Instance false has F={(0,2),(2,3)}, caps (2,1,2,7), b=(1,1,0,2), |O|=4;
instance true has F={(0,2)}, caps (1,1,1,1), b=(0,1,0,1), |O|=5.
For BOTH instances L=4 and M=10. Explicit optimal S are respectively F∪{(0,1)} with value 3/4
and F with value −3/4; each is feasible and dominates EVERY feasible T.
For EACH instance there EXISTS a maximum gadget matching, with weights respectively 166 and 200.
No GENERAL existence of a maximum matching or algorithm runtime is asserted.

## SAP.P011a.T14

For EVERY positive n, mandatory graph R, natural caps d, real edge weights w, real U,
IF for EVERY relaxed vector a:E_n→R satisfying 0≤a_e≤1, a_e=1 on edges of R,
and Σ_{e incident i}a_e≤d_i at EVERY i, one has Σ_e w_e a_e≤U, THEN:

* For EVERY Boolean edge vector a whose simple graph is compatible, Σ_{e:a_e}w_e≤U.
* For EVERY real vector x and Boolean a with compatible graph, IF w_e=(x_i−x̄)(x_j−x̄)
  for EVERY e=(i,j), THEN V₁(A;x)≤[n s²(x)+2U]/n².
* IF w_e=1 for EVERY e, THEN for EVERY x and compatible Boolean a,
  V₂(A;x)≤s²(x)/n ·(1+2U/n).

On six vertices with x=(1,1,1,−1,−1,−1), empty R and all caps 1, let w_e=x_i x_j,
and f_e=1/2 for same-sign endpoints and 0 otherwise. Then f is relaxed feasible with
objective 3, EVERY relaxed feasible vector has objective ≤3, and there EXISTS an integer
feasible graph with objective 2 and V₁=5/18, while EVERY integer feasible graph has objective ≤2.
The corresponding relaxed bound is (6+2·3)/6²=1/3.
The theorem also names the integer witness {(0,1),(3,4)} and asserts exactly its compatibility,
objective 2 and V₁=5/18. It asserts average x=0, s²(x)=1, relaxed doubled objective 6,
integer doubled objective 4 (with both upper bounds and attainment), and relaxed variance value 1/3.
There ALSO EXIST a relaxed feasible vector a₀ and integer feasible vector a with
objective(a₀)<objective(a): an arbitrary feasible relaxed point need not be an upper bound.

On three vertices with empty R, caps 1 and unit weights, constant a_e=1/2 is relaxed feasible,
its objective is 3/2 (doubled objective 3), EVERY relaxed feasible vector has objective ≤3/2,
there EXISTS an integer compatible graph with directed adjacency sum 2, and EVERY compatible
graph has directed adjacency sum ≤2. Thus the integer undirected optimum is 1.

## Mathlib definition checks made during the blind stage

* `Probability/Distributions/Uniform.lean:275–282`: each point of a finite nonempty type has mass 1/card.
* `Probability/ProbabilityMassFunction/Basic.lean:214` and PMF mapping: finite pushforward law.
* `Probability/Independence/Basic.lean:144` and its kernel definition: independence of generated sigma algebras.
* `MeasureTheory/Integral/Bochner/Basic.lean:158`: integral is 0 outside integrability.
* `MeasureTheory/Measure/Real.lean`: measure real is `(μ E).toReal`.
* `Probability/Distributions/Gaussian/Real.lean:222` and `Probability/CDF.lean:57–85`:
  Gaussian parameters are mean and variance; cdf is the probability of (−∞,t].
* `Order/LiminfLimsup.lean:54–68` (dual definitions): real liminf is supremum of eventual lower bounds.
* `Analysis/InnerProductSpace/PiL2.lean:1242`: `toEuclideanLin` is the linear map between Euclidean spaces.
* `Analysis/Matrix/Spectrum.lean:60–105`: eigenvalues and the unitary matrix whose COLUMNS are its eigenvectors.
* `LinearAlgebra/Matrix/Hermitian.lean:44`: Hermitian means conjugate transpose equals self; over R this is symmetry.

Division in R and the matrix inverse are totalized, but positive n is supplied wherever finite
variance denominators matter. The natural subtraction for b_i is mathematically ordinary subtraction
under the explicit feasibility premise; the unconditional cardinality/size statements still use its
literal nonnegative truncation. Empty index types occur only in harmless extra finite identities.
