# Blind reading of the Challenge

This file was written from `SAP/P011b/Defs*.lean`, `SAP/P011b/Defs/*.lean`, `SAP/P011b/Challenge.lean`, and `SAP/P011b/Challenge/Part1.lean`, before opening `claims.json` or `record.json`. Names below are abbreviations for the explicit mathematics specified here, not additional hypotheses. All the Challenge theorems are universally closed over their displayed arguments; T15, T18, T20, T23 and T26 have no arguments or premises.

## Common objects and conventions

Indices of a size-n sample are the integers 0,...,n-1 (`Fin n`). A graph is a symmetric Boolean adjacency function with false diagonal; thus it is a simple undirected labelled graph. Write A also for its real 0/1 adjacency matrix, deg_A(i)=sum_j A_ij, and C(R,d) for the graphs A containing every edge of R and satisfying deg_A(i)<=d_i, where the caps d_i are natural numbers. `Maximizes R d f A` means both A in C(R,d) and, for every B in C(R,d), f(B)<=f(A). `ProgramFeasible` instead writes sum_j A_ij<=d_i and R_ij<=A_ij using real matrix entries; symmetry, zero diagonal and binary entries come from the graph type. `RelaxedFeasible` uses a real variable a_ij for each i<j, requires 0<=a_ij<=1, a_ij=1 on R, and sum of incident a_ij<=d_i.

For a real vector x, let bar(x)=sum_i x_i/n, c(x)_i=x_i-bar(x), S(x)=sum_i c(x)_i^2, s²(x)=S(x)/n, q(M,x)=sum_i sum_j M_ij x_i x_j, and H_A=I+A. The matrix `1` here is the identity, not the matrix of all ones. Set t_i=min(d_i,n-1), with natural-number subtraction. The estimators are

- V1(A,x)=[S(x)+q(A,c(x))]/n²;
- V2(A,x)=s²(x)/n * [1+sum_ij A_ij/n];
- V2'(d,x)=s²(x)/n * [1+sum_i t_i/n];
- VR(A,r)=q(H_A,r)/n² (no centering of r).

The helper versions are V1R=S/[n(n-1)]+q(A,c(x))/n², V2R=S/[n(n-1)]*[1+sum_ij A_ij/n], and V2'R=S/[n(n-1)]*[1+sum_i t_i/n]. All n in real denominators are cast to real numbers. Theorems using these helper discrepancies assume n>1; the other statistical theorems assume positive sizes. Graph-only T24 allows n=0.

A model m consists of a probability measure P on R^n with its usual product Borel sigma algebra, a deterministic real weight vector theta, graphs G and R, and natural caps d. For the coordinate outcome Y, write X_i=theta_i Y_i, B=bar(X), beta=E B, C_ij=E[(X_i-E X_i)(X_j-E X_j)], delta_i=E X_i-beta, v=E[(B-E B)^2], sigma²=meanVariance=sum_i C_ii/n, M=meanSpread=sum_i delta_i²/n, and bG=meanBias=q(H_G,delta)/n. `var m f` is E[(f-E f)^2]. `covOf m f g`, denoted K(f,g) below, is E(fg)-E(f)E(g), whereas Mathlib's `ProbabilityTheory.covariance`, denoted Cov(f,g), is E[(f-E f)(g-E g)]. They agree when the required integrals exist. The expectation is the Bochner integral, which Mathlib sets to zero for nonintegrable functions; integrability is not built into Model. `Integrable` explicitly means almost everywhere strong measurability and finite integral of the norm. `MemLp ... 2` means square integrability (including almost everywhere strong measurability).

Dependency means: for every two finite disjoint vertex subsets S,T with no G edge between them, the entire subvectors (Y_i)_{i in S} and (Y_j)_{j in T} are independent. Mathlib `IndepFun` is independence of their generated sigma algebras, so this is joint independence of these subvectors, not merely pairwise uncorrelatedness. Homoskedastic means C_ii=C_jj for all i,j; positivity is not part of this definition. Define rho_ij=0 if sigma²=0 and C_ij/sigma² otherwise, and V2star=s²(X)/n*[1+sum_ij G_ij rho_ij/n].

A family F has positive integer sizes n_k tending to infinity and one model of that size for each k in N. `Nested` says sizes are nondecreasing and, for every k, there exists an injection of its vertices into those at k+1 preserving both edges and nonedges of G. It does not require the laws to be restrictions of a common law. `Scaling F c1 c2 c3 c4` says Nested, all four real constants strictly positive, Dependency at every k, almost surely |X_ki-beta_k|<=c1 simultaneously for all i at every k, deg_Gk(i)<=c2 for all k,i, n_k v_k -> c3, and |theta_ki|<c4 for all k,i. `Valid F` says G_k in C(R_k,d_k) at every k.

All probability limits below mean k -> infinity along natural numbers. T_k converges in probability to a possibly moving deterministic a_k when, for every real epsilon>0, P_k(|T_k-a_k|>epsilon)->0. A variance estimator W is `Conservative` when, for every epsilon>0, P_k(n_k(v_k-W_k)>epsilon)->0. `Tight F T` means: for every epsilon>0 there exist B>0 and k0 such that, for all k>=k0, P_k(|T_k|>B)<=epsilon. `probability` is the real-valued measure of the indicated event; on arbitrary sets it uses the measure's outer-measure extension. No measurability assumption is placed on graph selectors quantified in T16.

Phi is the CDF of the normal probability measure with mean 0 and variance 1. z_alpha=inf{t:1-alpha/2<=Phi(t)}. `coverage m W alpha` is P(|B-beta|<=z_alpha sqrt(max(W,0))). The only quantification over alpha in the statements assumes 0<alpha<1. `l2` is the Euclidean norm sqrt(sum of coordinate squares).

For a real n by p design D, ols(D,y)=(D^T D)^(-1)D^T y and olsTheta(D) is the p by n matrix n(D^T D)^(-1)D^T. Mathlib's matrix inverse is the inverse on nonsingular matrices and zero otherwise; T16 explicitly excludes singular Gram matrices. `MeanModel m D b` means every Y_i is integrable and E Y_i=(Db)_i. The true residual is theta_i(y_i-(Db)_i); the fitted residual rhat_i(y)=theta_i(y_i-(D ols(D,y))_i).

`Edge n` is the set of pairs i<j; an upper Boolean vector a chooses the edges of its associated graph `fromUpper a`, and `toUpper A` restricts A to i<j. U(a,w)=sum_{i<j:a_ij=true} w_ij. `upperDegree a i` counts selected edges incident to i, and `upperSum f` means sum_{i<j} f(i,j). `nonzeroRule x` chooses exactly the i<j for which c(x)_i c(x)_j !=0.

The named finite laws are genuine pushforwards of uniform probability mass functions on finite nonempty sets; repeated image values receive their summed masses. `signModel n` has independent fair +/-1 coordinates, all weights 1, and G=R empty,d=0. `threePointModel n` instead has independent uniform {0,1,2} coordinates with the same weights and graph constraints. Their families have n_k=k+1. `pathModel(t,K)` consists of K independent blocks (t+U,-2t+3U/5+4V/5,t+V), U,V independent fair signs in each block, weights 1, G=R disjoint three-vertex paths 0--1--2, and caps the path degrees. `blockGraph` places disjoint copies in consecutive coordinate blocks, without between-block edges.

The star law, with K independent four-vertex blocks and weights 1, is as follows. The three leaves L1,L2,L3 are independent Bernoulli variables. For `upper=false`, their probabilities are (1/4,1/4,1/4), and conditional on the leaves the centre C is Bernoulli with probability 33/48+(L1+L2+L3)/12. For `upper=true`, leaf probabilities are (3/4,1/4,1/2) and the centre probability is 18/48+(L1+L2+L3)/12. The definitions implement these using three independent uniform draws in {0,1,2,3} and one in {0,...,47}. G=R is the disjoint union of stars with centre coordinate 0 in each block; caps are (3,1,1,1). `starFamily upper` uses K=k+1 and n_k=4(k+1).

## SAP.P011b.T15

This is an unconditional conjunction about the two explicitly defined star families:

1. The false-star family satisfies Scaling with constants (1,3,27/128,2) and Valid. For every k it is homoskedastic, almost surely binary in every coordinate, E Y_i equals the corresponding block coordinate of (3/4,1/4,1/4,1/4), and its entire covariance matrix is (3/16)I+(1/64)G.
2. For every k its beta=3/8, n_k v_k=27/128, meanBias=-3/128, every graph A is compatible if and only if A=G_k, and E[n_k V1(G_k,Y)]=3[64(k+1)-47]/[1024(k+1)].
3. n_k V1(G_k,Y) converges in probability to 3/16. P(27/128-n_k V1(G_k,Y)>3/256)->1.
4. For every real alpha, if 0<alpha<1, the coverage defined using sqrt(max(V1,0)) converges to 2 Phi(z_alpha sqrt(8/9))-1, and this number is strictly less than 1-alpha.
5. The true-star family satisfies Scaling with (1,3,47/192,2) and Valid; for every k beta=1/2 and n_k v_k=47/192. Its n_k V1(G_k,Y) converges in probability to 53/192.
6. For each Boolean upper, q(H_Gk,Y-mu)/n_k converges in probability to 47/192 if upper=true and 27/128 otherwise, where mu repeats (1/2,3/4,1/4,1/2) in the true case and (3/4,1/4,1/4,1/4) in the false case.
7. For every Boolean upper and every integer K>0, take the two-column design whose first column is 1 and second column repeats (0,1,-1,0) in the true case or (3,-1,-1,-1) in the false case. MeanModel holds with coefficient vector (1/2,1/4) or (3/8,1/8), respectively, and for every deterministic y, ols(D,y)_0=bar(y).
8. For every upper,k and real upper-edge vector a, RelaxedFeasible is equivalent to a being exactly the true star adjacency restricted to i<j. For every upper,k, all coordinates are almost surely binary and, for every graph A, compatibility is equivalent to A=G_k.
9. On a single star, q(I+G,(3/8,-1/8,-1/8,-1/8))=-3/32 and q(I+G,(0,1/4,-1/4,0))=1/8. Also (3/16)/(27/128)=8/9.

There are no external hypotheses on these laws. The theorem does not separately assert a conditional-law formula, the centre's probability range, design Gram identities, or identities saying delta equals either displayed vector.

## SAP.P011b.T16

For every F, every four real constants, and every proof that Scaling F holds with them, for every natural p, every j in Fin p, every sequence of n_k by p designs D_k, and every fixed vector b in R^p: assume for every k det(D_k^T D_k)!=0, MeanModel(F_k,D_k,b), and for every k,i theta_ki=olsTheta(D_k)_ji. Thus p is fixed across k and j exists, so p>0. Then:

1. For every k,i, delta_ki=olsTheta(D_k)_ji (D_k b)_i-b_j.
2. n_k V1(G_k,X_k)-n_k v_k converges in probability to the moving value meanBias(F_k).
3. For every k, every deterministic outcome vector y and every vector c in R^p, rhat_k(y+D_k c)=rhat_k(y), and c(X_k(y+D_k c))=c(X_k(y))+(theta_ki(D_k c)_i-c_j)_i.
4. If there exist real Bx,By,lambda with lambda>0 such that every row of every D_k has Euclidean norm<=Bx, almost surely every |Y_ki|<=By at every k, and for every k and z in R^p, lambda||z||²<=q((D_k^T D_k)/n_k,z), then sqrt(n_k)||ols(D_k,Y)-b|| is Tight, n_k VR(G_k,rhat_k(Y)) converges in probability to n_k v_k, and the following implication holds for every sequence of outcome-dependent graph selectors A_k(y): if Valid F and for every k,y the graph A_k(y) maximizes VR(B,rhat_k(y)) over C(R_k,d_k), then VR(A_k(Y),rhat_k(Y)) is Conservative.

The extra design and outcome bounds are an antecedent only for item 4. Scaling, rank, MeanModel and the weight equalities are antecedents for every item, including the exact finite identities.

## SAP.P011b.T17

For every positive n, every model m, and every i,j,k,l in Fin n (repetitions allowed), write v=(i,j,k,l), X_a=theta_a Y_a, B=bar(X), r_a=X_a-B and Q_ab=E(X_a X_b)-E(X_a B)-E(X_b B)+E(B²). The conclusion is a conjunction of the following five independent implications; there is no dependency-graph or Scaling assumption.

Define WP by integrability of B² and, for each pair (a,b) among (i,j),(k,l), integrability of X_a X_b, X_a B, X_b B. Define WF by integrability, for every subset s of the four *positions* {0,1,2,3}, of (product_{a in s} X_{v_a}) B^(4-|s|). Define CM by integrability of product_{a in s} X_{v_a} for every nonempty position subset s. Define RP like WP with raw Y_a Y_b,Y_a B,Y_b B instead of the weighted products, still including B². Define RF like WF with Y_{v_a} in the product. Since s is a subset of four positions, 4-|s| is never truncated below its intended nonnegative value, including when the vertex indices repeat.

Let

F4=E(X_i X_j X_k X_l)
 -E[B(X_i X_j X_k+X_i X_j X_l+X_i X_k X_l+X_j X_k X_l)]
 +E[B²(X_i X_j+X_i X_k+X_i X_l+X_j X_k+X_j X_l+X_k X_l)]
 -E[B³(X_i+X_j+X_k+X_l)]+E(B⁴).

Let P_ab=theta_a theta_b E(Y_a Y_b)-theta_a E(Y_a B)-theta_b E(Y_b B)+E(B²). Let RF4 be the full sixteen-term raw expansion: sum over every position subset s of (-1)^(4-|s|) (product_{a in s} theta_{v_a}) E[(product_{a in s} Y_{v_a}) B^(4-|s|)]. This describes exactly the separately displayed terms of `rawFourthMoment`.

- WP implies E(r_i r_j)=Q_ij and E(r_k r_l)=Q_kl.
- WP and WF imply K(r_i r_j,r_k r_l)=Cov(r_i r_j,r_k r_l)=E(r_i r_j r_k r_l)-Q_ij Q_kl=F4-Q_ij Q_kl.
- CM implies, for every real constant b,
  K((X_i-b)(X_j-b),(X_k-b)(X_l-b))
  =K(X_i X_j,X_k X_l)
  -b[K(X_i X_j,X_k)+K(X_i X_j,X_l)+K(X_i,X_k X_l)+K(X_j,X_k X_l)]
  +b²[K(X_i,X_k)+K(X_i,X_l)+K(X_j,X_k)+K(X_j,X_l)].
- RP implies Q_ij=P_ij, Q_kl=P_kl, E(r_i r_j)=P_ij and E(r_k r_l)=P_kl.
- RP and RF imply K(r_i r_j,r_k r_l)=Cov(r_i r_j,r_k r_l), E(r_i r_j r_k r_l)=RF4, and K(r_i r_j,r_k r_l)=RF4-P_ij P_kl.

## SAP.P011b.T18

This is unconditional, with the specific law Y=(1,1,1,1) almost surely, theta=(2,3,4,5), and empty G=R,d=0. For the ordered indices 0,1,2,3, it says beta=7/2 and the true K covariance of (2Y0-B)(3Y1-B) and (4Y2-B)(5Y3-B) is zero; this equals Mathlib Cov. The first printed surrogate, E[(2Y0-B)(Y1-B)(4Y2-B)(5Y3-B)]-E[(2Y0-B)(3Y1-B)]E[(4Y2-B)(5Y3-B)], is 9/4. The last printed surrogate is F4-120 times the sixteen-term `printedBracket` at these coordinates and weights, and equals 93009/16. Here the printed bracket's sixteen terms have the coefficient pattern in Defs/Part4: its first coefficient is 1 rather than the four-weight product, its fifth term has coefficient -theta_k theta_l rather than -theta_i theta_k theta_l, and it is multiplied outside by 120. The numerical expression 9/16-(9/16+140-70) equals -70. The correctly weighted F4-P_01 P_23 is zero. The true covariance differs from 9/4, 93009/16 and -70. This is one fixed counterexample, not a universal covariance formula.

## SAP.P011b.T19

For every F and four real constants, assume Scaling, Homoskedastic(F_k) for every k, and meanVariance(F_k)>0 for every k. Then:

1. For every k and every deterministic y, n_k V2star_k(y)-n_k v_k=[1+sum_ij G_ij rho_ij/n_k]*(s²(X_k(y))-sigma_k²).
2. s²(X_k(Y))-sigma_k²-M_k converges in probability to zero.
3. If the deterministic sequence M_k tends to zero, then n_k V2star_k(Y) converges in probability to n_k v_k.

There is no Valid assumption. The third statement's mean-spread hypothesis is not assumed for the first two statements.

## SAP.P011b.T20

An unconditional conjunction for the independent fair-sign family:

1. Scaling holds with (1,1,1,2), and Valid holds.
2. For every integer n>0, signModel(n) is homoskedastic, beta=0, n Var(bar(Y))=1, E[bar(Y)²]=1/n, and for every deterministic vector y of signs, n V2star(y)=1-bar(y)² and |n V2star(y)-n Var(bar(Y))|=bar(y)².
3. For every real epsilon>0 and every integer n>0, 1-1/(n epsilon)<=P(|n V2star-n Var(bar(Y))|<epsilon); for this same arbitrary epsilon, these inside-event probabilities at n=k+1 tend to 1.
4. These inside probabilities at epsilon=1/2 are exactly 1/2 at n=2, 7/8 at n=4, and 32631/32768 at n=16. It is false that they tend to 0 for every epsilon>0.
5. The universal proposition is false which quantifies over all families F and all real c1,c2,c3,c4 and, assuming Scaling, Valid and homoskedasticity at every k, asserts for every epsilon>0 that P_k(|n_k V2star_k-n_k v_k|<epsilon)->0. The event is strict and is the inside event.
6. For every n>0 this model has Dependency; every raw coordinate has expectation zero and weighted variance one; almost surely every |X_i-beta|=1; and on every deterministic sign vector n V2star=s²(X)=1-bar(y)².

## SAP.P011b.T21

For every n>0 and model m, assuming Dependency, Homoskedastic and square integrability of every weighted coordinate X_i, the conjunction says:

- n Var(B)=sigma²[1+sum_ij G_ij rho_ij/n];
- for all i,j, rho_ij<=1;
- for every deterministic y, V2star_m(y)<=V2(G,weighted(m,y)).

The same theorem also includes, without further hypotheses, these facts about pathModel(0,1): it is homoskedastic and has Dependency, every weighted coordinate variance is 1, rho_01=3/5, rho_12=4/5, rho_02=0, and both 3 Var(B) and sigma²[1+sum_ij G_ij rho_ij/3] equal 29/15. Zero common variance is allowed in the universal portion, where rho was defined to be zero.

## SAP.P011b.T22

For every integer n>0:

1. `fromUpper` is a bijection from Boolean functions on pairs i<j to Graph n.
2. For every upper-edge vector a and every real x, q(A,c(x))=2 U(a,(c(x)_i c(x)_j)_{i<j}), where A=fromUpper(a).
3. For every a and vertex i, deg_A(i)=upperDegree(a,i).
4. For every R,d,a, A in C(R,d) if and only if a is true on every R upper edge and every upperDegree(a,i)<=d_i.
5. For every R,d,a,x, A maximizes V1 over C(R,d) if and only if A is compatible and, for every Boolean vector b whose graph is compatible, U(b,c(x)_i c(x)_j)<=U(a,c(x)_i c(x)_j).
6. For every a,x, n² V1(A,x)=n s²(x)+2 U(a,c(x)_i c(x)_j).
7. For every a, sum_ij A_ij=2 U(a,1).
8. The number of possible upper-edge coordinates is n(n-1)/2, using integer arithmetic.

There is no feasibility premise, so the equivalences also apply when the feasible set is empty. Existence of a maximizing graph is not asserted here.

## SAP.P011b.T23

This is unconditional. For x=(-2,1/2,3/2), bar(x)=0 and the three upper centered products are (-1,-3,3/4). The nonzero-product rule selects every edge of the triangle, so every vertex has degree 2; it is incompatible with empty R and caps all 1. The graph `edge23` with sole edge {1,2} is compatible with those constraints, and its upper objective is 3/4. For every graph A, and every proof A is compatible with those constraints, its upper objective is at most 3/4; if equal to 3/4 then A=edge23. For the separate vector (0,1,-1), the mean is zero and the centered product at {0,1} is zero. That edge is present in `edge12` but absent from the rule's graph, so that graph is incompatible with R=edge12 and caps all 2.

## SAP.P011b.T24

For every natural n (including 0), graphs R,G and cap vector d, assume G in C(R,d). Then for every graph A, ProgramFeasible(R,d,A) if and only if A in C(R,d), and ProgramFeasible(R,d,G). The hypothesis is compatibility of the true graph; no probabilistic statement or data object is quantified.

## SAP.P011b.T25

For every integer n>1, graphs R, natural cap vector d and real data vector x, the conjunction states:

1. For every graph A, V1<=V1R and V2<=V2R; also V2'<=V2'R. If S(x)>0, all three comparisons are strict for every A.
2. For every graph A, maximizing V1R over C(R,d) is equivalent to maximizing V1, and maximizing V2R is equivalent to maximizing V2.
3. For every real beta,c, if |x_i-beta|<=c for every i, then for every graph A, 0<=n(V1R-V1)<=4c²/(n-1).
4. For every A the formulas S/n²+q(A,c(x))/n² and S/n²*[1+sum_ij A_ij/n] equal V1 and V2 respectively, and S/n²*[1+sum_i t_i/n]=V2'.
5. For every A, V1R-V1=S/[n²(n-1)]=s²/[n(n-1)], V2R=n/(n-1) V2 and V2'R=n/(n-1) V2'.

No graph feasibility premise, positive empirical variance premise (except in the strict-comparison implication), bounded data premise (except in item 3), or probability-law assumption is imposed globally. There is no explicit limiting-family conclusion.

## SAP.P011b.T26

This unconditional conjunction gives the following examples and a stochastic realization:

- For x=(0,1,2), R=G empty and d=0: compatibility, bar(x)=1, S=2; V1=V2=V2'=2/9 while V1R=V2R=V2'R=1/3; all three inequalities are explicit. The adjacency quadratic, adjacency sum and truncated-cap sum all vanish.
- For x=(0,0,3), R empty, G=edge12 (sole edge {0,1}), d=(1,1,0): compatibility, bar(x)=1, c(x)=(-1,-1,2), S=6; V1=8/9, V2=V2'=10/9, V1R=11/9, V2R=V2'R=5/3; all three discrepancies are nonzero. The adjacency quadratic, adjacency sum and truncated-cap sum are all 2. V1R/V1=11/8 and V2R/V2=V2'R/V2'=3/2.
- For x=(0,1,2), R empty, G complete on three vertices and all caps 2: compatibility, V1=0, V1R=1/9, and q(G,c(x))=-2; the two V1 values differ, and for every real C, C V1<V1R.
- The independent uniform {0,1,2} family satisfies Scaling with (1,1,2/3,2), Valid, and for every k homoskedasticity, beta=1 and n_k v_k=2/3.
- In threePointModel(3), beta=1, 3 Var(B)=2/3, Homoskedastic and Dependency hold, and P(Y=(0,1,2))=1/27.

## SAP.P011b.T27

For every n>0, graphs R,G, natural cap vector d, every proof G in C(R,d), and every real x:

1. C(R,d) is finite and nonempty.
2. For every real function f on Graph n, there exists a graph A maximizing f over C(R,d). For every graph A, if A maximizes f then f(G)<=f(A), and if G also maximizes f then f(G)=f(A).
3. For every graph A, ProgramFeasible is equivalent to compatibility.
4. For every A, maximizing q(A,c(x)) is equivalent to maximizing V1(A,x), and n² V1(A,x)=n s²(x)+q(A,c(x)).
5. For every A, maximizing sum_ij A_ij implies maximizing V2(A,x). If s²(x)>0, every V2 maximizer also maximizes the adjacency sum.
6. Every assertion of T22 above holds at this n, including all its universally quantified designs x and constraints R,d, not only the ones supplied to T27.

The sharpness clause is equality when the supplied feasible G itself maximizes f. It does not assert that an arbitrary compatible G always attains the bound.

## SAP.P011b.T28

For every n>0, graphs R,G,A, natural cap vector d and real x, assume G in C(R,d) and A maximizes V2(B,x) over C(R,d). Then V2(G,x)<=V2(A,x)<=V2'(d,x). If every vertex of this maximizing A has degree min(d_i,n-1), then V2(A,x)=V2'(d,x). No necessity of that degree condition is asserted, and no positivity of s²(x) is required.

## Mathlib definitions followed

The primitive meanings above were checked in these source files under `/home/ubuntu/sal/deps/mathlib/Mathlib/`: `Probability/Moments/Covariance.lean` (covariance), `Probability/Independence/Basic.lean` (IndepFun), `MeasureTheory/Function/L1Space/Integrable.lean` (Integrable), `MeasureTheory/Function/LpSeminorm/Defs.lean` (MemLp), `MeasureTheory/Integral/Bochner/Basic.lean` (integral and integral_undef), `LinearAlgebra/Matrix/NonsingularInverse.lean` (inverse), `Probability/CDF.lean` (cdf), `Probability/Distributions/Gaussian/Real.lean` (gaussianReal, whose second parameter is variance), `Probability/Distributions/Uniform.lean` (uniformOfFintype), and `Probability/ProbabilityMassFunction/{Basic,Constructions}.lean` (toMeasure and map). All sums and products are finite Mathlib Finset sums/products. Filter limits to neighborhoods give the usual real limits; `atTop` on N is the usual limit as the index tends to infinity.
