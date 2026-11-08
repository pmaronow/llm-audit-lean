# Blind reading of the Lean statements

This file was written using only `SAP/P011a/Defs*.lean`, the six Defs parts, the Challenge files, and the Mathlib source definitions. Neither `claims.json` nor `record.json` has been opened. All fourteen Challenge theorems have no arguments: each asserts the conjunction described below, including the universal quantifiers inside that conjunction. A named proposition in Defs is expanded here, not treated as an assumption.

## Common objects, notation, and primitive meanings

Indices are `Fin n`, namely the integers from 0 through n-1. A graph is a symmetric Boolean array with false diagonal, so it is a finite simple undirected labelled graph. Write A also for its real 0/1 adjacency matrix, `deg_A(i)` for its number of neighbours, and H_A=I+A. Matrix `1` means the identity, not the all-ones matrix. Matrix products, transpose, trace, diagonal matrices, and matrix-vector products have their ordinary finite-dimensional meanings.

`Compatible R d A` means R is a subgraph of A and deg_A(i) <= d_i for every i, with natural-number caps d_i. `Maximizes R d f A` means A is compatible and, for every compatible graph B, f(B) <= f(A). Thus existence of a compatible graph is part of being a maximizer. Put t_i=min(d_i,n-1) (natural-number subtraction), and c_i=0 when t_i=0, otherwise c_i=1-1/t_i.

For a real vector x put bar(x)=sum_i x_i/n, z_i=x_i-bar(x), s²(x)=sum_i z_i²/n, q_M(x)=sum_ij M_ij x_i x_j. Define

* V1(A,x)=q_{H_A}(z)/n²;
* V2(A,x)=s²(x)/n * (1+sum_ij A_ij/n);
* V2'(d,x)=s²(x)/n * (1+sum_i t_i/n);
* C(d,A)=H_A+diag(c_i deg_A(i));
* V1+(d,A,x)=V1(A,x)+sum_i c_i deg_A(i) z_i²/n²;
* VY(d,x)=sum_i(1+t_i)z_i²/n²;
* varianceForm(M,x)=q_M(z)/n²;
* VR(A,r)=q_{H_A}(r)/n², without centering r again.

`PSD M` means M is symmetric and q_M(x)>=0 for every real vector x. The norm of a matrix is the operator norm for the Euclidean norm: the definition goes through Mathlib `Matrix.toEuclideanLin`, not the norm on raw function-valued matrices. `l2(x)=sqrt(sum_i x_i²)`, `maxAbs(x)=max_i |x_i|` (zero on an empty index set), and `frobeniusSq(M)=sum_ij M_ij²`. The positive part M+ is U diag(max(lambda_i,0)) U^T for Mathlib's orthonormal eigendecomposition when M is real symmetric; for a nonsymmetric M the definition returns zero. All its substantive uses below have symmetric inputs.

A `Model n` consists of a Borel probability measure P on R^n, deterministic real weights theta_i, a graph G, a required graph R, and natural caps d_i. It does not by itself assert a dependency property, moments, or compatibility. Let X_i=theta_i Y_i, bHat=bar(X), b=E bHat, Sigma_ij=E[(X_i-E X_i)(X_j-E X_j)], delta_i=E X_i-b, B=q_{H_G}(delta)/n, vbar=sum_i Sigma_ii/n, and smean=sum_i delta_i²/n. `expectation` is Mathlib's real Bochner integral, and `var f=E[(f-E f)²]`. The integral is defined as zero for nonintegrable functions; therefore integrability is not implicit in the Model type. `probability(E)` is `(P E).toReal`, including the outer-measure value when E is not measurable. Because Model laws are probability measures its values are finite and in [0,1].

`Dependency` says: for every two finite sets S,T of vertices, if they are disjoint and no G-edge joins S to T, the random vectors (Y_i)_{i in S} and (Y_j)_{j in T} are independent. Mathlib `IndepFun` means independence of their generated sigma-algebras; this is vector independence, not merely pairwise independence. `Homoskedastic` means all diagonal entries of Sigma are equal, referring to X rather than unweighted Y.

A `Family F` has sizes n_k>0 for every natural k, n_k -> infinity, and a Model n_k for every k. `Nested` says n_k is nondecreasing and for each k there exists an injection of the vertices at k into those at k+1 preserving both edges and nonedges of G. It imposes no coupling or marginal consistency of laws across k. `Scaling F c1 c2 c3 c4`, in this order, means Nested F; c1,c2,c3,c4>0; Dependency at every k; for every k, almost surely simultaneously for all i, |X_i-b_k|<=c1; deg_G(i)<=c2 everywhere; n_k Var(bHat_k)->c3; and |theta_i|<c4 everywhere. `Valid F` separately means G_k is compatible with (R_k,d_k) for every k.

Write Q_k=n_k Var(bHat_k) (`scaledTrue`) and O_k(y)=n_k V1(G_k,X(y)) (`scaledOracle`). `InProbability F T a` says, for every real epsilon>0, P_k(|T_k-a_k|>epsilon)->0; a may vary with k. `Conservative F V` says, for every epsilon>0, P_k(n_k(Var(bHat_k)-V_k)>epsilon)->0. `Tight F T` says for every epsilon>0 there exist a real bound L>0 and k0 such that, for every k>=k0, P_k(|T_k|>L)<=epsilon.

Phi is the CDF of Mathlib `gaussianReal 0 1`, the Gaussian of mean zero and variance one. z_alpha=inf{t:1-alpha/2<=Phi(t)}. `coverage` is P(|bHat-b|<=z_alpha sqrt(max(V,0))). `ConservativeCoverage` means for every alpha with 0<alpha<1, 1-alpha<=liminf_k coverage_k. These are real liminfs (`Filter.liminf` is the supremum of eventual lower bounds). For coverage the sequence is bounded. The quantile set is nonempty and bounded below in the alpha range used.

`CliqueUnion A` says the relation i=j or A_ij=true is transitive. It therefore describes a disjoint union of complete graphs, including isolated vertices. `upperSum` sums over i<j exactly once. The centering matrix is P_n=I-J/n, where J is the all-ones matrix. The data-dependent matrix D(x)=xx^T/n. Put U(y)=sum_i(X_i-b)²/n, g=1+sum_ij G_ij/n, e(y)=s²(X(y))-vbar-smean (`varianceRemainder`). Put rho_ij=0 if vbar=0 and Sigma_ij/vbar otherwise; V2*(y)=s²(X(y))/n * (1+sum_ij G_ij rho_ij/n).

All finite variance-estimator identities below explicitly require n>0 unless otherwise noted. Division in R is totalized by 1/0=0; square root is Mathlib `Real.sqrt` (zero on negative inputs). At n>0 these conventions do not change the displayed denominators. Uniform laws below mean pushforwards of the uniform distribution on a finite nonempty type: Mathlib `PMF.uniformOfFintype`, `PMF.map`, and `PMF.toMeasure`. A uniformly selected Boolean array gives mutually independent signs, with sign(true)=1 and sign(false)=-1.

## Explicit model families used below

The four-cycle has edges 01,12,23,30. For K independent blocks and independent signs u_0,...,u_3 in each block, the cycle observations are

    (a+u0+u3, -a+u0+u1, a+u1+u2, -a+u2+u3).

The size is 4K, theta=1, G=R is the block diagonal union of these cycles, and all caps are 2. `cycleFamily a` uses K=k+1. Block and local indices of vertex i are floor(i/q) and i modulo q respectively.

The path has edges 01,12. Its observations, for independent signs U,V, are

    (t+U, -2t+3U/5+4V/5, t+V).

`pathModel t K` uses K independent blocks, theta=1, G=R equal to the path union, and caps equal to the local path degrees (1,2,1). `pathFamily t` uses K=k+1.

`signModel n` has independent signs Y_i, theta=1, G=R empty, caps zero. `signFamily` has n=k+1. `SignWitnessFacts` asserts Scaling with (1,1,1,2), Valid, Q_k=1, and b_k=0 at every k.

In `alternatingModel n`, t_n=n/[2 floor((n+1)/2)], Y_i=2*1_{i even}+u_i for independent signs, theta_i=t_n, G=R empty and caps zero. `alternatingFamily` uses n=k+1. Put p_n=floor((n+1)/2)-floor(n/2) and spread_n=t_n²(1-p_n²/n²).

In `unstableModel K`, n=4K, independent Y_i=u_i for even i and n*u_i for odd i; theta_i=2*(1,0,-1,0) repeated by block; G=R empty and caps zero. `unstableFamily` uses K=k+1.

For real a,b and a fixed infinite Boolean sequence s, `fixedMeanModel a b s n` has independent Y_i=a sign(s_i)+b u_i; its mixture version has Y_i=a v_i+b u_i with two independent sign arrays. Both have theta=1, empty G=R, zero caps. Their families have n=k+1.

## SAP.P011a.T1

This is an unconditional conjunction about the two cycle families and finite matrices:

1. The a=3/2 family satisfies Scaling (7/2,2,4,2) and Valid. At every k it is homoskedastic, its unweighted means repeat (3/2,-3/2,3/2,-3/2), Sigma=2I+G, b=0, Q=4, B=-9/4, and a graph is compatible if and only if it equals G. At every k, E O=7/4-12/n and Var O=44/n-96/n²-288/n³.
2. O converges in probability to 7/4. For every epsilon with 0<epsilon<9/4, both P(|O-4|>epsilon) and P(4-O>epsilon) tend to one.
3. For every real t, P(sqrt(n) bHat<=t)->Phi(t/2). For every alpha in (0,1), oracle V1 coverage tends to 2 Phi(z_alpha sqrt(7/16))-1, and that number is strictly below 1-alpha.
4. The a=3 family satisfies Scaling (5,2,4,2) and Valid, and at every k is homoskedastic with b=0 and Q=4. O converges in probability to -5. In one block, Y=(5,-1,5,-1) has probability 1/16 and its V1 is -9/4.
5. For every real a, the fixed matrix H with rows (1,0,0,1),(1,1,0,0),(0,1,1,0),(0,0,1,1) has HH^T=2I+A_cycle; q_{H_cycle}(a,-a,a,-a)=-4a²; and the sum of entries of 2I+A_cycle is 16. Finally bar(5,-1,5,-1)=2.

## SAP.P011a.T2

For every real t, assuming t=1 or t=2:

1. The path family satisfies Scaling (6,2,29/15,2), Valid, and homoskedasticity at every k. At every k, b=0, Q=29/15, compatibility is equivalent to A=G, and E O=(29-10t²)/15-217/[135(k+1)]. O converges in probability to (29-10t²)/15.
2. If t=1, for every 0<epsilon<2/3, P(|O-29/15|>epsilon) and P(29/15-O>epsilon) tend to one. For every alpha in (0,1), coverage tends to 2 Phi(z_alpha sqrt(19/29))-1, strictly below 1-alpha.
3. If t=2, P(V1(G,X)<0)->1, and for every alpha in (0,1) clipped coverage tends to zero.
4. For every local vertex i the average of the four sign outcomes, and separately its expectation under the one-block model, equals (t,-2t,t)_i. The one-block covariance matrix is [[1,3/5,0],[3/5,1,4/5],[0,4/5,1]]. The mean vector has H_path quadratic form -2t². With S=sum_i Y_i and L=sum_ij(H_path)_ij Y_j, the four-sign averages are E S=0, E S²=29/5, E q_H(Y)=29/5-2t², Var(q_H(Y))=8t²+8836/625, and E(SL)=14. Also q_H(1)=7.
5. For every natural K>0, let the design have columns 1 and the repeated (t,-2t,t) vector. The unweighted coordinates Y_i are integrable and E Y=D(0,1). For every y in R^(3K), the zeroth coordinate of `(D^T D)^(-1)D^T y` is bar(y). The inverse is Mathlib's nonsingular matrix inverse, which returns zero at a singular real matrix; these displayed designs are nonsingular for t=1,2 and K>0.

## SAP.P011a.T3

For every Family F, then every four real constants c1,c2,c3,c4, assuming Scaling:

1. O-(Q+B) converges in probability to zero.
2. For every k, |E O_k-Q_k-B_k|<=3(1+c2)² c1²/n_k.
3. s²(X)-vbar-smean converges in probability to zero.
4. O-Q converges in probability to zero if and only if B_k->0. The oracle V1 is Conservative if and only if liminf B_k>=0. If delta_i=0 for every k,i, O-Q converges in probability to zero. If H_G is PSD for every k, oracle V1 is Conservative.

Independently, for every natural n>0 and graph A, H_A is PSD if and only if A is a clique union. For every labelling C:Fin n->N with A_ij=true iff i!=j and C_i=C_j, and then every real vector x,

    V1(A,x)=sum_{c in image C} (sum_{i:C_i=c} z_i)²/n².

## SAP.P011a.T4

For every F, real c1,c2,c3,c4,K, assuming Scaling, then a deterministic sequence of real matrices M_k, assuming each M_k is symmetric and its Euclidean operator norm <=K:

1. There exist a real L>=0 and k0 such that for all k>=k0, Var(q_{M_k}(centered X))<=L n_k.
2. n_k varianceForm(M_k,X)-Q_k converges in probability to [tr((M_k-H_G)Sigma_k)+q_{M_k}(delta_k)]/n_k (a potentially varying deterministic target).
3. If both M_k and M_k-H_G are PSD at every k, then at every k the two terms q_M(delta) and tr((M-H_G)Sigma) are separately nonnegative, and varianceForm(M_k,X) is Conservative.

Separately, for every F,c1,c2,c3,c4 satisfying Scaling, then every k and real symmetric M of size n_k,

    E q_M(centered X)=tr(P_n M P_n Sigma)+q_M(delta)
      =tr(M Sigma)+q_M(delta)-2 sum_ij(M Sigma)_ij/n
         +q_M(1) Var(bHat).

Independently, for every n>0 and vector x with each x_i in {1,-1}, D(x)=xx^T/n has norm one and trace one, and n varianceForm(D(x),x)=(1-bar(x)²)². Under signFamily, n varianceForm(D(Y),Y)-1 converges in probability to zero, whereas tr(D(Y)-I)/n converges in probability to -1. This theorem also includes the full clique characterization and formula of T3 and the SignWitnessFacts given above.

## SAP.P011a.T5

For every n>0, then R,A,d, assuming compatibility, then every real vector x:

1. deg_A(i)<=t_i for every i, and C(d,A)=diag(deg_A)+A+diag(1-h_i), where h_i=0 if t_i=0 and deg_A(i)/t_i otherwise. For every z, q_{diag(deg_A)+A}(z)=sum_{i<j} A_ij(z_i+z_j)².
2. C(d,A), C(d,A)-H_A, I+diag(t), diag(t)-A, diag(t)-diag(deg_A), and diag(deg_A)-A are all PSD. V1+ is nonnegative and equals varianceForm(C(d,A),x). Also (I+diag(t))-H_A=(diag(t)-diag(deg_A))+(diag(deg_A)-A), and for every z the second term's quadratic form is sum_{i<j}A_ij(z_i-z_j)².
3. V1(A,x)<=VY(d,x). Let E+(B)=sum_{i<j}[z_i z_j+(c_i z_i²+c_j z_j²)/2]B_ij. Then n² V1+(d,A,x)=sum_i z_i²+2E+(A).
4. For every natural D, if all t_i=D then VY=V2'=s²(x)(1+D)/n. For every natural d0,D with D>=1, deg_A=d0 everywhere and t=D everywhere imply V1+=V1+d0(1-1/D)sum_i z_i²/n². If d0>=1 and both degrees and caps equal d0, the correction is (d0-1)sum_i z_i²/n². If all graph degrees vanish, V1+=V1.

For every F,c1,c2,c3,c4 satisfying Scaling, then Valid, then every graph-valued selection A_k(y) which maximizes the corrected objective for every k,y: the norm of C(d,G) is <=1+2c2 at every k, its V1+ is pointwise <= the selected maximum, and each of V1+(d,G,X), V1+(d,A_k(y),X), VY(d,X), and their selected-maximum/Young minimum is Conservative. If for every k there exists a natural D common to all its t_i, V2'(d,X) is also Conservative. No measurability assumption is separately imposed on the graph selection.

Finally, for every n>0,R,A,d,x, if A maximizes V1+ then for every compatible B, E+(B)<=E+(A), and the same identity n²V1+=sum_i z_i²+2E+(A) holds.

## SAP.P011a.T6

For every n>0 and graph A: (H_A)+ and (H_A)+-H_A are PSD; ||(H_A)+||<=1+max_i deg_A(i); for every x, max(V1(A,x),0)<=VPositive(A,x), where VPositive=varianceForm((H_A)+,x); and for every PSD M, ||(H_A)+-H_A||_F²<=||M-H_A||_F².

For every F,c1,c2,c3,c4 satisfying Scaling, VPositive(G,X) is Conservative. For every natural n (including zero), graph A and PSD M, equality of the preceding two distances implies M=(H_A)+.

For the four-cycle let E have rows (17/20,-1/4,1/4,-17/20),(-1/4,3/20,-3/20,1/4),(1/4,-3/20,3/20,-1/4),(-17/20,1/4,-1/4,17/20). Both E and H_cycle+E are PSD, but their comparison at x=(0,1,-1,0) gives q_{H+E}(x)=3/5 and q_{H+}(x)=1. At every k of cycleFamily(3/2), E[n VPositive]=4-12/n and Q_k=4; n VPositive converges in probability to 4.

There do not exist a real c and real weights w_ij on three vertices such that for every Graph 3, VPositive(A,(1,-2,1))=c+sum_{i<j}w_ij A_ij.

The matrix U with rows (1,1,1,1)/2,(1,1,-1,-1)/2,(1,-1,-1,1)/2,(1,-1,1,-1)/2 satisfies U^T U=I and H_cycle=U diag(3,1,1,-1)U^T. Its clipped matrix U diag(3,1,1,0)U^T has quadratic form q_H(x)+(x0-x1+x2-x3)²/4. For every x in R^4 this is also the quadratic form of (H_cycle)+, and equals 3(sum_i x_i)²/4+[(x0-x2)²+(x1-x3)²]/2.

For every natural n and real symmetric matrix M, if U,lambda are Mathlib's chosen orthonormal spectral data, M+-M=U diag(max(lambda_i,0)-lambda_i)U^T.

## SAP.P011a.T7

For every n>0,A,x, q_A(z)=sum_i deg_A(i) z_i²-sum_{i<j}A_ij(z_i-z_j)².

For every n>0, then d and natural D, assuming t_i<=D everywhere, then every vector x: every V1-maximizer A with empty R satisfies

    0<=n(VY-V1(A,x))<=sum_{r=1}^D(3r²+2r) maxAbs(z)²/n.

Every V1+-maximizer Ap with empty R satisfies

    0<=sum_i max(1,2t_i)z_i²/n-n V1+(d,Ap,x)
      <=maxAbs(z)²/n * sum_{r=1}^D(4r²+r).

For every F,c1,c2,c3,c4 satisfying Scaling, then Valid, then empty R at every k, then every selection A_k(y) maximizing V1 at every k,y, the selected estimator is Conservative. There is no uniform bound on supplied d_i in this clause.

For every selection A_k(y) maximizing V1 over empty-R graphs on n=k+1 with caps d_i=k, for every k,y whose coordinates are signs,

    V1(A_k(y),y)=(1-bar(y)²)²/2,
    VY((k,...,k),y)=1-bar(y)².

Under signFamily the unscaled selected V1 converges in probability to 1/2 and the unscaled Young statistic to 1. This theorem also includes SignWitnessFacts. The supplied caps in this example belong to the optimization, whereas signFamily's stored caps are zero.

## SAP.P011a.T8

For every F,c1,c2,c3,c4 satisfying Scaling, then every estimator V in the following exact union of classes, both Conservative F V and ConservativeCoverage F V hold:

1. Valid F and V is corrected oracle V1+, Young VY, a pointwise maximum of V1+ over compatible graphs, or the minimum of that corrected maximum and Young;
2. V is the spectral positive-part oracle;
3. Valid F, R empty everywhere, and V is a pointwise maximum of the original V1;
4. Valid F, liminf B_k>=0, and V is original oracle V1 or a pointwise compatible maximum of original V1.

Every maximization above is for every k and every y. Independently, for every F and constants satisfying Scaling and Valid, if either all weighted means equal b at every k,i or every G_k is a clique union, both variance conservativeness and ConservativeCoverage hold for oracle V1. Then for every graph selection maximizing original V1 at every k,y both properties also hold for its maximum. The theorem includes the entire cycle and path counterexample propositions described in T1 items 1-4 and T2 items 1-3.

## SAP.P011a.T9

For designs D_k with fixed natural column count p and a fixed real coefficient vector gamma, `MeanModel` requires every unweighted Y_i integrable and E Y_i=(D_k gamma)_i. True residual z_i=theta_i(Y_i-(D gamma)_i); fitted residual r_i=theta_i(Y_i-(D gammaHat(Y))_i). Set Delta=r-z. A coefficient map is required measurable for every k in each of the three asymptotic assertions below.

1. For every F,c1,c2,c3,c4 satisfying Scaling, then p,D,gamma,gammaHat, assuming measurable gammaHat, MeanModel at every k, a real uniform upper bound on the Euclidean row norms of D, and tightness of sqrt(n)||gammaHat-gamma||_2; then every graph selection A, assuming Valid F and pointwise maximization of VR(B,r) by A: E z_i=0 and E z_i z_j=Sigma_ij at every k,i,j; sqrt(n)maxAbs(Delta), ||Delta||_2, and ||z||_2/sqrt(n) are tight; n VR(G,r)-Q converges in probability to zero; and VR(A,r) is Conservative.
2. For every F,constants satisfying Scaling, then p,D,gamma,gammaHat, assuming measurability, MeanModel, existence of a real uniform almost-sure bound on all |z_i|, and ||Delta||_2/sqrt(n)->0 in probability; then every A with Valid F and the same pointwise maximization: n VR(G,r)-Q->0 in probability and VR(A,r) is Conservative. No design-row or coefficient rate assumption occurs in this clause.
3. For every F,constants satisfying Scaling, then p,D,gammaStar,gammaHat, assuming measurability, uniform almost-sure boundedness of z defined with gammaStar, and ||r-z||_2/sqrt(n)->0 in probability (without MeanModel),

       n VR(G,r)-Q - q_{H_G}(mu)/n ->0 in probability,
       mu_i=E X_i-theta_i(D gammaStar)_i.

4. The unstableFamily satisfies Scaling (2,1,2,3). For every k let n=4(k+1) and D have columns 1 and repeated (1,0,-1,0). MeanModel holds with coefficient zero. The OLS intercept variance is n/2+1/(2n). The expectation of n VR(G,fitted residual using OLS) is n+2-7/n. That statistic does not converge in probability to the constant 2.
5. Independently, for every natural n (including zero), real symmetric M, and r,z, |q_M(r)-q_M(z)|<=||M|| ||r-z||_2(2||z||_2+||r-z||_2).

## SAP.P011a.T10

For every real a,b with a>0 and b>0:

1. For every infinite Boolean sequence s, fixedMeanFamily(a,b,s) satisfies Scaling (2a+b,1,b²,2); mixtureFamily(a,b) satisfies Scaling (a+b,1,a²+b²,2).
2. For every natural n (including zero), the mixture law equals the sum over all s in Bool^n of 2^(-n) times the fixedMeanModel law using the extension of s by false outside the first n indices. This is an equality of measures with ENNReal scalar multiplication.
3. There is no sequence of statistics T_k:R^(k+1)->R, measurable at each k, which converges in probability to b² under every one of the infinite fixed-mean families and to a²+b² under the mixture family.
4. For every sequence T_k measurable at each k, if for every epsilon>0 the mixture probability P(a²+b²-T_k>epsilon)->0, then it is false that T_k->b² in probability for every fixed infinite s.

Separately, for every real a,b, infinite Boolean s, and natural n>0: each fixed-mean E Y_i=a sign(s_i), each diagonal covariance is b², beta=bar(a sign(s_i)), and n Var(bHat)=b². Each mixture E Y_i=0, each diagonal covariance is a²+b², beta=0, and n Var(bHat)=a²+b². These finite identities do not require a,b positive.

## SAP.P011a.T11

The alternatingFamily satisfies Scaling (2,1,1,2), Valid, and at every k is homoskedastic, with beta=1 and Q=t_n². For its empty graph, n V2-Q converges in probability to 1; P(|n V2-Q|>1/2)->1 and P(|n V2-Q|<3/2)->1. V2 is nevertheless Conservative.

For every k, putting n=k+1,t=t_n,m=alternatingModel(n): 1/2<=t<=1; beta=1; Sigma_ii=t² and delta_i=t*(2 if i even else 0)-1 for every i; smean=spread_n. For every sign array u,

    s²(X)=t²+smean+2t sum_i delta_i sign(u_i)/n
            -t²(sum_i sign(u_i))²/n².

E e=-t²/n and E e²=4t² smean/n+t^4(3/n²-2/n³). If n is even, t=1, smean=1, and E[(n V2-2)²]=4/n+3/n²-2/n³; each of P(|n V2-1|>1/2) and P(|n V2-1|<3/2) is at least 1-4(4/n+3/n²-2/n³).

For every k and every y, V2*=V2, n V2=s²(X), and n V2*-Q=smean+e(y).

## SAP.P011a.T12

For every F,c1,c2,c3,c4 satisfying Scaling, assuming homoskedasticity at every k, for every k (write n=n_k):

1. For every y, s²(X)=U(y)-(bHat(y)-b)². E U=vbar+smean; Var U<=(1+c2)c1^4/n; E(bHat-b)²<=(1+c2)c1²/n; E(bHat-b)^4<=(1+c2)c1^4/n; E e²<=4(1+c2)c1^4/n.
2. Q<=vbar*g, 1<=g<=1+c2. For every y, n V2=g*s²(X) and Q-n V2<=(1+c2)|e(y)|. For every epsilon>0,

       P(Q-n V2>epsilon)<=4(1+c2)^3 c1^4/(n epsilon²).

3. V2 is Conservative.
4. For every i, vbar=Sigma_ii; smean>=0; Q=sum_ij Sigma_ij/n. For every y the full gap chain is

       Q-n V2 <= g(vbar-s²(X))
               = -g(smean+e(y)) <= (1+c2)|e(y)|.

No validity or supplied-degree hypothesis is present in T12.

## SAP.P011a.T13

An edge is an unordered pair represented uniquely as (i,j) with i<j. A degree problem P has a forced edge set F, natural caps d_i, and rational edge weights w_e. A set S is feasible iff F is a subset of S and its incident-edge count at each i is <=d_i. Its objective is sum_{e in S}w_e. Optional edges O are all edges outside F; r_i=min(d_i,n-1)-deg_F(i), a truncated natural subtraction. L is the lcm of denominators of optional rational weights, W_e=L*num(w_e)/den(w_e) using integer division, and M=1+max_{e in O}|W_e| (empty maximum zero).

The gadget has r_i slot vertices for each i and two vertices (e,false),(e,true) for each optional edge. There is one central edge joining those two vertices with weight 4M; for each side and each slot at its endpoint, an edge from that side vertex to the slot, with weight 2M+W_e. A matching is a finite edge set with no endpoints shared by distinct edges. Decode(J) consists of optional e for which J contains a slot edge at both sides.

For every natural n>0, then every degree problem P:

1. A feasible S exists iff deg_F(i)<=min(d_i,n-1) for every i.
2. If that degree condition holds, then for every S, feasibility is equivalent to existence of T subset O with deg_T(i)<=r_i everywhere and S=F union T.
3. Under the same condition, for every finite gadget edge set J, if it is a matching and its weight is >= the weight of every matching J', then F union Decode(J) is feasible, has objective >= every feasible S, and its objective is

       objective(F)+[weight(J)-4M*|O|]/(2L).

4. Without the degree condition, the combinatorial bounds still assert 2|O|+sum_i r_i<=2n(n-1) and |O|+sum_{e=(i,j) in O}(r_i+r_j)<=|O|(2n-1), with natural subtraction in the right sides.

For every natural n (including zero) and P, the gadget vertex and edge cardinalities are exactly 2|O|+sum_i r_i and |O|+sum_{e=(i,j) in O}(r_i+r_j).

Two concrete four-vertex problems both have w_ij=x_i x_j for x=(3/2,1/2,-1/2,-3/2). For `second=false`, F={02,23}, caps=(2,1,2,7), r=(1,1,0,2), |O|=4, and the displayed feasible maximizing solution is F union {01}, with objective 3/4. For `second=true`, F={02}, all caps one, r=(0,1,0,1), |O|=5, and the displayed feasible maximizing solution is F, with objective -3/4. In both cases L=4 and M=10. For each Boolean second there exists an actual gadget matching attaining the maximum, with weight 166 for false and 200 for true. The general reduction is conditional on a supplied maximum matching and does not itself quantify existence of one.

## SAP.P011a.T14

A fractional edge vector a is `RelaxedFeasible R d` iff 0<=a_e<=1 on every edge, a_e=1 on each R-edge, and sum of its incident edge values at every i is <=d_i. Its objective is sum_e w_e a_e. A Boolean edge vector defines the ordinary symmetric graph `fromUpper`; its objective is the same sum over selected edges.

For every n>0, then R,d,w:Edge n->R,U in R, assuming U bounds the objective of every fractionally feasible vector:

1. Every compatible Boolean vector has objective <=U.
2. For every x then Boolean a, if its graph is compatible and w_(i,j)=z_i z_j on every edge, V1(fromUpper(a),x)<=[n*s²(x)+2U]/n².
3. If every w_e=1, then for every x,a with compatible graph, V2(fromUpper(a),x)<=s²(x)/n*(1+2U/n).

For n=6, x=(1,1,1,-1,-1,-1), empty R and all caps one, put w_ij=x_i x_j and f_ij=1/2 within each equal-sign triple, zero across them. f is fractionally feasible, objective 3, and all fractional objectives are <=3. There exists a compatible integer graph of objective 2 and V1=5/18; every integer objective is <=2. The fractional variance bound is (6+2*3)/6²=1/3. Additionally bar(x)=0, s²(x)=1, the full symmetric objective values are twice the edge objectives (6 fractional, 4 integer), and the very same integer claims hold for the named edge set {01,34}.

For n=3, empty R, caps one, and unit weights, a_e=1/2 is fractionally feasible with objective 3/2; every fractional objective is <=3/2. There exists a compatible graph with sum_ij A_ij=2, and every such sum is <=2. Equivalently, the fractional full symmetric objective is 3. Finally, in the six-vertex problem there exist a feasible fractional vector a0 and a feasible integer vector a whose objectives satisfy objective(a0)<objective(a). This last assertion concerns a possibly suboptimal fractional feasible point, not the fractional maximum.

## Mathlib source trail

The nontrivial primitive meanings above were checked at: `Probability/Independence/Basic.lean` (IndepFun and generated sigma-algebras); `MeasureTheory/Integral/Bochner/Basic.lean` (totalized integral); `MeasureTheory/Function/L1Space/Integrable.lean` (almost-everywhere strong measurability and finite absolute integral); `Probability/Distributions/Uniform.lean`, `Probability/ProbabilityMassFunction/Constructions.lean`, and `Probability/ProbabilityMassFunction/Basic.lean` (uniform pushforward laws); `Probability/CDF.lean` and `Probability/Distributions/Gaussian/Real.lean` (CDF and Gaussian variance parameter); `Order/LiminfLimsup.lean` (eventual lower-bound supremum); `Analysis/InnerProductSpace/PiL2.lean` (Euclidean matrix map); `Analysis/Matrix/Spectrum.lean` and `LinearAlgebra/Matrix/Hermitian.lean` (real spectral decomposition); `LinearAlgebra/Matrix/NonsingularInverse.lean` (matrix inverse); and `LinearAlgebra/Matrix/Trace.lean` (diagonal sum). All are under the permitted Mathlib source tree. No solution or comparator was used.
