# Blind reading (saved before opening claims.json or record.json)

I read all five Challenge docstrings and statements, every source declaration named in their closures, and the types of all 99 distinct generated proof declarations (compiled `scratch/ClosureChecks.lean`; output in `scratch/closure-checks.log`). Generated declarations supply arithmetic facts, graph validity, probability instances, index bounds, or standard Mathlib typeclass instances; they do not add statistical assumptions. Some are named after unrelated propositions because Lean reused auxiliary proofs. Constructors/projections have the meanings of the structures below.

## Common notation, fully expanded

Indices are `Fin n` (integers from 0 through n-1). A graph is a Boolean n-by-n array with symmetric entries and false diagonal. Write A_ij=1 or 0 for its real adjacency matrix, d_A(i)=sum_j A_ij, and S_A=I+A. All matrices below are real finite square matrices. Write q_M(x)=sum_i sum_j M_ij x_i x_j. A matrix is PSD when it is symmetric and q_M(x)>=0 for every real vector x. Its operator norm is the norm of the associated continuous linear map on Euclidean space; its squared Frobenius norm is sum_ij M_ij^2. Write bar(x)=sum_i x_i/n, Hx=x-bar(x)1, and sv(x)=sum_i(Hx)_i^2/n.

A model consists of a probability measure P on R^n, deterministic real weights theta_i, a true graph G, a recruitment graph R, and supplied natural-number degree caps d_i. X_i=theta_i Y_i. All expectations mean Mathlib's real Bochner integral against P. betaHat=bar(X), beta=E betaHat, Var(f)=E[(f-E f)^2], and C_ij=E[(X_i-E X_i)(X_j-E X_j)]. Put delta_i=E X_i-beta and b=q_(I+G)(delta)/n. Homoskedastic means all C_ii equal.

G is a dependency graph precisely when, for any two disjoint finite subsets U,V with no G edges between them, the random vectors of raw coordinates (Y_i)_(i in U) and (Y_j)_(j in V) are independent (Mathlib `IndepFun`). This is joint independence across separated sets, not just zero covariance or pairwise independence. Deterministic weights preserve it.

A family has positive natural sizes n_k tending to infinity and one model per k. The row scaling assumptions W(c1,c2,c3,c4) say all four constants are positive; every row has this dependency graph; almost surely every |X_i-beta_k|<=c1; every true degree is <=c2; n_k Var(betaHat_k) tends to c3; and every |theta_i|<c4. They impose no cross-row law coupling or graph embedding. `WholeScaling` and `RowScaling` both mean exactly W. The older `Scaling` additionally requires n_k monotone and an induced embedding of each true G_k into G_(k+1). It occurs only in explicit witness assertions here.

Compatibility of B with (R,d) means every R edge is a B edge and d_B(i)<=d_i. Validity means the true G is compatible in every row. `Maximizes R d f B` means B is compatible and f(B')<=f(B) for every compatible B'. A random maximizer is a function of the row data satisfying this for every data vector, not just almost surely.

Set t_i=min(d_i,n-1) in natural numbers and a_i=0 if t_i=0, otherwise 1-1/t_i. The estimators used in the statements are

- V1(B,x)=q_(I+B)(Hx)/n^2.
- Vplus(d,B,x)=V1(B,x)+sum_i a_i d_B(i)(Hx)_i^2/n^2.
- VYoung(d,x)=sum_i(1+t_i)(Hx)_i^2/n^2.
- Mplus: for symmetric M choose a Mathlib orthonormal eigenbasis U and replace each eigenvalue lambda by max(lambda,0), obtaining U diag(max(lambda,0)) U^T; for nonsymmetric M the definition returns the zero matrix.
- Vpos(B,x)=q_(S_B plus)(Hx)/n^2.

All sums over i<j mean exactly one copy per unordered edge. maxAbs(x) is the maximum of |x_i| as a nonnegative real, using the finite supremum with empty value zero. ||x||_2=sqrt(sum_i x_i^2).

Convergence in probability of T_k to deterministic a_k means: for every real epsilon>0, P_k(|T_k-a_k|>epsilon) tends to zero. Conservativeness of a variance estimator V means: for every epsilon>0, P_k(n_k(Var(betaHat_k)-V_k)>epsilon) tends to zero. These are statements about probabilities in each row, without a common probability space.

Phi is the CDF of Mathlib's real Gaussian with mean zero and variance one. z_alpha=inf{t:1-alpha/2<=Phi(t)}. Coverage is P(|betaHat-beta|<=z_alpha sqrt(max(V,0))). Conservative coverage means that, for every 0<alpha<1, the liminf of these probabilities is at least 1-alpha. Tightness T=O_p(1) means for each epsilon>0 there exist B>0 and k0 with P_k(|T_k|>B)<=epsilon for every k>=k0.

Uniform finite laws mean pushforward of the uniform probability mass function on a specified nonempty finite type. A uniform Boolean vector gives mutually independent fair signs e_i in {-1,1}, with sign(true)=1 and sign(false)=-1. A product Boolean-vector type gives independence of all its coordinates, including across factors. Block index is integer quotient i/q and local index i modulo q, with q>0; the block graph has the supplied small graph within each block and no edges across blocks.

## SAP.P011a.T6

The theorem has no external hypotheses: its type is the following conjunction of universal assertions and explicit examples.

1. For every natural n>0 and graph A on n vertices, S_A plus and S_A plus-S_A are PSD; ||S_A plus||op<=1+max_i d_A(i); for every x, max(V1(A,x),0)<=Vpos(A,x); and for every PSD M, ||S_A plus-S_A||F^2<=||M-S_A||F^2.
2. For every family F, then every four real constants c1,c2,c3,c4, if W holds, Vpos(G_k,X_k) is conservative as defined above.
3. For every n (including zero), graph A, PSD M, equality of the two squared distances in item 1 implies M=S_A plus. This states uniqueness of the nearest PSD matrix, with PSD M and equality as premises.
4. Let A be the four-cycle 0-1-2-3-0 and let
   D=[[17/20,-1/4,1/4,-17/20],[-1/4,3/20,-3/20,1/4],[1/4,-3/20,3/20,-1/4],[-17/20,1/4,-1/4,17/20]].
   S_A+D and D are PSD. For v=(0,1,-1,0), q_(S_A+D)(v)=3/5, whereas q_(S_A plus)(v)=1. Thus this particular PSD majorant is not above the clipped matrix in Loewner order.
5. There do not exist c in R and real w_ij on three vertices such that, for every graph A on those vertices, Vpos(A,(1,-2,1))=c+sum_(i<j) w_ij A_ij. This fixed-data assertion rules out an affine graph objective.
6. Let U have rows (1,1,1,1)/2, (1,1,-1,-1)/2, (1,-1,-1,1)/2, (1,-1,1,-1)/2. Then U^T U=I and S_cycle=U diag(3,1,1,-1) U^T. With K=U diag(3,1,1,0) U^T, every x satisfies q_K(x)=q_S(x)+(x0-x1+x2-x3)^2/4. Also, for every x, q_(S plus)(x) equals both this same expression and 3(x0+x1+x2+x3)^2/4+((x0-x2)^2+(x1-x3)^2)/2.
7. The cycle family with n=4(k+1) uses independent fair signs u0,u1,u2,u3 in every independent block, outcomes (a+u0+u3,-a+u0+u1,a+u1+u2,-a+u2+u3), weights one, G=R=disjoint cycles, and caps two. For a=3/2 every row has n Var(betaHat)=4, E[n Vpos(G,X)]=4-12/n, and n Vpos(G,X) converges in probability to 4.
8. For every n, symmetric real M, and its chosen orthogonal eigenbasis U with eigenvalues lambda_i, Mplus-M=U diag(max(lambda_i,0)-lambda_i) U^T.

Docstring reading: a corrected spectral estimator, including its finite optimality, asymptotic guarantee, limitations in matrix order and optimization, and a cycle calculation.

Junk-value audit: finite estimator assertions require n>0; all family sizes are positive. Uniqueness and the spectral identity allow n=0, where the unique empty matrix and empty sums make the assertions legitimate. Degree maxima use finite sup with empty value zero, but the norm-bound branch has n>0. Real division is totalized with 1/0=0, but no displayed estimator or cycle denominator in its asserted use is zero. The nonsymmetric-zero branch of Mplus is never used: S_A is symmetric and the last identity assumes Hermitian M (equivalent to symmetric here). Eigenvector choices can be noncanonical but the spectral function is basis-independent. Bochner integrals default to zero when nonintegrable; W bounds weighted centered observations, guaranteeing all weighted moments appearing here, and the cycle laws have finite support. Probability uses ENNReal.toReal; total mass one excludes infinity. No logarithm, rpow, infimum, liminf, partial-function default, or dangerous cast appears in this theorem. Quotient/remainder block indexing is guarded by q=4>0 and explicit index proofs.

## SAP.P011a.T7

The theorem is a conjunction with the following quantifier order and content.

1. For every n>0, graph A, then real x, with z=Hx,
   q_A(z)=sum_i d_A(i) z_i^2-sum_(i<j) A_ij(z_i-z_j)^2.
2. For every n>0, natural caps d_i, natural D satisfying every t_i<=D, and real data x, every V1 maximizer A under empty recruitment has
   0<=n(VYoung(d,x)-V1(A,x))<=maxAbs(Hx)^2/n * sum_(r=1..D)(3r^2+2r).
   Every Vplus maximizer Ap under those same constraints has
   0<=sum_i max(1,2t_i)(Hx)_i^2/n-n Vplus(d,Ap,x)
   <=maxAbs(Hx)^2/n * sum_(r=1..D)(4r^2+r).
   These are separate universal conditionals, not an assumption that one A maximizes both objectives.
3. For every F and c1,c2,c3,c4 with W, valid true graph, and R_k empty for every k, then every function A_k(y) maximizing the compatible V1 objective for every k,y, V1(A_k(y),X_k) is conservative and has conservative clipped Wald coverage. Also for every k, almost surely maxAbs(HX_k)<=2c1. There is no uniform cap bound on the supplied d_i in this branch.
4. The sign family has n=k+1, independent fair signs Y_i, theta_i=1, true and recruitment graphs empty, and caps zero. It satisfies the stronger nested Scaling with constants (1,1,1,2), is valid, and has beta=0 and n Var(betaHat)=1 in every row.
5. For every choice of V1-maximizing graph functions A_k(y) under empty recruitment and caps k=n-1, every sign-valued vector y has exactly V1(A_k(y),y)=(1-bar(y)^2)^2/2 and VYoung(k,y)=1-bar(y)^2. Under the sign family these converge in probability, without multiplying by n, to 1/2 and 1 respectively. The witness law's stored caps zero do not enter these two externally specified full-cap objectives.
6. For every n>0, sign-valued vector y with bar(y) different from both 1 and -1, then every V1-maximizing A with empty recruitment and caps n-1, A_ij=true if and only if i!=j and (Hy)_i(Hy)_j>0. Thus the optimizer is uniquely the union of the two residual-sign cliques on nonconstant sign samples.

Docstring reading: all finite degree formulas, coverage and conservativeness with possibly growing supplied caps, and an explicit large-gap sign example.

Junk-value audit: n>0 guards all finite averages and estimator denominators. n_k>0 and n_k->infinity guard all asymptotics. Natural t_i=min(d_i,n-1) really uses truncated n-1, but n>0 everywhere it matters; caps in the gap example are k=(k+1)-1. For t_i=0 the degree correction is explicitly zero and does not use the erroneous value 1-1/0=1. D=0 gives an empty Icc(1,D) sum equal to zero, with feasible graphs then empty; this is meaningful. maxAbs of an empty vector is zero, but the relevant branches are nonempty. Gaussian quantiles use sInf in R, whose empty/unbounded fallback is zero; 0<alpha<1 ensures its set is nonempty and bounded below. sqrt is applied only to max(V,0). Coverage liminf is taken on probabilities in [0,1], so no unbounded-set convention intervenes. Integrals of weighted quantities are integrable by W; signs have finite support. Graph selector functions need not be explicitly measurable, but their objective value equals the finite maximum of continuous functions and hence has a measurable value. No log, rpow or default block index occurs here. Probability-toReal is finite because all laws are probabilities.

## SAP.P011a.T8

First quantify F, then c1,c2,c3,c4 and W, then an arbitrary real estimator function V_k(y). If V is in the following union of four classes, conclude both conservativeness and conservative clipped Wald coverage:

1. Under valid constraints, V is exactly one of Vplus(d,G,X), VYoung(d,X), a samplewise compatible Vplus maximum, or the minimum of that maximum and VYoung. The two maximum alternatives existentially quantify a graph selector satisfying the maximization property for all rows and all data.
2. V is exactly Vpos(G,X), with no validity requirement for R,d in this alternative.
3. Under valid constraints and R empty in every row, V is a compatible V1 maximum, with an existential graph selector as above.
4. Under valid constraints and 0<=liminf_k b_k, V is either the original oracle V1(G,X) or a compatible V1 maximum.

The theorem separately universally quantifies another F and constants with W. If either every E X_i equals that row's beta, or every G is a disjoint union of cliques, then 0<=liminf b_k. The clique condition is the transitivity of the reflexive relation i=j or G_ij=true; together with graph symmetry it says exactly a union of complete components, including isolated vertices.

It also states a finite assertion: for every n>0, R,G,d with G compatible, every data x, and every compatible Vplus maximizer A, all of Vplus(d,G,x), Vplus(d,A,x), VYoung(d,x), their stated minimum, and Vpos(G,x) are nonnegative.

Finally it includes two full counterexample propositions (assertions about specific laws, without an external counterexample hypothesis):

- Cycle: n=4(k+1), independent cycle blocks as described in T6, a=3/2. Strong nested Scaling constants (7/2,2,4,2), validity, homoskedasticity, means (a,-a,a,-a) per block and C=2I+G hold. In each row beta=0, n Var(betaHat)=4, b=-9/4, and compatibility has the singleton G. E[n V1]=7/4-12/n; Var(n V1)=44/n-96/n^2-288/n^3; n V1 tends in probability to 7/4. For every 0<epsilon<9/4, both absolute-error>epsilon and underestimation>epsilon probabilities relative to 4 tend to one. For every real t, P(sqrt(n) betaHat<=t)->Phi(t/2). For every 0<alpha<1, clipped coverage tends to 2Phi(z_alpha sqrt(7/16))-1<1-alpha. For a=3, strong Scaling constants (5,2,4,2), validity, homoskedasticity, beta=0, scaled variance 4, and n V1->-5 hold; the one-block sample (5,-1,5,-1) has probability 1/16 and V1=-9/4.
- Path: for every real t equal to 1 or 2, n=3(k+1), independent blocks (t+u,-2t+3u/5+4v/5,t+v) with mutually independent fair signs u,v; G=R are disjoint paths 0-1-2, theta=1 and degree caps the true degrees. Strong Scaling constants (6,2,29/15,2), validity, homoskedasticity, beta=0, scaled variance 29/15, and singleton compatibility hold. E[n V1]=(29-10t^2)/15-217/(135(k+1)); n V1 tends to (29-10t^2)/15. When t=1, both absolute-error and underestimation probabilities tend to one for 0<epsilon<2/3; for every 0<alpha<1, coverage tends to 2Phi(z_alpha sqrt(19/29))-1<1-alpha. When t=2, the probability V1<0 tends to one and every such clipped coverage tends to zero.

Docstring reading: a corrected list of sufficient conditions for variance control and Wald coverage, with explicit homoskedastic counterexamples to the unrestricted original known-edge estimator. The conjunction is not itself phrased as the negation of a printed assertion.

Junk-value audit: means and covariance are Bochner integrals; W supplies bounded weighted moments, while all witnesses have finite support. The mean-bias liminf is of a bounded real sequence under W (bounded means and true degree), and coverage liminf is of probabilities in [0,1], so their real-order fallback values cannot supply a conclusion. Alpha is restricted to (0,1), ensuring a genuine finite Gaussian quantile; all square roots in coverage are clipped, and 7/16,19/29 are positive. All relevant n and k+1 denominators are positive. Natural caps are truncated before correction; the t_i=0 branch is explicit. The graph spectral input is always symmetric, so the zero branch is unused. Finite maxima exist under validity; their values are measurable despite absent selector measurability premises. Empty graphs are genuine feasible graphs, not empty feasible sets. Boolean blocks use proven index bounds, positive block width and finite nonempty sample spaces. No log, rpow, infinite-probability conversion, or partial-function default is used.

## SAP.P011a.T9

The theorem conjoins three universal asymptotic principles, a finite inequality, and a concrete failure example.

For each of the three principles quantify F, real c1,c2,c3,c4, and W first; then a natural p (fixed across rows), real n_k-by-p matrices D_k, a real vector gamma in R^p, and coefficient estimators gammaHat_k from R^(n_k) to R^p. A coefficient estimator is assumed AE measurable under each row law. Put z_i=theta_i(Y_i-(D gamma)_i), r_i=theta_i(Y_i-(D gammaHat)_i), and Vres(B,r)=q_(I+B)(r)/n^2, with NO sample centering of r.

1. Root-n principle: assume every raw Y_i is integrable and E Y_i=(D_k gamma)_i, there exists a real B with ||row_i(D_k)||_2<=B uniformly in rows and units, and sqrt(n)||gammaHat-gamma||_2=O_p(1). Then quantify any graph selector A, assume validity and that A maximizes Vres(B,r) over the compatible graphs in every sample. Conclude E z_i=0, E z_i z_j=C_ij, sqrt(n) maxAbs(r-z)=O_p(1), ||r-z||_2=O_p(1), ||z||_2/sqrt(n)=O_p(1), n Vres(G,r) converges in probability to n Var(betaHat), and Vres(A,r) is conservative.
2. Prediction principle: instead assume the same correct mean model, a uniform almost-sure bound on |z_i|, and ||r-z||_2/sqrt(n)->0 in probability. Quantify A and assume validity and its samplewise Vres maximization. Conclude the same oracle consistency and maximum conservativeness. There is no bounded-design or coefficient-rate hypothesis in this branch.
3. Misspecification principle: the vector is now gammaStar and no correct-mean hypothesis is assumed. Assume AE-measurable coefficients, uniformly almost-sure bounded z_i=theta_i(Y_i-(D gammaStar)_i), and ||r-z||_2/sqrt(n)->0 in probability. Conclude n Vres(G,r)-n Var(betaHat) converges in probability to q_(I+G)(h)/n, where h_i=E X_i-theta_i(D gammaStar)_i. No constraints or optimizer occur in this branch.
4. For every natural n (including zero), every symmetric real n-by-n M, then every real r,z, |q_M(r)-q_M(z)|<=||M||op ||r-z||_2(2||z||_2+||r-z||_2).
5. Failure family: n=4(k+1), independent signs e_i, raw outcomes Y_i=e_i at even i and n e_i at odd i, w=(1,0,-1,0) repeated, theta_i=2w_i, and true/recruitment graphs empty with zero caps. It satisfies nested Scaling constants (2,1,2,3). Set D_i=(1,w_i). The zero coefficient vector is a correct integrable mean model. For every row Var(OLS intercept)=n/2+1/(2n), and E[n Vres(G,fitted residual)]=n+2-7/n. This statistic fails to converge in probability to 2.
6. More finite facts, for every block count m>0 (n=4m): theta_i=2w_i; for every real data y, OLS intercept=bar(y), OLS slope=(2/n)sum_i w_i y_i, betaHat=OLS slope, and n Vres(G,r)=(4/n)sum_(w_i!=0)(y_i-bar(y)-w_i OLS slope)^2. Every row has n Var(betaHat)=2, beta=0, E Y_i=0, and almost surely |theta_i Y_i|<=2. The residual statistic expectations at m=1,2 are exactly 17/4 and 73/8.

OLS means the algebraic formula (D^T D)^(-1) D^T y, with Mathlib's nonsingular inverse, not a generalized inverse or minimizer chosen from a set.

Docstring reading: sufficient conditions for model-based residuals, a perturbation bound, an extension based on prediction error, a misspecification bias formula, and a correctly specified OLS example that lacks the needed estimation rate.

Junk-value audit: every statistical row has n>0; sqrt(n)>0 in all stochastic-rate quotients. The finite perturbation inequality at n=0 is a legitimate 0<=0. Norm square roots have nonnegative arguments by sums of squares. Raw integrability is explicit in a correct mean model; bounded weighted residuals and W give all required weighted moments elsewhere. Nonintegrable fitted coefficients need not have moments, since the conclusions use probability rates rather than expectations of them. OLS's inverse returns zero for singular real Gram matrices, but the displayed witness has D^T D=diag(n,n/2) with m>0, so no singular default enters its formulas. The general residual principles do not use OLS or invert any design. p=0 is allowed and means the unique empty coefficient vector and zero prediction; it is an ordinary subcase. No liminf, log, rpow, sInf or toReal(infinity) occurs in this target. Block width four and all local indices are certified. No graph nesting is required in the universal principles; the explicit failure example asserts the stronger property.

## SAP.P011a.T10

The theorem is a conjunction of the following assertions; its top level has no hypotheses.

1. For every a,b>0 and every infinite Boolean pattern s, the fixed-mean family has n=k+1, X_i=Y_i=a sign(s_i)+b e_i with independent fair e_i, weights one, empty true and recruitment graphs, and caps zero. It satisfies nested Scaling constants (2a+b,1,b^2,2). The mixture family has Y_i=a e_i+b f_i with all e_i,f_i mutually independent and satisfies nested Scaling constants (a+b,1,a^2+b^2,2).
2. For every natural n, including zero, the mixture law equals the sum over all 2^n Boolean patterns on Fin n of 2^(-n) times the corresponding fixed-mean law. A finite pattern is extended to natural indices by false outside i<n; those outside indices are never observed in this identity.
3. For each a,b>0, no sequence of Borel real statistics T_k on R^(k+1) is simultaneously convergent in probability to b^2 under every fixed infinite mean pattern and to a^2+b^2 under the mixture. Also every such Borel statistic with P_mix(a^2+b^2-T_k>epsilon)->0 for all epsilon>0 fails convergence to b^2 for at least one fixed infinite pattern. The same two impossibility assertions are additionally stated for arbitrary functions T_k, with no Borel hypothesis.
4. For every real a,b, every infinite pattern s and n>0 (positivity of a,b is not required for this moment clause), fixed-model means are a sign(s_i), diagonal covariances are b^2, beta is the average of those means, and n Var(betaHat)=b^2. Mixture means and beta are zero, diagonal covariances are a^2+b^2, and n Var(betaHat)=a^2+b^2.
5. There is no single observed-data rule V, whose arguments in order are n, y in R^n, natural caps d, real weights theta and a graph R, such that for every F, all positive scaling constants and W, n V(n,Y,d,theta,R) converges in probability to n Var(betaHat). The rule has no law, target variance or true graph argument. No measurability premise is imposed on this rule; the finite-support impossibility already covers arbitrary functions.
6. For every F and constants with W, the identically zero unscaled statistic converges in probability to Var(betaHat_k). This uses the unscaled target, which tends to zero.
7. For every n>0, the fixed-mean model a=b=1 with every s_i=true has exactly the law of (2 I_i)_i for independent Bernoulli(1/2) indicators. In this model Var(betaHat)=1/n and E[betaHat/n]=Var(betaHat). Thus the literal sampling-design example is an all-one population and independent half inclusion; it is not a general design-unbiasedness theorem.

Docstring reading: a scaled universal impossibility and a conservativeness-versus-consistency obstruction, verified finite mixtures and moments, the distinction from unscaled consistency, and one design-information example. It calls itself a corrected statement, not a refutation of a canonical assertion.

Junk-value audit: a,b>0 give genuinely different positive scaled targets. The moment clause validly permits a=0 or b=0; it makes no impossibility assertion there. Family sizes k+1 are positive; n>0 guards finite variance and unbiasedness formulas. At n=0 the mixture law identity has one pattern and mass 2^0=1, so no empty normalization arises. ENNReal inverse of 2^n is finite and positive, never inverse-zero or inverse-infinity. Uniform Boolean-vector spaces are nonempty even on Fin 0. All laws have finite support; all moments therefore exist, and arbitrary functions restricted to each finite support have measurable representatives. Events evaluated for those functions have ordinary finite-support probabilities, so dropping the global Borel hypothesis does not manufacture a nonmeasurable counterexample. Every law has mass one, preventing toReal(infinity). The false extension of finite patterns is explicit, but no observed coordinate can reach it. No square root, log, rpow, infimum, liminf, singular inverse or hazardous natural subtraction enters this statement. All casts are exact embeddings of finite natural counts.
