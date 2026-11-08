# Blind reading

This file was written before opening claims.json or record.json. The source inventory is closure.json; all five target docstrings, every listed source definition, and the source expressions generating the listed auxiliary proof declarations were read. Generated structure constructors/projections have precisely their field meanings below. Generated _proof_* declarations prove finite-index bounds, positivity, graph symmetry/irreflexivity, probability-measure instances, or displayed finite definitions; they introduce no additional mathematical parameters or assumptions. Imports were inspected; the definitions ultimately import Mathlib.

## Common notation, fully expanded

The following notation is used in each section to avoid repeatedly writing the same finite sums and integrals. It is a translation of the SAP definitions, not additional assumptions.

* A graph on n vertices is a Boolean function A on Fin n × Fin n, symmetric in its arguments and false on the diagonal. Its real adjacency matrix a has entry 1 where A is true and 0 otherwise. Its degree at i is the natural-number sum of these indicators. I is the identity matrix, so M_A = I+a has diagonal 1, not an all-ones diagonal contribution off the diagonal.
* A model consists of a Borel probability measure P on the Euclidean coordinate space R^(Fin n), deterministic real weights theta_i, graphs G (true dependency) and R (recruitment), and natural-number degree caps d_i. Thus probability measures and finite total mass are part of the type. Write E f = integral f dP, X_i(y)=theta_i y_i, B(y)=sum_i X_i(y)/n, beta=E B, mu_i=E X_i, delta_i=mu_i-beta, Sigma_ij=E[(X_i-mu_i)(X_j-mu_j)], and Var f=E[(f-E f)^2].
* For a real vector x, bar x=sum_i x_i/n, z_i=x_i-bar x, and s_n^2(x)=sum_i z_i^2/n. The divisor is n. For a real matrix H, q_H(x)=sum_i sum_j H_ij x_i x_j. V_1(A,x)=q_(I+a)(x-bar x)/n^2. The oracle uses G. Its scaled value is n V_1(G,X). The scaled true variance is n Var B. Mean bias is q_(I+a_G)(delta)/n, mean spread is sum_i delta_i^2/n, and mean variance is sum_i Sigma_ii/n.
* A graph A is compatible exactly when every true recruitment edge is an A edge and degree_A(i) <= d_i for every vertex. A maximizer is compatible and has objective at least that of every compatible Boolean graph; no uniqueness is built into this definition. An upper edge is a pair (i,j) with i<j. A fractional feasible vector has one real a_ij per upper edge, 0<=a_ij<=1, value 1 on recruitment edges, and sum of incident values <=d_i at each vertex.
* Dependency of a model means: for every two disjoint finite vertex subsets S,T, if there are no G edges from S to T, the entire subvectors (y_i)_(i in S) and (y_j)_(j in T) are independent under P, in Mathlib's IndepFun sense. It is a dependency graph condition, stronger than just zero covariance off edges. Homoskedastic means all weighted-coordinate variances Sigma_ii are equal.
* A family has positive natural sizes n_k, n_k tending to infinity along the natural-number atTop filter, and a model at each size. Nested means sizes are nondecreasing and, for each consecutive pair, an injection of vertices preserves both edges and nonedges of the true graphs. It does not impose a joint coupling or agreement of outcome laws across sample sizes.
* Scaling(F,c1,c2,c3,c4) is the conjunction of nesting; strictly positive real constants c1,c2,c3,c4; dependency at every sample; almost surely |X_i-beta_k|<=c1 for every vertex and sample; degrees of G bounded above by c2 (after exact casting to reals); n_k Var B_k tending to c3; and |theta_i|<c4 for every sample and vertex. Validity means the true graph is compatible at every sample.
* T_k ->_p a_k means, for every real epsilon>0, P_k(|T_k-a_k|>epsilon) tends to 0. Conservativeness of an unscaled variance estimator V_k means, for every epsilon>0, P_k(n_k(Var B_k-V_k)>epsilon) tends to 0. Tightness of T_k means: for each epsilon>0 there are B>0 and a natural k0 such that P_k(|T_k|>B)<=epsilon for every k>=k0. All the limits in this document use k -> infinity.
* For an n by p real design D, H=D^T D, ols(D,y)=H^(-1)D^T y, and olsTheta(D)=n H^(-1)D^T. Matrix inverse here is Mathlib's determinant/adjugate nonsingular inverse. A mean model requires every raw coordinate y_i integrable and E y_i=(D b)_i. True residuals are e_i=theta_i(y_i-(Db)_i). Fitted residuals are rhat_i=theta_i(y_i-(D bhat)_i). V_res(A,r)=q_(I+a_A)(r)/n^2 and does not center r again. Euclidean l2(x)=sqrt(sum_i x_i^2).

Common totalization audit: real division by zero is defined as zero; the displayed statistics need positive n. Every family has positive sizes, every finite theorem using B has positive n or a nonempty Fin n, and every block regression is guarded by positive block count. Real integrals are Bochner integrals, zero if the function is not integrable; the statistical meaning is therefore on the stated integrability domains or the usual measure-theoretic domain. Scaling's almost-sure bound makes all weighted-coordinate moments finite (beta is a fixed real); mean models separately require raw-coordinate integrability, and design regularity bounds raw outcomes. Measure.real is ENNReal.toReal of a measure value; probability measures have values at most one, so infinity cannot occur. Independent empty subvectors and empty finite sums have their standard values and do not eliminate positive sample sizes. All casts of naturals to reals in these formulas are exact. There are no logarithms, nonintegral real powers, integer casts, or unspecified partial-function defaults in these closures. Additional target-specific domain checks follow.

## SAP.P011b.T15

This is a closed proposition, with no external hypotheses. It asserts all the following properties of two explicit sequences. Every universal quantifier mentioned below is part of the conclusion.

For a Boolean u (lower=false, upper=true) and K=k+1 positive blocks, n=4K. The true and recruitment graphs are K disjoint copies of the four-vertex star, with center position 0 and leaves 1,2,3. The caps are 3 at each center and 1 at each leaf. Every theta is 1. The law is the pushforward of the uniform probability measure on (Fin 3 -> Fin 4) × Fin 48 independently at each block. At each block, independently sampled latent integers U_1,U_2,U_3 in {0,1,2,3} determine leaves L_j as indicators U_j<t_j. The lower thresholds are (1,1,1); upper thresholds are (3,1,2). Independently V is uniform on {0,...,47}. Put C=sum_j L_j. The center is the indicator V<33+4C (lower) or V<18+4C (upper). The coordinate vector is center followed by the three leaves. Local vertex position is the natural remainder modulo 4; block index is natural division by 4. Both index functions have their bounds proved. This is an actual finite probability law, not a specification by desired moments.

The two designs D have an intercept column of ones and a covariate repeated blockwise: x^-=(3,-1,-1,-1), x^+=(0,1,-1,0). The coefficients are b^-=(3/8,1/8), b^+=(1/2,1/4). For all u,K>0, every outcome coordinate is integrable and E y=D b; the covariate sum is zero; D^T D=diag(4K,12K) in the lower model and diag(4K,2K) in the upper model; its determinant is nonzero; the row of n(D^T D)^(-1)D^T for the intercept is theta=(1,...,1); and, for every data vector y, its intercept OLS estimate is bar y=B(y).

For both u and every K>0, the block subvectors are jointly independent (Mathlib iIndepFun) and each block's pushforward law is the displayed one-block law. In that one-block law the three leaf coordinates are jointly independent; their success probabilities are (1/4,1/4,1/4) or (3/4,1/4,1/2). For every binary leaf pattern s, its event has strictly positive probability and

P(center=1 and leaves=s)/P(leaves=s)
= a + sum_j(s_j-p_j)/12,

where a=3/4 lower or 1/2 upper. These conditional probabilities lie in [11/16,15/16] lower and [3/8,5/8] upper. All coordinates are binary almost surely for both sequences.

The lower sequence satisfies Scaling with (c1,c2,c3,c4)=(1,3,27/128,2), validity, and homoskedasticity. Its means in each block are (3/4,1/4,1/4,1/4), covariance matrix is (3/16) I+(1/64) a_G, beta=3/8, scaled true variance=27/128, and mean bias=-3/128. Its scaled oracle expectation at K=k+1 is 3(64K-47)/(1024K). The scaled oracle converges in probability to 3/16, and P(27/128-scaledOracle>3/256) tends to one. Its ratio of limiting estimate to true scaled variance is (3/16)/(27/128)=8/9.

The upper sequence satisfies Scaling with (1,3,47/192,2) and validity. Its beta is 1/2 and scaled true variance is 47/192 at every sample; its scaled oracle converges in probability to 53/192. For every u,K>0, the individual means are mu^-=(3/4,1/4,1/4,1/4) or mu^+=(1/2,3/4,1/4,1/2), and offsets from beta are delta^-=(3/8,-1/8,-1/8,-1/8) or delta^+=(0,1/4,-1/4,0). On one star, q_(I+a_G)(delta^-)=-3/32 and q_(I+a_G)(delta^+)=1/8. For each Boolean u, q_(I+a_G)(y-mu)/n converges in probability to the true scaled variance (27/128 lower, 47/192 upper).

At every sample of both models the only compatible Boolean graph is G. More strongly, the fractional feasible vectors are exactly the adjacency upper triangle of G. For every selection A_k(y) of raw compatible maximizers, at every sample and every data vector A_k(y)=G_k, and n_k V_1(A_k(y),y) converges to 3/16 or 53/192 as appropriate. The selection quantifier precedes its maximizing premise. Existence is also apparent because G is compatible and unique.

Let Phi(t)=P(Z<=t) for Mathlib's real Gaussian Z of mean 0 and variance 1; z_alpha=inf{t in R: 1-alpha/2<=Phi(t)}. For every real 0<alpha<1, the lower-model clipped coverage

P(|B-beta|<=z_alpha sqrt(max(V_1(G,y),0)))

tends to 2 Phi(z_alpha sqrt(8/9))-1, strictly smaller than 1-alpha. The probability V_1(G,y)<0 tends to zero. The printed-domain coverage, with the additional event V_1(G,y)>=0 and sqrt(V_1(G,y)) in its inequality, has the same limit for every such alpha.

Junk-value audit: K>0 and n=4(k+1)>0 protect all sample-size denominators and full-rank inverse calculations. The leaf-pattern denominators are explicitly positive. The uniform latent spaces are nonempty finite sets for every K used. Center thresholds lie strictly between 0 and 48, so the indicator construction realizes the stated conditional Bernoulli probabilities without clipping or saturation of probabilities. The normal quantile is a real sInf; for 0<alpha<1 its defining upper level set is nonempty and bounded below, and the Gaussian is nondegenerate, so no empty/unbounded-set value is used. The square root is Mathlib's nonnegative square root (zero on nonpositive inputs); the clipped coverage explicitly defines what negative estimates mean, while the second coverage explicitly excludes them and their probability vanishes. sqrt(8/9) is in its positive domain. All explicit laws are finitely supported; every displayed moment is finite. The Boolean and fractional programs are nonempty and uniquely feasible. No real liminf or limsup occurs in this target. No natural subtraction or problematic casting is used. Hypotheses in auxiliary implications are satisfied by their explicit positive-block designs and graph G, rather than made inconsistent.

## SAP.P011b.T16

This is a closed conjunction of eight propositions. It does not take the older T16Statement as an external hypothesis. Its quantifiers and conclusions are as follows.

1. For all naturals n,p with 0<p<=n, all models m on n vertices, designs D, coefficient vectors b, and j in Fin p: if det(D^T D) is nonzero, E y=D b with all y_i integrable, and theta_i=[n(D^T D)^(-1)D^T]_(j,i), then for every y, B(y)=ols(D,y)_j; beta=b_j; and for every i, mu_i=theta_i(Db)_i and delta_i=theta_i(Db)_i-b_j. These are finite identities without Scaling.

2. For all n,p with 0<p<=n, m,D,j satisfying full rank and those same coefficient weights (a mean model is not required), for all data y and all c in R^p: ols(D,y+Dc)=ols(D,y)+c; the fitted residual vector is unchanged; for every Boolean graph A its residual objective is unchanged; and the raw centered weighted vector changes by the deterministic vector (theta_i(Dc)_i-c_j)_i.

3. Under the finite full-rank/weight hypotheses of item 2, for every intercept index j0 with D_(i,j0)=1 for every i and j!=j0, every data y and real t: the j-th coefficient, the whole fitted residual vector, and every graph's residual objective are unchanged by adding t to every response. The law is not changed or needed for these pointwise identities.

4. For every family F and every real c1,c2,c3,c4 satisfying Scaling, all of the following hold: (a) n V_1(G,X)-n Var B converges in probability to the moving deterministic mean bias q_(I+a_G)(delta)/n; (b) n V_1(G,X) is consistent for n Var B iff the bias tends to zero; (c) the raw oracle is conservative iff the real liminf of that bias is nonnegative; (d) validity implies existence of a maximizing graph selection, and nonnegative liminf bias implies that every maximizing selection is conservative; (e) if all weighted-coordinate means equal beta at every sample, the oracle is consistent and, under validity, every compatible maximum is conservative. A graph selection is an arbitrary function of k and y with graph value; a maximizing selection must maximize at every y. Conservativeness here is exactly the one-sided scaled tail definition in the common notation.

5. An explicit family demonstrates that condition (c)'s nonnegative liminf need not follow from conservativeness of all compatible maxima. Use the lower binary-star model of T15, with independent blocks, n=4(k+1), theta=1 and the same true star graph and degree caps, but empty recruitment graph. It satisfies Scaling(1,3,27/128,2) and validity. For every k its two-column intercept/covariate design has nonzero Gram determinant, means D(3/8,1/8), and the stated OLS intercept weights. Its scaled true variance is 27/128, mean bias is -3/128, and the empty graph is compatible. For every y the empty-graph scaled estimate is exactly s_n^2(y); this sample variance converges in probability to 15/64. A raw maximizing selection exists and every such selection is conservative, although liminf mean bias is strictly negative. This does not assume the maximum equals the empty-graph objective.

6. A finite pointwise witness for raw slope noninvariance has n=p=2, D rows (1,-1),(1,1), theta=(-1,1), empty true/recruitment graphs and caps zero, and P=Dirac at zero responses. The Gram determinant is nonzero, E y=D*0, theta is the OLS slope weight vector, the first column is an intercept, the slope at y=0 equals the slope at y=(1,1), and the fitted residual vectors at these data agree. Nevertheless the empty-graph raw estimates are respectively 0 and 1/2. The shifted vector need not have positive probability under the unshifted Dirac law: this assertion compares objective formulas at data vectors, not random events.

7. For every family and positive Scaling constants satisfying Scaling, every fixed natural p, fixed j in Fin p, size-indexed designs D_k and deterministic coefficients b_k in R^p, assume 0<p, p<=n_k at every k, all Gram determinants nonzero, integrable coordinate mean models E y=D_k b_k, the j-th OLS weight formula at every k,i, and the following design regularity: there exist real Bx,By>=0 and lam>0 such that all Euclidean row norms of D_k are <=Bx, all |y_i|<=By almost surely at every k, and for every k and z in R^p,

lam ||z||_2^2 <= z^T (D_k^T D_k/n_k) z.

Then sqrt(n_k)||ols(D_k,y)-b_k||_2 is tight. At every k and every y define e_i=theta_i(y_i-(D_k b_k)_i) and d_i=theta_i[D_k(ols(D_k,y)-b_k)]_i; here d_i is an error vector, not the model's natural degree cap. Fitted residuals equal e-d pointwise. At every k,y,

|q_(I+a_G)(e-d)-q_(I+a_G)(e)|/n
<= (1+c2) [2 (||e||_2/sqrt n)(||d||_2/sqrt n)+||d||_2^2/n].

Both sides (each viewed as a random statistic) converge in probability to zero. The fitted residual scaled oracle n V_res(G,rhat) is consistent for n Var B. Under validity a residual-maximizing graph selection exists; every such selection yields a conservative residual estimator. No sample-size constancy of b_k is imposed. There is no separate assumption of an OLS rate: it is a conclusion from the stated bounds, graph dependency and coercivity.

8. For every n (including n=0), recruitment graph R, true graph G and caps d for which G is compatible, every family of graph-indexed real objectives f(A,y) measurable in y for each A, and every selection A(y) attaining the finite compatible maximum at every y, y -> f(A(y),y) is measurable. The graph selection itself need not be measurable: every maximizer gives the same value of a finite maximum. This conclusion supplies measurability of the statistics used above and does not base a counterexample on a nonmeasurable event.

Junk-value audit: the finite OLS items have 0<p<=n and nonzero Gram determinant; the singular inverse's zero default cannot supply their conclusions. The residual asymptotic item has positive family sizes, fixed nonempty p through j, nonzero determinants and lam>0. sqrt(n) and every Euclidean norm have nonnegative arguments, and sqrt(n) denominators are strictly positive. A zero error vector is allowed and is an ordinary zero norm. All weighted moments in item 4 exist from Scaling. Raw coordinate means are explicitly integrable in finite mean-model items, and regularity bounds them in item 7. Real liminf is the supremum of eventual lower bounds, which could use a default value for an unbounded sequence; here |delta_i|<=c1 and degree<=c2 imply |meanBias|<=(1+c2)c1^2, uniformly, so the liminf is the ordinary finite real liminf. The explicit witness has constant finite negative bias. Finitely many Boolean graphs and validity guarantee a nonempty feasible set and attained finite maximum, with no empty supremum or infimum. Empty graph types at n=0 in the measurability item are singletons and that item uses no division or moments. The two-point witness has finite moments and full rank; it asserts pointwise data-shift behavior. Uniform star latent spaces are finite/nonempty. The existential regularity constants and positive variance limits are compatible with nontrivial intercept designs and independent bounded outcomes. There is no logarithm, real-power domain issue, natural subtraction, or unbounded moment calculation in the stated domains.

## SAP.P011b.T17

The outer quantifiers are: for every natural n, every proof hn of n>0, every probability model m on R^n, and every four indices i,j,k,l in Fin n (not required distinct), the following five implications all hold. They do not assume Scaling, graph validity, or homoskedasticity. All integrals are with respect to m.law. Write X_a=theta_a y_a, B=sum_a X_a/n, r_a=X_a-B, and

Q_ab=E(X_a X_b)-E(X_a B)-E(X_b B)+E(B^2).

Let v=(i,j,k,l) index the four positions by Fin 4, Y_a=y_(v_a), and t_a=theta_(v_a). The moment domains and assertions are:

* Weighted pair domain: B^2 is integrable, and for each of the two pairs (i,j),(k,l), X_a X_b, X_a B, X_b B are integrable. On this domain E(r_i r_j)=Q_ij and E(r_k r_l)=Q_kl.
* In addition, weighted fourth domain: for every subset S of the four position indices, (product_(a in S) X_(v_a)) B^(4-|S|) is integrable. Then C=E[(r_i r_j)(r_k r_l)]-E(r_i r_j)E(r_k r_l) equals the actual Mathlib covariance integral E[((r_i r_j)-E(r_i r_j))((r_k r_l)-E(r_k r_l))], equals E(r_i r_j r_k r_l)-Q_ij Q_kl, and equals F(X_i,X_j,X_k,X_l,B)-Q_ij Q_kl. The fully expanded F is

E(X_i X_j X_k X_l)
-E[B(X_i X_j X_k+X_i X_j X_l+X_i X_k X_l+X_j X_k X_l)]
+E[B^2(X_i X_j+X_i X_k+X_i X_l+X_j X_k+X_j X_l+X_k X_l)]
-E[B^3(X_i+X_j+X_k+X_l)]+E(B^4).

* Constant moment domain: for every nonempty subset S of the four positions, product_(a in S) X_(v_a) is integrable. For every real constant b,

Cov((X_i-b)(X_j-b),(X_k-b)(X_l-b))
= Cov(X_i X_j,X_k X_l)
-b[Cov(X_i X_j,X_k)+Cov(X_i X_j,X_l)+Cov(X_i,X_k X_l)+Cov(X_j,X_k X_l)]
+b^2[Cov(X_i,X_k)+Cov(X_i,X_l)+Cov(X_j,X_k)+Cov(X_j,X_l)].

Here each displayed Cov is explicitly E(fg)-E f E g, with the stated domains making it an ordinary covariance.

* Raw pair domain: B^2 and, for each pair (a,b) in {(i,j),(k,l)}, y_a y_b, y_a B and y_b B are integrable. Then each Q_ab and E(r_a r_b) equals

t_a t_b E(y_a y_b)-t_a E(y_a B)-t_b E(y_b B)+E(B^2).

* In addition, raw fourth domain: for every subset S of the four positions, (product_(a in S) Y_a) B^(4-|S|) is integrable. Then the preceding product covariance agrees with Mathlib's covariance; E(r_i r_j r_k r_l) is the full raw expansion

sum_(S subset Fin 4) (-1)^(4-|S|) (product_(a in S) t_a) E[(product_(a in S) Y_a) B^(4-|S|)],

and the covariance is that expansion minus the product of the two displayed raw pair expansions. The source lists all 16 terms explicitly, one fourth-order term, four negative cubic terms, six positive quadratic terms, four negative linear terms, and E(B^4).

Junk-value audit: hn makes n nonzero, so B's division is ordinary. Empty products are 1; the empty subset in each fourth domain therefore requires integrability of B^4, and the full subset requires the four-coordinate product, with exponent zero. Every S is a subset of Fin 4, so |S|<=4: the natural subtraction 4-|S| never truncates a negative intended exponent. The moment assumptions are separated: no fourth-moment assumption is needed for the first pair identities, and the constant-centering expansion does not assume random-B moments. Repeated selected vertices are still distinct positions in Fin 4, so powers of the same variable are not lost by Finset deduplication. Zero weights are allowed; the raw domains explicitly retain raw integrability when raw expressions are requested, preventing misuse of 0 times a junk integral. The difference-of-expectations definition of Cov is connected to the centered Mathlib covariance where it is used. The finite subset domains include all terms needed for the relevant integrals; no nonintegrable-default identity is being used. There are no quantiles, matrix inverses, square roots, real liminfs, or empty extrema in this target. A finite Dirac model, including the constant witness of T18, satisfies all five moment domains simultaneously.

## SAP.P011b.T18

This is a closed explicit counterexample calculation. Its model is n=4, P=Dirac at y=(1,1,1,1), theta=(2,3,4,5), empty true/recruitment graphs, and caps all zero. Its beta and B at the supported point are 7/2. Define r=(2y_0-B,3y_1-B,4y_2-B,5y_3-B), U=r_0 r_1, V=r_2 r_3. At the support r=(-3/2,-1/2,1/2,3/2), U=V=3/4. The theorem asserts that E(UV)-E U E V=0 and that the actual centered-integral Mathlib covariance agrees with this zero.

The first compared expression is E[(2y_0-B)(y_1-B)(4y_2-B)(5y_3-B)]-E U E V. It has no weight 3 on the second factor in the first expectation, and its value is 9/4.

For precision, the other expression uses the following explicitly printed bracket P, with t=(2,3,4,5), raw Y_a=y_a, a_ab=E(Y_a Y_b), h_a=E(Y_a B), and h=E(B^2):

P=a_01 a_23
-t_0 t_1 t_2 a_01 h_2-t_0 t_1 t_3 a_01 h_3+t_0 t_1 a_01 h
-t_2 t_3 h_0 a_23
+t_0 t_3 h_0 h_3+t_0 t_2 h_0 h_2-t_0 h_0 h
-t_1 t_2 t_3 h_1 a_23
+t_1 t_3 h_1 h_3+t_1 t_2 h_1 h_2-t_1 h_1 h
+t_2 t_3 h a_23-t_2 h h_2-t_3 h h_3+h^2.

In particular the leading coefficient is 1 and the fifth term lacks t_0 relative to the full pair-moment product. With F the fully expanded fourth moment from T17, the second compared expression F-120 P has value 93009/16. The bracket-only repair is the separately defined F-[P+(120-1) a_01 a_23], moving only the leading bracket and retaining all the other printed coefficients; it equals -70. The theorem additionally gives the arithmetic identity 9/16-(9/16+140-70)=-70. The actual covariance differs from each of 9/4, 93009/16, and -70. The fully corrected F minus the product of the two fully weighted pair-moment formulas is zero.

The docstring explicitly calls this a refutation of the printed claim. The mathematical statement establishes only these explicit comparisons; whether those expressions and this witness fit the canonical printed reading must be checked after the blind stage.

Junk-value audit: n=4 and all weights are ordinary finite reals. Dirac at a finite vector has every polynomial moment finite; both covariance definitions have their ordinary values. All events/coordinates are Borel. Constant coordinates satisfy every subvector independence demanded by the empty dependency graph. No division is by zero, and the displayed rational denominators are positive integers. No square roots, logarithms, real powers, quantiles, empty extremal sets, natural subtraction, or default partial functions occur. There is no independence violation hidden in reusing the deterministic coordinates. This is a genuinely positive-size probability model, not a vacuous implication.

## SAP.P011b.T19

The first part quantifies over every family F, every four real constants c1,c2,c3,c4, every proof of Scaling(F,c1,c2,c3,c4), the hypothesis that each model is homoskedastic, and the hypothesis that every mean weighted variance sigma_k^2=sum_i Sigma_ii/n_k is strictly positive. It then asserts the following. Let

rho_ij = Sigma_ij/sigma_k^2,
K_k = 1+(sum_i sum_j a_G,ij rho_ij)/n_k,
V_2^*(y)=s_n^2(X)/n_k * K_k.

(The definition sets rho=0 when sigma_k^2=0, a branch excluded here.) For every sample k and every data vector y, the exact identity

n_k V_2^*(y)-n_k Var B_k = K_k [s_n^2(X(y))-sigma_k^2]

holds. The remainder s_n^2(X)-sigma_k^2-sum_i delta_i^2/n_k converges in probability to zero. If the deterministic mean spread sum_i delta_i^2/n_k tends to zero, n_k V_2^* is consistent for n_k Var B_k. Moreover at every sample K_k=(n_k Var B_k)/sigma_k^2 and 0<=K_k<=1+c2. If for every sample and vertex mu_i=beta_k, consistency follows. The constants and all probability statements have exactly the meanings in the common notation; validity is not required for this universal part because the estimator uses the true graph.

The second part is an explicit family demonstrating failure of auxiliary consistency with heterogeneous means. Put n=k+1, let a_n=n/[2 ceil(n/2)] where ceil(n/2) is implemented as natural (n+1)/2, and let independent fair signs S_i take values -1,+1. The raw outcomes are y_i=2+S_i at even zero-based positions i and S_i at odd positions. All weights equal a_n. The true/recruitment graphs are empty and caps are zero. These are the pushforwards of uniform probability on the finite Boolean-vector space. The theorem asserts Scaling with (2,1,1,2), validity, homoskedasticity, positive common variance sigma_n^2=a_n^2, and beta_n=1 for every sample. It asserts that mean spread tends to one, and

P(|n V_2^*(y)-n Var B|>1/2) tends to one.

This is an assertion about an explicit family meeting the standing scaling and positive-variance hypotheses, not an implication with an extra assumption of nonvanishing spread.

Junk-value audit: every family sample has n>0. The general rho denominator is explicitly positive, so its zero-variance convention is irrelevant; positivity also makes the claimed ratio K_k=(n Var B)/sigma_k^2 ordinary division. K_k can be zero at finite samples without a new division by it. Scaling bounds all weighted moments, and the explicit family has finite support. In the witness, (n+1)/2 is floor division in the natural numbers and equals ceil(n/2); for n>0 it is at least one, so the weight denominator is positive. No truncated subtraction is used. Although the weight definition would return zero at n=0, that value is never used by the family. The independent signs are genuinely independent coordinate draws and the empty graph is a dependency graph. Norms, square roots, liminf/limsup, logarithms, unbounded extrema and partial-function defaults do not occur here. Positive common variance, bounded centered weighted outcomes, bounded weights, nested growing empty graphs, and the nonzero limiting scaled variance are jointly compatible in the explicit construction.

## Closure source coverage

The complete closure inventory is retained in closure.json. Sources read for T15: Part1, Part2, the block-index/uniform/star definitions of Part3, all of Part5, and WholeW1 through T15WholeStatement (including w1StarB and its finite-vector proof helpers). Sources read for T16: its listed Part1/Part2/Part3 definitions and all WholeW2 declarations. Sources read for T17: its listed model/expectation/weight definitions, pairMoment, fourthMoment, rawFourthMoment, covOf, and all T17Statement local moment-domain definitions. Sources read for T18: those same basic moment definitions, emptyGraph, constantWitness, every cw* declaration in its closure, T18Core and T18Statement. Sources read for T19: all its common model/family/dependency/scaling definitions, sign/emptyGraph/uniform definitions, meanVariance, varianceRemainder, rho, V2star, T19Statement, w1CorrelationFactor, w1AlternatingWeight, w1AlternatingModel, w1AlternatingFamily, and T19WholeStatement. Constructors, projections and every source-generated proof named by each closure were covered along with their enclosing declaration. Unrelated target declarations in imported source files were not used to infer a claim.
