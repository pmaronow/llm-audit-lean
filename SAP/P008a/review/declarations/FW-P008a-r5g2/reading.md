# Blind reading

Saved at stage 1, before opening `claims.json` or `record.json`. This is a reading of the elaborated statements and their source definitions, not a comparison with the canonical claims.

I read all five entries of `closure.json`, all source declarations in their closures, and the 86 distinct auxiliary declarations with source line 0 by compiling `scratch/ClosureProofs.lean`. The auxiliary declarations supply numeral instances, nonemptiness of Boolean function spaces, finite-index bounds, membership of the constructed nodes in their fields, normalization of uniform laws, and sum-type elimination. They add no substantive mathematical hypotheses. Structure constructors and projections have the fields described below. No local `AGENTS.md` was found.

## Common mathematical notation (all SAP definitions expanded)

Indices `Fin N` mean integers 0 through N−1. An assignment is a function from those indices to Booleans; write z_i in {0,1} for its real-valued indicator. A finite law consists of real numbers Q(z)≥0 summing to 1. Expectation is the finite sum E_Q f=Σ_z Q(z)f(z); covariance is E_Q[(f−E_Q f)(g−E_Q g)], and variance is covariance with itself. A uniform law assigns reciprocal cardinality to each element of a nonempty finite type. On all Boolean assignments its mass is 2^(−N), so it is the independent fair-coin law. The predicate called common Bernoulli means exactly Q(z)=Π_i (p if z_i=1, otherwise 1−p).

An override z[i←b] changes coordinate i to b and leaves every other coordinate fixed. The marginal of a statistic F at i,b is E_Q F(z[i←b]); it is an intervention expectation over the original law, not a conditional expectation defined by division by an event probability.

The spatial ambient space is Euclidean R² (`EuclideanSpace R (Fin 2)`). A spatial model consists of a set A⊆R², nodes p_i∈A, a Borel measure ζ on R², and a potential-outcome function Y(x,z)∈R. Put C_i(d)={x∈A:dist(p_i,x)=d}, μ_i(d)=ζ restricted to C_i(d), v_i(d)=(μ_i(d)(R²)).toReal, and

    A_i(d;f) = v_i(d)^(−1) ∫ f dμ_i(d),
    M_i(d,z) = A_i(d; x↦Y(x,z)),
    m_i(b,d) = E_Q M_i(d,z[i←b]),
    τ_i(d) = m_i(1,d)−m_i(0,d),
    AMR(d) = N^(−1) Σ_i τ_i(d),
    risk(b,d) = N^(−1) Σ_i m_i(b,d).

For any finite array M_i(z), its finite AMR is N^(−1)Σ_i[E_Q M_i(z[i←1])−E_Q M_i(z[i←0])]. For a finite point set C, its counting mean is (Σ_{x∈C} f(x))/|C|.

For regression, let n_1=Σ_i z_i and n_0=N−n_1 (subtraction in R). For a response vector m, put mbar_b=Σ_{i:z_i=b}m_i/n_b, e_i=m_i−mbar_(z_i), w_i=z_i/n_1−(1−z_i)/n_0, and g_i=w_i e_i. The Hajek statistic for assignment-dependent responses is Σ_i z_i M_i(z)/n_1−Σ_i(1−z_i)M_i(z)/n_0. The binary design matrix X has rows (1,z_i); H=(XᵀX)^(−1), beta=H Xᵀm, u=m−X beta, the actual OLS treatment weights are a_i=(H Xᵀ)_(1,i), and the actual OLS treatment scores are G_i=a_i u_i. Matrix operations here are Mathlib finite matrix operations. Given an arbitrary real array D and real c, write

    K_ij(c)=1 if D_ij≤c, otherwise 0,
    V(g,D,c)=Σ_i Σ_j g_i g_j K_ij(c),
    B_ab=Σ_i Σ_j K_ij(c) u_i u_j X_ia X_jb.

Thus the OLS treatment sandwich variance is (H B H)_(1,1). The archived rule is V(g,D,c+j) when c>0, and V(g,D,c) otherwise, with j a natural-number position cast to R. The physical rule is V(g,D,c) and ignores its natural-number position argument.

The four fixed toy nodes, with exact real rational coordinates, are

    (2028297641/2147483648, 4318520789/2147483648),
    (7976664621/2147483648, 1029755657/268435456),
    (1053580245/536870912, 2017196647/2147483648),
    (7110225301/2147483648, 499145583/1073741824).

The linearization score used below is φ_i(z)=2z_i(M_i(z)−m_1)−2(1−z_i)(M_i(z)−m_0), with m_1,m_0 arbitrary real constants unless otherwise stated.

## SAP.P008a.T6

Source: `Challenge/Part1.lean:62–76`, `Defs/Part6.lean:93–139`, and the common definitions above. The theorem is a conjunction of five assertions, with no external parameters or hypotheses.

1. For every natural N, assignment z, response vector m∈R^N, real array D, and real c, in that order, if c≥0, n_1≥1 and n_0≥1, then the Hajek statistic for the fixed responses equals Σ_i w_i m_i; every actual OLS treatment weight a_i equals w_i; every OLS residual u_i equals e_i; and (H B H)_(1,1)=V(g,D,c). Within this conclusion, for every proof that D_ii=0 for all i and c<D_ij for all distinct i,j, V(g,D,c)=Σ_i g_i²=Σ_{z_i=1}e_i²/n_1²+Σ_{z_i=0}e_i²/n_0², and V(g,D,c)=V(g,D,0). D need not be symmetric, nonnegative or metric for the general identities.
2. For every g∈R^4, all distinct fixed toy nodes are farther than 2/5 apart, V(g,dist,2/5)=Σ_i g_i²=V(g,dist,0), and for all real t and critical, both endpoints t±critical sqrt(V(g,dist,2/5)) equal the corresponding endpoints with cutoff zero. No particular observed response vector or ten numerical intervals are stated.
3. For every N, base vector b, coefficient array A, constants m_1,m_0, and distinct indices i,j, in that order, set M_i(z)=b_i+Σ_k A_ik z_k. Under the uniform law on Boolean assignments, Cov(φ_i,φ_j)=A_ij A_ji. Distinct indices are a hypothesis; no restriction on diagonal A, constants, signs or sparsity is imposed.
4. For every N>0, base b, coefficient array A, m_1,m_0, in that order, with the same fair-coin law and scores, Var(N^(−1)Σ_i φ_i)=N^(−2)[Σ_i Var(φ_i)+Σ_iΣ_{j≠i}A_ij A_ji]. Furthermore, for every D,c with c≥0, D_ii=0, and A_ij A_ji=0 whenever c<D_ij, the covariance sum N^(−2)Σ_ij Cov(φ_i,φ_j)K_ij(c) equals that variance. The support condition is sufficient; an iff saying it is necessary is not stated.
5. For every N, spatial model, real d,r,c, and family f_ik:R²→R, in that order, assume its field is measurable, all circle masses v_i(d)>0, all circle measures have finite total mass, f_ik(x)=0 whenever r<dist(p_k,x), for every i,k,x on the whole plane, and d+r≤c. Then for every i,k with c<dist(p_i,p_k), the normalized circle integral A_i(d;f_ik)=0. There are no explicit nonnegativity assumptions on d,r,c, no injectivity assumption on nodes, and no explicit integrability assumption on f. The support condition makes each integrand in the conclusion zero on the circle.

Junk-value audit: real reciprocals/division at zero occur in the general definitions, including empty arms and N=0. The first branch excludes empty arms (and consequently N<2), the variance branch assumes N>0, and the pair branch requires actual distinct indices. The purely geometric branch allows N=0 but then has no i,k to conclude about. Matrix inversion returns a totalized inverse on singular matrices; n_1,n_0≥1 ensure det(XᵀX)=n_1 n_0>0 in every matrix assertion. The toy square roots have nonnegative arguments because the theorem identifies them with sums of squares; arbitrary signs of the multiplier do not turn the endpoint equalities into interval coverage assertions. `toReal` sends infinite measure to zero and a Bochner integral is zero for a nonintegrable function; positive finite circle masses explicitly exclude zero/infinite normalization in the geometric branch, and support vanishing excludes use of a nonintegrable nonzero restriction. Negative-radius circles are empty, so for nonempty node types positive mass rules those out. All sums are finite. n_0 uses real, not truncated natural subtraction. There are no logarithms, real powers, suprema, infima, limits or partial functions in this closure.

Docstring reading: a disclosed restricted package of general OLS/HAC and HC0 algebra, a toy-node equality, additive covariance and variance algebra, and a planar support bound. It explicitly omits a numeric smallest distance, ten reproduced interval pairs, and the c=r warning attributed to another theorem.

## SAP.P008a.T7

Source: `Challenge/Part1.lean:78–88`, `Defs/Part7.lean:19–49`, `Defs/WholeW1.lean:144–294`, and the common definitions. This is a closed conjunction proving facts about specified objects, followed by universal algebraic consequences; there are no assumed existence, separation or integrability hypotheses that could hide the construction.

The four centres are p_0=(0,0), p_1=(20,0), p_2=(0,20), p_3=(20,20). Radii r_j are 1,3/2,2,5/2. For k=0,…,39999 set ell_k=2(k+1)−40001, A_k=40000²+ell_k², u_k=(40000²−ell_k²)/A_k, v_k=80000 ell_k/A_k, and q_k=(u_k,v_k). Circle-labelled points are x_ijk=p_i+r_j q_k. The label set is the disjoint union of the four centres and all triples (i,j,k). Its embedding sends a centre label to p_i and a triple to x_ijk. The finite field F is its image; F_c is the image of the triples alone; C_ij is the filter of F by dist(p_i,x)=r_j.

Put B_i=(400,1000,400,1000)_i. The first complete potential-outcome schedule is zero at every centre and, at x_ijk, is 1 precisely when k<B_i−321 z_i (the threshold subtraction is in naturals). The companion schedule is zero at the centres and 1−z_i at every x_ijk. Formally each is extended along the embedding to all of R² with zero as the fallback value. For each schedule the spatial field is F, the nodes are p_i, and ζ is counting measure restricted to F. The finite label mean M^label_ij(z) is the counting mean of the 40000 outcomes over k. The finite law Q is uniform over the sixteen assignments. The displayed observed assignment is (1,1,0,0), with mass 1/16. It has two units in each arm.

The conjuncts say all of the following.

* For each k, A_k>0, 1+u_k≠0, u_k²+v_k²=1, v_k/(1+u_k)=ell_k/40000, and ||q_k||=1. The slope sequence is strictly increasing and q is injective. All x_ijk have the designated distance from their own centre. Distinct centres have distance at least 20. For all distinct centres i,l and all x∈R² with dist(p_i,x)≤5/2, dist(p_l,x)≥35/2.
* The entire label embedding is injective. F has 640004 distinct points. For all i,j, C_ij is exactly the image of k↦x_ijk and has cardinality 40000. For each schedule and i,j the spatial circle is C_ij, its restricted measure is Σ_k δ_(x_ijk), its real mass is 40000 and its extended-real total mass is finite. Every real-valued function f on R² is integrable for that restricted measure, with integral Σ_k f(x_ijk).
* For all assignments and appropriate indices, the schedules have their stated centre and circle values, all outcomes on F are 0 or 1, and actual spatial circle means equal their finite label means. First-schedule means are (B_i−321 z_i)/40000; companion means are 1−z_i.
* For every i,j,b, the first schedule's intervention circle mean is (B_i−321 b)/40000, every node effect and every radius AMR is −321/40000, and the observed Hajek estimate at every radius is −321/40000. Both the sum of the four actual AMRs and the sum of the four actual observed estimates are −321/10000. The companion intervention means are 1−b, every radius AMR and observed estimate is −1, and their four-radius sums are −4. All these assertions also appear for the finite label version, with the same values.
* To define spatial sampling probability, sample a point uniformly from F_c and independently sample z from Q, identify the point's owning centre, replace that owner's coordinate by b, and average the first-schedule outcome. Formally the owner is an extension of x_ijk↦i, with index 0 as fallback. The theorem states F_c has 640000 points, the owner at every x_ijk is i, and, for every f:R²→R, its uniform mean over F_c equals (1/16)Σ_ij[(1/40000)Σ_k f(x_ijk)]. Thus the actual spatial probability equals (1/16)Σ_ij E_Q M^label_ij(z[i←b]). These probabilities are 7/400 at b=0 and 379/40000 at b=1; their difference is −321/40000. For every w∈R^4 with w_j≥0 and Σ_jw_j=1, the weighted sum of actual radius AMRs equals that spatial difference. Adding the unweighted AMR sum to baseline probability yields −73/5000<0 (negativity is also explicitly in the label component).
* For all real a,b∈[0,1], a−b≥−1 and a−b≠−4; it also differs from the companion AMR sum. Finally −321/40000=−0.008025, −321/10000=−0.0321 and 100(−321/40000)=−0.8025.

Junk-value audit: B_i−321 z_i is natural truncated subtraction, but B_i is either 400 or 1000, so no truncation occurs. Every counting denominator is a fixed positive cardinality. The geometry denominators and 1+u_k are explicitly proved positive/nonzero as appropriate. The arbitrary-choice preimage in `Function.extend` could be ambiguous for a noninjective embedding, and fallback values would matter off its image; injectivity is a conclusion of this same theorem, all circle and sampling points are in the image, and values there are explicitly established. The owner fallback is used nowhere in the sampling support. All matrix-free statistics here use four nodes, and every Hajek assertion is at the fixed two-treated/two-control assignment. Empty-arm totalization under other assignments does not enter an asserted Hajek value. Spatial masses are explicitly 40000 and finite, and integrability is proved, so neither infinite `toReal` nor nonintegrable Bochner zero changes an asserted mean. Counting measure on the full uncountable plane would not be sigma-finite, but the actual measure here is restricted to a finite field and is finite. No square roots, logarithms, real powers, limits or empty extrema occur.

Docstring reading: this is a specified synthetic planar binary-outcome construction, not a reconstruction of application data. The contradiction concerns interpreting unnormalized radius sums as probability differences.

## SAP.P008a.T8

Source: `Challenge/Part1.lean:90–111`, `Defs/Part7.lean:52–89`, `Defs/Part4.lean:53–67`, and the common definitions. This is a conjunction of seven independent assertions.

1. For every N, spatial model P, finite law Q on assignments, real d, and then proofs of N>0, measurability of the field, v_i(d)>0 and finiteness of μ_i(d)(R²) for every i, assume each override outcome x↦Y(x,z[i←b]) is integrable on μ_i(d) whenever Q(z)≠0, for every i,b,z, and all Y(x,z) on the field are binary. Then every risk(b,d) lies in [0,1] and AMR(d)=risk(1,d)−risk(0,d). Q need not be independent or have full support.
2. For every J and w,q_0,q_1∈R^J, in that order, assume w_j≥0, Σ_jw_j=1, and 0≤q_bj≤1 for both b. For every pair of reals L,U satisfying L≤q_1j−q_0j≤U for every j, both mixtures Σ_jw_j q_bj lie in [0,1], their difference is Σ_jw_j(q_1j−q_0j), that difference lies in [L,U], and its absolute value is at most 1.
3. For every J>0 and arbitrary q_0,q_1∈R^J, the difference of their equally weighted means is the mean of their differences, and Σ_j(q_1j−q_0j)=J[(Σ_j(q_1j−q_0j))/J].
4. For every J, every nonnegative w∈R^J summing to one, and every real t, Σ_j t=Jt and Σ_jw_jt=t.
5. For every n≥0 and nondecreasing real sample s indexed 0,…,n, followed by real q,m,x,y with 0≤q≤1 and m>0, x≤y iff x/m≤y/m, |x|≤|y| iff |x/m|≤|y/m|, and Q7(s/m,q)=Q7(s,q)/m. Here Q7 is explicitly the following formula: h=nq, j=min(max(floor(h),0),n) (the first maximum is conversion of an integer to a natural), gamma=h−j, and Q7=(1−gamma)s_j+gamma s_min(j+1,n). On the stated q-domain this is ordinary type-7 linear interpolation of a sorted nonempty sample.
6. The supplied constants obey (−19/625)/4=−19/2500, (−321/10000)/4=−321/40000, (21/625)/4=21/2500, −321/40000<−19/2500 and −321/10000<−19/625. They are not formally identified with empirical estimates or permutation outputs.
7. In the finite four-node companion counting schedule from T7, with 40000 labels at each of four radii, outcome 1−z_i at every label, and independent fair assignments, the sum of four finite AMRs is −4. For every a,b∈[0,1], a−b differs from that sum. This branch does not assert a planar realization.

Junk-value audit: the circle-average pitfalls (zero or infinite mass and nonintegrable outcomes) are excluded exactly on positive-Q override terms by the first branch's assumptions. At zero-Q assignments arbitrary totalized integrals are multiplied by zero in finite expectations and cannot change them. N>0 rules out empty node averages. A normalized nonnegative vector cannot exist on J=0 (the empty sum would be 0=1); such impossible subcases do not vacate the J>0 instances. The equal-mean branch separately assumes J>0. Quantile indexing clamps an integer floor through `Int.toNat` and `min`; q∈[0,1] ensures no unintended clipping/extrapolation, and at q=1 the final interpolation has gamma=0. n=0 is a legitimate singleton sample. Division by m is protected by m>0, division by four is nonzero, and the companion label means divide by 40000. No negative square roots, log, real powers, empty extrema or limiting operations occur. No matrix inverse occurs in this statement's closure.

Docstring reading: a disclosed restriction covering probability-mixture algebra, positive rescaling, a label-level counterexample and numerical divisions. It expressly excludes a joint sampling-space construction, empirical attribution, the actual grid, some finite extrema/order-statistic language and planar realization of the companion model.

## SAP.P008a.T9

Source: `Challenge/Part1.lean:113–122`, `Defs/Part7.lean:92–129`, `Defs/WholeW1.lean:14–107`, and the common definitions. This is a closed conjunction with the following content.

The spatial construction uses nodes p_i=(2i,0), i=0,…,3, field R², measure Σ_{i=0}^3Σ_{a=0}^3 δ_((2i+a/10,0)), and outcome Y(x,z)=Σ_i [2i if dist(x,p_i)≤3/10, otherwise 0], independent of z. At each radius d_j=(j+1)/10, j=0,1,2, every circle mass is 1, its total measure is finite, its outcome is integrable for every assignment, and M_i(d_j,z)=2i. Node distances are D_il=|2i−2l|. The short grid is (1/5,3/10), the long grid is (1/10,1/5,3/10), and short[0]=long[1]=1/5.

At assignment z=(0,0,1,1) both arm counts are 2. The response vector at radius 1/5 is m=(0,2,4,6), its Hajek estimate is 4, its actual OLS coefficients are (1,4), residuals (−1,1,−1,1), treatment weights (−1/2,−1/2,1/2,1/2), and scores G=(1/2,−1/2,−1/2,1/2). The scalar contrast scores g agree with these. With supplied cutoff 2/5 the archived rule at natural positions 1 and 2 gives respectively variance 1 and 1/2 for the same spatial responses and distances. The effective cutoffs are 7/5<2 and 12/5; K(7/5) is exactly the identity, while K(12/5) has entries 1 iff |i−l|≤1. The first HAC is Σ_iG_i²=1; the second is 1+2(G_0G_1+G_1G_2+G_2G_3)=1+2(−1/4+1/4−1/4)=1/2.

For every N,z,m with n_1,n_0≥1, the theorem additionally states det(XᵀX)=n_1n_0≠0, Xᵀu=0, a_i=w_i and u_i=e_i for all i, G=g as functions, Σ_iG_i=(H Xᵀu)_1=0, and for every real D,c the treatment sandwich entry equals V(G,D,c). These universal algebraic facts do not assume the displayed example or a metric D.

For every four-node configuration p in R² with each coordinate in [0,4], all squared distances are at most 32. The fixed toy nodes satisfy this box condition. Numerically, 2/5+6=32/5, (32/5)²=1024/25>32 and 3.438−(−0.038)=869/250>0. For every such boxed p, every assignment z and response m with both arm counts at least one, the cutoff 32/5 includes every pair; V(G,dist,32/5)=(Σ_iG_i)²; the archived variance at cutoff 2/5 and position 6 is zero; and for every real multiplier h, the displayed endpoint difference [1.7+h sqrt(V)]−[1.7−h sqrt(V)] is zero and 2h sqrt(V)≠869/250. An older conjunct also states the fixed-toy-node zero variance and width incompatibility under n_1,n_0≠0, and that all fixed-toy squared distances are at most 32.

Junk-value audit: all actual OLS inverses used have determinant n_1n_0>0. In the older fixed-four-node branch nonzero arm counts also imply positivity, because they are genuine counts and sum to 4. The construction explicitly gives positive finite masses and integrability; no zero/infinite `toReal` or nonintegrable integral drives its responses. The outcome construction uses real rational coordinates and bounded indicators, so it is measurable. The square-root argument in every width assertion is proved zero, not an arbitrary negative estimate collapsed by `Real.sqrt`. Every grid index is a valid finite index. The position is a natural cast to R; positions 1 and 2 correspond to the same radius appearing at the first and second places, although no generic search-for-grid-position function is defined. The archived variance rule is defined directly as a mathematical model; there is no theorem about execution of external software. No unbounded extrema, limits, logarithms, real powers or partial-function defaults occur. Distinctness is not required in the generic box bound, appropriately for that bound.

Docstring reading: claims a planar example of position sensitivity and a generic box-bound sixth-row incompatibility for the supplied cutoff-plus-position model, with actual OLS vectors and normal equations. It does not claim to verify an external archived implementation against its source.

## SAP.P008a.T10

Source: `Challenge/Part1.lean:124–131`, `Defs/Part8.lean:19–37`, `Defs/WholeW1.lean:14–43,109–142`, and the common definitions. This is a closed conjunction of the older correction statement, all the universal OLS identities just expanded under T9, and strengthened actual-OLS consequences.

For every N,z,m,D,c, with both arm counts nonzero, and every natural j,k, the physical variance of g at position j is V(g,D,c), equals that at position k, and Σ_ig_i=0. If additionally D_il≤c for all pairs, V(g,D,c)=(Σ_ig_i)²=0. No c≥0, symmetry or metric hypothesis on D is imposed. The same physical variance at cutoff 2/5, scores (1/2,−1/2,−1/2,1/2) and distances |2i−2l| is 1 at both positions 1 and 2.

For every z,m on the fixed four toy nodes, with nonzero arm counts, V(g,dist,2/5)=Σ_ig_i²=V(g,dist,0) and the archived variance at cutoff 2/5 and position 6 is zero. This is the older scalar-score component.

The actual-OLS component quantifies first over every N,z,m,D,c with arm counts at least one, and then every j,k. It states physicalVariance(G,D,c,j)=V(G,D,c)=physicalVariance(G,D,c,k); if all D_il≤c, then V(G,D,c)=(Σ_iG_i)²=0. Every pair of fixed toy nodes satisfies K_il(2/5)=1 iff i=l. Finally, for every z,m on those four nodes with both arm counts at least one, V(G,dist,2/5)=Σ_iG_i²=V(G,dist,0); V(G,dist,2/5)>0 iff some actual OLS residual u_i is nonzero; V(G,dist,2/5)=0 iff all actual OLS residuals vanish; and archivedVariance(G,dist,2/5,6)=0. The accompanying universal OLS identities state det(XᵀX)=n_1n_0≠0, normal equations Xᵀu=0, a=w, u=e, G=g, Σ_iG_i=(H Xᵀu)_1=0, and the sandwich equality for all D,c.

Junk-value audit: the general scalar-score branch's nonzero count hypotheses and the actual-OLS branch's at-least-one hypotheses exclude all empty arms; since arm counts are nonnegative integer-valued reals they are equivalent requirements. Thus singular inverses and zero count divisions are not used in any substantive assertion. The fixed toy-node cutoff is diagonal, so its HAC is a genuine nonnegative sum of squares, and positivity is tied to an actual nonzero residual rather than assumed. The position-invariance equality is partly definitional, since the physical rule ignores position; the OLS, positivity and all-pairs consequences are additional nondefinitional assertions. There are no integrals, quantiles, square roots, logarithms, real powers, empty extrema, limits, or partial-function defaults in this closure. Natural positions are cast only in the archived rule; a corrected cutoff may be any real in the generic algebra.

Docstring reading: correcting the final bandwidth removes position sensitivity, gives HC0 on the toy nodes, and characterizes positivity by actual residuals. Its last sentence about justifying radius enlargement is prose guidance, not a formal criterion for dependence coverage.
