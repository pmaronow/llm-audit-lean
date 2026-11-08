# Blind reading of the Challenge

This file was written and saved before opening either `claims.json` or `record.json`. The fourteen Challenge stubs are `SAP.P013a.T1` through `SAP.P013a.T14`. Each asserts the correspondingly numbered `T*Statement` in Defs, without additional parameters or hypotheses on the stub itself. All mathematical content below comes from those definitions.

## Common objects and expanded definitions

All designs are finite probability spaces: a finite type Ω with a strictly positive real weight w(z) for every z, and sum_z w(z)=1. Thus Ω cannot be empty. E_P X=sum_z w(z)X(z), Cov_P(X,Y)=E_P(XY)−E_P X E_P Y, Var_P X=Cov_P(X,X), and Pr_P(A)=sum_{z:A(z)} w(z). All these sums are finite; no measurability or integrability conventions are involved.

A population F for P, N, K has an exposure map D:Ω×{0,…,N−1}→{0,…,K−1} and an arbitrary real outcome table y_i(d). Put I_i^d(z)=1{D(z,i)=d}, p_i(d)=E I_i^d, p_ij(d,e)=E(I_i^d I_j^e), and Y_i(z)=y_i(D(z,i)). `Positivity F d` means, for every unit i, 0<p_i(d)<1. Let T_d=sum_i y_i(d), mean_d=T_d/N, τ_de=(T_d−T_e)/N, H_d(z)=sum_i I_i^d(z)y_i(d)/p_i(d), mean-hat_d=H_d/N, and τ-hat_de=(H_d−H_e)/N. All divisions here are real divisions. They are totalized in Lean (division by zero is zero), so the hypotheses making denominators positive matter.

Use ordered pairs throughout, and define

- B_ij^{de}(z)=I_i^d I_j^e [(p_ij(d,e)−p_i(d)p_j(e))/p_ij(d,e)] [y_i(d)/p_i(d)] [y_j(e)/p_j(e)].
- v_d(z)=sum_i I_i^d(1−p_i(d))[y_i(d)/p_i(d)]² + sum_{i≠j} B_ij^{dd}(z). The zero joint terms are zero by real division by zero.
- a_d(z)=sum_{i≠j:p_ij(d,d)=0} [I_i^d y_i(d)²/(2p_i(d))+I_j^d y_j(d)²/(2p_j(d))].
- A_d=sum_{i≠j:p_ij(d,d)=0} y_i(d)y_j(d).
- C_de(z)=sum_{i≠j:p_ij(d,e)>0} B_ij^{de}(z) − sum_{i,j:p_ij(d,e)=0} [I_i^d y_i(d)²/(2p_i(d))+I_j^e y_j(e)²/(2p_j(e))]. The second sum includes i=j.
- Vhat_de(z)=[v_d+a_d+v_e+a_e−2C_de]/N².

`PairIndependent F i j` is independence of the individual exposure variables: p_ij(d,e)=p_i(d)p_j(e) for every d,e, including when i=j if requested. `VectorIndependent P D A B` says for every pair of full exposure vectors a,b, Pr(D_A=a_A,D_B=b_B)=Pr(D_A=a_A)Pr(D_B=b_B). On finite alphabets this is independence of the two subvectors.

For a Boolean directed relation h, `PrintedNoEdge h A B` prohibits an edge (i,j) whenever any of (i∈A,j∉B), (j∈A,i∉B), (i∉A,j∈B), (j∉A,i∈B) holds. Notice the complements. `CorrectedNoEdge` instead prohibits edges between A and B in either direction (the definition repeats each of the two alternatives, which does not change the proposition). `PrintedDependency` and `GenuineDependency` require vector independence for every disjoint pair A,B satisfying, respectively, these no-edge predicates. `RowBound h m` bounds every outgoing row sum by m, including the diagonal. The relation need not be loopless. The symmetric pair indicator G_h(i,j)=1{i=j or h(i,j) or h(j,i)} counts the diagonal and both orientations.

`independentProduct P Q` has weights w_P(z)w_Q(u); `replicateDesign P R` has weights product_{r<R} w_P(z_r). R=0 is an empty product on a singleton. With R independent replicates and an independent observed assignment z, C_i=sum_{r<R} I_i^d(z_r), ptilde_i=(C_i+1)/(R+1), and Htilde_d=sum_i I_i^d(z)Y_i(z)/ptilde_i. The C_i and ptilde_i are real-valued, not natural-number division. `IsMinimumPi F d p0` requires an attained minimum: some i has p_i(d)=p0 and all i have p0≤p_i(d). κ=(sum_i |y_i(d)|)/|T_d|, with the usual Lean totalization if T_d=0.

A sequence S contains, for each n≥0, N=n+1 units, a finite sample space `Fin supportSize`, a finite exposure alphabet, two distinct labels d_n,e_n, and positivity at those two labels for every unit and n. Other labels need not have positive probabilities. Write P_n,F_n, τhat_n,τ_n,V_n=Var(τhat_n), and Vhat_n=Vhat_{d_n e_n}. The sequence conditions expand as follows.

- `NestedPopulationSetup`: there exist, first, injections label_n from each alphabet into ℕ, then fixed distinct labels d,e∈ℕ and one table y:ℕ×ℕ→ℝ, such that for every n label_n(d_n)=d, label_n(e_n)=e, and for every unit i<n+1 and every local label a, F_n.outcome(i,a)=y(i,label_n(a)). Only the comparison labels must be identified across all sizes.
- `StandingPositivity`: every label at every size satisfies positivity.
- `ComparisonBounded`: there exist real c1≥0,c2>0 such that for all n,i the two comparison outcomes have absolute value ≤c1 and both reciprocal comparison probabilities have absolute value ≤c2.
- `Condition3`: the same type of common bounds, but for every label at every size.
- `Condition4`: there exists a sequence of Boolean matrices g_n such that for every n,i,j, g_n(i,j)=false implies pair independence for every pair of labels, and N^−2 sum_ij 1{g_n(i,j)}→0.
- `Condition5Printed`: there exist a single natural m and relations h_n such that for every n, printed dependency holds and every outgoing row sum is ≤m.
- `Condition5Genuine`: the same, using genuine dependency and additionally requiring h_n symmetric for every n.
- `Condition5CorrectedDirected`: genuine dependency and the common outgoing row bound, without symmetry.
- `Condition6`: there exists real c>0 with N V_n→c.
- `LowerTailCondition`: for every real δ>0, Pr(N Vhat_n<N V_n−δ)→0.
- `ScaledVarianceConcentration`: N(Vhat_n−E Vhat_n)→0 in probability.
- `ScaledVarianceVanishes`: Var(N Vhat_n)→0.
- `JointLowerBound S b`: for every n and distinct i,j each of p_ij(d_n,d_n), p_ij(e_n,e_n), p_ij(d_n,e_n) is either zero or ≥b. The reverse contrast is covered by reversing the ordered pair.
- `PositiveJointDomain S n`: at least one of those three kinds of off-diagonal joint probabilities is positive. `IsMinimumPositiveJoint S n b` requires b>0, attainment among those off-diagonal joints, and b≤every positive such joint. No minimum is required when the positive domain is empty.

Convergence in probability to a real a means, for every ε>0, Pr(ε<|X_n−a|)→0, on these possibly varying finite spaces. `TendsNormal P X μ v` means convergence of Pr(X_n≤x) at every real x to the cdf of `ProbabilityTheory.gaussianReal μ v`. Mathlib's second Gaussian parameter is the **variance** v∈ℝ≥0; at v=0 it is a point mass. `TendsDistribution` instead quantifies only over continuity points of the target cdf. Write Φ for the cdf of N(0,1) and z_α=inf{x∈ℝ:1−α/2≤Φ(x)}. For 0<α<1 this is the finite positive usual normal critical value. Square roots are Mathlib's nonnegative real square root (zero for nonpositive arguments). `seqCoverage` is Pr(0≤Vhat_n and |τhat_n−τ_n|≤z_α sqrt(Vhat_n)). A negative estimate explicitly counts as noncoverage. All coverage liminfs are of real sequences in [0,1], so Mathlib's conditional-completeness convention does not replace an unbounded limit by a junk value.

Mathlib sources followed: `Probability/CDF.lean` (`cdf_eq_real`: the cdf is the probability of (−∞,x] for probability measures); `Probability/Distributions/Gaussian/Real.lean` (`gaussianPDFReal`, `gaussianReal`, and its probability-measure instance); `Order/LiminfLimsup.lean` (liminf is the supremum of eventual real lower bounds); `Data/Finset/Powerset.lean` (`powersetCard n U` consists exactly of n-element subsets of U). `Tendsto … atTop (𝓝 a)` is ordinary sequence convergence; `atTop atTop` is divergence to +∞; `∀ᶠ n in atTop` means for every sufficiently large n.

## T1

This is an unconditional conjunction about an explicit family, including a universally quantified finite part. For every natural r and every proof 2≤r, take N=2r, ε=1/N², t=1−2ε, and r independent pair assignments with atom weights (ε,1/2−ε,1/2−ε,ε) at a=0,1,2,3. A pair's first exposure is 0 for a<2 and 1 otherwise; its second exposure is 0 for even a and 1 for odd a. Units 2k,2k+1 have outcomes +1,−1 respectively at both labels. Pair index is floor(i/2). Define signed score q(a)=4(first exposure−second exposure), with subtraction in ℤ before conversion to ℝ, and b_N(a)=2/ε if the exposures agree and 16−4/t otherwise. Then:

1. For every i,d, p_i(d)=1/2 and |y_i(d)|=1. For every distinct i,j and all d,e, their joint is ε or 1/2−ε for a common pair according as d=e or d≠e, and is 1/4 for different pairs. The relation h(i,j)=1{same pair} satisfies both genuine and printed dependency and RowBound h 2. The first-moment/dependency/row-bound assertions are also repeated as a separate conjunction.
2. τ_10=0. For every realized assignment z, τhat_10=N^−1 sum_k q(z_k), N² Vhat_10=sum_k b_N(z_k), and Vhat_10>0. The true variance is 8t/N and E Vhat_10 equals it. The probability every pair splits is t^r; the probability some pair fails to split is ≤1/N. On every all-split assignment N Vhat_10=8−2/t. Var(N Vhat_10)=4(N−2)^4(N+2)^4/[N^5(N²−2)]. For one pair, E b_N=16t.
3. For the sequence r=n+2, with n over all naturals, N V→8, N Vhat→6 in probability, Vhat/V→3/4 in probability, Var(N Vhat)/(4N)→1, and Var(N Vhat)→+∞. sqrt(N)τhat converges in distribution to N(0,8).
4. For every real α, if 0<α<1, the interval coverage Pr(|τhat−τ|≤z_α sqrt(Vhat)) converges to 2Φ(z_α sqrt(3/4))−1, and that value is strictly smaller than 1−α.

## T2

The conjunction contains five separate implications, with separate universal quantifiers over S in each clause.

1. For every S, nested setup, comparison boundedness, genuine symmetric Condition 5, Condition 6, and the lower-tail condition together imply: for every α with 0<α<1, liminf_n coverage_n(α)≥1−α.
2. For every S, centered scaled-variance concentration alone implies the lower-tail condition.
3. For every S, vanishing scaled-estimator variance alone implies the lower-tail condition.
4. For every S satisfying nested setup, comparison boundedness and genuine symmetric Condition 5, for every real b>0 with JointLowerBound S b, there exists real C≥0 such that eventually Var(N Vhat_n)≤C/N; also the lower-tail condition holds.
5. For every S satisfying those same three setup conditions, for every real sequence b_n, if for every n with a nonempty positive off-diagonal joint domain b_n is its attained positive minimum, there exists C≥0 such that eventually Var(N Vhat_n)≤C/(N b_n). Moreover, if N b_n→+∞, the lower-tail condition holds. No constraint on b_n is imposed at sizes with an empty positive domain. This clause does not separately assert centered concentration.

## T3

This unconditional statement gives exact computations for a two-unit example. Assignments (0,0),(0,1),(1,0),(1,1) have respective weights 2/9,4/9,1/9,2/9. For a real a, outcomes at exposure 0 are zero, and outcomes at exposure 1 are a for unit 0 and −1 for unit 1. `signedOneReplicate a` is Htilde_1 with one independent replicate, written directly with denominator (I_i^1(replicate)+1)/2.

For a=2: every unit and both labels satisfy positivity; p_0(1)=1/3, p_1(1)=2/3, T_1=1, E Htilde_1=2/9, and absolute relative bias is 7/9. Also 4/9<7/9, 1/2<7/9, (1−1/3)²≤1/2<(1−1/3). The number R=1 satisfies 1≥log(1/2)/log(1−1/3)−1, while the bias exceeds 1/2. For a=1 the total is zero, E Htilde_1=−1/3, and |E Htilde_1−T_1|>|T_1|(1−1/3)². There are no quantified hypotheses on these explicit examples.

## T4

For every finite design P and population F, if N>0, then for every label d satisfying positivity, every natural R≥1, and every real attained minimum p0 of its marginal probabilities, let E=E Htilde_d and T=T_d. Both equalities

E=sum_i y_i(d)[1−(1−p_i(d))^(R+1)]=T−sum_i y_i(d)(1−p_i(d))^(R+1)

hold, and |E−T|≤(1−p0)^(R+1) sum_i |y_i(d)|. If T≠0, then κ≥1 and |(E−T)/T|≤κ(1−p0)^(R+1). Under the additional alternative (all y_i(d)≥0) or (all y_i(d)≤0), κ=1, the bound improves to (1−p0)^(R+1), and for every real b>0, R≥log b/log(1−p0)−1 implies relative bias≤b. Without that sign assumption, for every b>0 the sufficient condition is R≥log(b/κ)/log(1−p0)−1. Separately, the rational inequalities (1999/2000)^10594≤1/200<(1999/2000)^10593 hold. The displayed general theorem excludes R=0.

## T5

This is an unconditional six-part theorem.

1. For every N and disjoint finite subsets A,B of its units, PrintedNoEdge for the identity relation is equivalent to A=B=∅.
2. For every finite design, N,K and exposure map, the identity relation satisfies PrintedDependency and has row bound 1.
3. For every natural q, on 3q units let h(i,j) mean i≠j and floor(i/3)=floor(j/3). This is symmetric and loopless. For every disjoint A,B, PrintedNoEdge is equivalent to A=B=∅. Every row has exactly 2 edges. For every finite design, alphabet and exposure map on these 3q units, PrintedDependency holds for this h.
4. For every N, use one fair Bernoulli assignment shared by every unit and outcomes zero at both labels. The identity relation satisfies printed dependency and row bound 1; every i,d has p_i(d)=1/2; every i,j has p_ij(1,1)=1/2 and fails PairIndependent.
5. For every N and Boolean relation g, if every g(i,j)=false implies PairIndependent in that shared family, sum_ij 1{g(i,j)}=N².
6. There exists an ExperimentSequence S with standing positivity, Condition 3 and printed Condition 5, but not Condition 4.

The universally quantified zero-unit/zero-triangle cases in the first five clauses are included, but the existential sequence always has n+1≥1 units.

## T6

1. For every N, Boolean h and subsets A,B (without a disjointness hypothesis for this equivalence), CorrectedNoEdge is equivalent to h(i,j)=h(j,i)=false for every i∈A,j∈B. If h is symmetric, this is equivalent just to h(i,j)=false for every such pair.
2. For every finite design, population and relation h satisfying genuine dependency, every i,j with G_h(i,j)=0 are pair independent. For every natural m with RowBound h m, sum_ij G_h(i,j)≤N(2m+1); if h is also symmetric, the sum is ≤N(m+1).
3. For every ExperimentSequence S, directed corrected Condition 5 implies Condition 4.

No positivity, nonempty-unit or outcome-bound assumption is needed for these finite independence/counting statements.

## T7

This is an unconditional explicit block-family theorem. Put L_0=0, L_r=2^(2^r) for r≥1, and r(i)=min{r≥1:i≤L_r}. The natural-number infimum is over a nonempty set. At unit i≥1, if r(i) is odd set both outcomes to 1. If r(i) is even, put k=i−L_{r(i)−1}−1; for even k use (y_i(0),y_i(1))=(0,2), and for odd k use (2,0). These are natural subtractions within their block, so no truncation changes k. Assign units independently to fair Bernoulli labels. B_N is the set of even-block units among 1,…,N, b_N=|B_N|, s_i=1 for even k and −1 for odd k, and R(z_i)=2z_i−1.

1. For every natural N≥1: for every i,d, p_i(d)=1/2 and |y_i(d)|≤2; distinct i,j have every joint 1/4; the identity relation satisfies genuine dependency and row bound 1; |τ_10|≤2/N; at every assignment τhat−τ=(2/N)sum_i R(z_i); V=4/N; Vhat=(4/N²)sum_i Y_i²; N Vhat=4+4b_N/N+(8/N)sum_{i∈B_N} s_i R(z_i); E(N Vhat)=4+4b_N/N; Var(N Vhat)=64b_N/N²≤64/N.
2. For every N≥1 and assignment, Vhat>0.
3. For every r≥1: if r is odd then 0≤b_{L_r}/L_r≤L_{r−1}/L_r; if r is even then 0≤1−b_{L_r}/L_r≤L_{r−1}/L_r. If r≥2, L_{r−1}/L_r=1/2^(2^(r−1)).
4. For the full sequence N=n+1, let W=N Vhat and T=(τhat−τ)/sqrt(Vhat). For every n, N V=4≤E W. Var(W)→0 and (τhat−τ)/sqrt(V) tends to N(0,1). There is no real s such that W→s in probability, no real s such that sqrt(V/Vhat)→s in probability, and no probability measure μ on ℝ to which T converges in distribution (at its cdf continuity points).
5. At odd block endpoints N=L_{2n+1}, W→4 in probability, sqrt(V/Vhat)→1 in probability, and T tends to N(0,1). At even endpoints N=L_{2n+2}, W→8, sqrt(V/Vhat)→1/sqrt(2), and T tends to N(0,1/2), with 1/2 its variance.

## T8

For every family of finite types L_n, designs P_n, real statistics estimate_n and Vhat_n, and real deterministic sequences target_n,V_n, suppose for every n that V_n=Var(estimate_n)>0. For every real c>0, assume N V_n→c, (estimate_n−target_n)/sqrt(V_n) tends to N(0,1), E(N Vhat_n)≥N V_n for every n, and Var(N Vhat_n)→0, where N=n+1. Put W_n=N Vhat_n and v_n=N V_n. Then all of the following hold:

1. W_n−E W_n→0 in probability.
2. For every ε∈(0,1), at every n, Pr(W_n<(1−ε)v_n)≤Var(W_n)/(ε²v_n²), and those probabilities tend to zero.
3. For every α∈(0,1) and every ε∈(0,1), liminf Pr(0≤Vhat_n and |estimate_n−target_n|≤z_α sqrt(Vhat_n))≥2Φ(z_α sqrt(1−ε))−1. For every α∈(0,1), that same liminf is ≥1−α.
4. For every real s≥c, if E W_n→s and additionally Vhat_n(z)>0 for **every** n and realization z, then W_n→s in probability, sqrt(V_n/Vhat_n)→sqrt(c/s) in probability, 0<sqrt(c/s)≤1, and (estimate_n−target_n)/sqrt(Vhat_n) tends to N(0,c/s).

The target sequence is arbitrary; no unbiasedness or consistency assumption is added. Strict positivity of all Vhat realizations is a hypothesis only of the last implication.

## T9

Two independent assertions: (i) for every S, nested setup, standing positivity, Condition 3 and Condition 4 imply mean-hat_{d_n}−mean_{d_n}→0 in probability; (ii) for every four real numbers estimate,target,V,Vhat with V>0,Vhat>0,

(estimate−target)/sqrt(Vhat)=[(estimate−target)/sqrt(V)] sqrt(V/Vhat).

There is no contrast consistency or coverage conclusion in this proposition.

## T10

Define Displays3(x,p) by the closed bin p−1/2000≤x≤p+1/2000. The unconditional statement says:

1. For every e,s,z∈ℝ, (e−zs)+(e+zs)=2e.
2. There are no reals e,L,U simultaneously in the bins centered at (0.295,0.050,0.536) and satisfying L+U=2e.
3. There are no such reals for the bins centered at (0.306,0.212,0.404).
4. For every e,s,z, neither triple (e,e−zs,e+zs) is in the first three bins nor in the second three bins.

There is no restriction that s or z be positive, so the incompatibility covers all symmetric real intervals.

## T11

For every two finite subsets U,neighbors⊆ℕ and every natural i,n, assume i∈U, neighbors⊆U, i∉neighbors, |neighbors|=39, 1≤n≤|U|−39 (the displayed upper subtraction is in ℕ). Sample uniformly from all n-element subsets S of U. Let p=Pr(i∈S and S∩neighbors=∅), q=Pr(i∉S and S∩neighbors=∅). Then

p=choose(|U|−40,n−1)/choose(|U|,n), q=choose(|U|−40,n)/choose(|U|,n), and q=[(|U|−39−n)/n]p.

The binomial arguments use natural subtraction, while the last ratio uses real subtraction. The assumptions imply |U|≥40 and n≤|U|, so the sampling denominator is positive and |U|−40 is the actual number of nonneighbors other than i. In addition, if |U|≤10n+5, then q≤9p; if also p≤27/40000, then q≤243/40000<1/100; if instead q≥1/100, then p≥1/900 and p>27/40000. Every implication is inside the single universal quantification above.

## T12

The conjunction negates two universal assertions, so it asserts counterexamples exist to each (they need not formally be the same example). The universal assertions being negated quantify, in order, over any finite design and population, N>0, a label d with positivity, any natural R (including zero), any attained minimum p0, and a nonzero T_d. The first asserts |(E Htilde_d−T_d)/T_d|≤(1−p0)^(R+1). The second then quantifies over every real b>0 and asserts that R≥log b/log(1−p0)−1 suffices for |(E Htilde_d−T_d)/T_d|≤b. Thus this theorem **refutes**, rather than proves, both unrestricted nonzero-total guarantees. Both negated universals use `Ω : Type` (universe zero), which contains the explicit finite examples.

## T13

This is a conjunction of two separately universally quantified results for every finite design and population.

1. If N>0, then for every label d with positivity, E H_d=T_d and

Var(H_d)=sum_i p_i(d)(1−p_i(d))[y_i(d)/p_i(d)]² + sum_{i≠j}[p_ij(d,d)−p_i(d)p_j(d)][y_i(d)/p_i(d)][y_j(d)/p_j(d)].

2. If N>0, then for every ordered pair of distinct labels d,e with positivity at both, E τhat_de=τ_de,

Var(τhat_de)=[Var(H_d)+Var(H_e)−2Cov(H_d,H_e)]/N²,

and Cov(H_d,H_e)=sum_{i≠j}[p_ij(d,e)−p_i(d)p_j(e)][y_i(d)/p_i(d)][y_j(e)/p_j(e)]−sum_i y_i(d)y_i(e).

Joint probabilities may vanish in both clauses; only the marginal probabilities occur as divisors.

## T14

For every finite design and population with N>0, and then every d satisfying positivity, the following conjunction holds: if p_ij(d,d)>0 for every i,j (including i=j), E v_d=Var(H_d); in all cases E v_d=Var(H_d)+A_d; and Var(H_d)≤E(v_d+a_d). All zero joint terms in v_d are the explicitly totalized terms described above, and a_d sums over exactly those impossible off-diagonal pairs. No sign assumption on outcomes or positivity of joint probabilities is imposed in the last two assertions.
