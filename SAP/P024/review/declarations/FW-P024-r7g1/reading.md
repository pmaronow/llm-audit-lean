# Blind reading

This file was written before opening `claims.json`, `record.json`, `earlier.json`, or `architect-report.md`. I read `closure.json`, the five Challenge declarations and their docstrings, and all source declarations in their closures. I also printed and read all 66 distinct generated auxiliary declarations in those closures; see `scratch/BlindClosure.lean` and `scratch/blind-closure-output.txt`. These auxiliaries supply numeral instances, nonzero finite-type sizes, positivity of cluster sizes, and nonemptiness of the finite sets used below. They introduce no statistical assumptions.

All probabilities below are ordinary finite sums: a `Design Ω` is a real mass function `a : Ω → ℝ` on a finite type, with `a(ω) ≥ 0` for every ω and `Σω a(ω) = 1`. Thus `E_a X = Σω a(ω) X(ω)`, `P_a(A) = Σω a(ω) 1_A(ω)`, and `Var_a X = Σω a(ω)(X(ω) − E_a X)²`. A uniform law on a nonempty finite type has mass `1 / |Ω|`. These are definitions by sums, not Bochner integrals. Every function used here has finite real values and is measurable for the finite discrete sigma algebra.

## SAP.P024.T1

Source: `SAP/P024/Challenge/Part1.lean:9–15`; statement: `SAP/P024/Defs/Part4.lean:10–32`. This is an unconditional conjunction about specified data, with universal quantifiers only inside the listed clauses. Its docstring calls it a counterexample to the necessity of a constant untreated path for design-unbiased estimation or sharp-null inference.

There are four dates, indexed by integers `t = 0,1,2,3`, and three equiprobable assignments `s = 0,1,2`. Assignment s starts exposure at calendar date s+2; the calendar date of index t is t+1. In symbols `z_s(t) = 1` iff `s+2 ≤ t+1`. The untreated and treated potential outcomes are fixed real functions `b_t = (t+1)²` and `c_t = b_t+2`. The eligible dates are the finite set `E = {1,2}` (calendar dates 2 and 3). Let `π_t = (1/3)Σs z_s(t)`.

The estimator called `calendarHT` is exactly

`H(s) = (1/2) Σ(t∈{1,2}) [if z_s(t)=1 then c_t/π_t else −b_t/(1−π_t)]`.

The finite-population effect on the eligible dates is `τ_E = (1/2)Σ(t∈{1,2})(c_t−b_t)`. The sharp-null before-after statistic uses b on both exposure states and all four dates:

`D(s) = Σ(t:z_s(t)=1)b_t/(3−s) − Σ(t:z_s(t)=0)b_t/(s+1)`.

For any statistic D on these three assignments, its inclusive upper-tail randomization value is `r(s) = #{u∈{0,1,2} : D(s) ≤ D(u)}/3`.

The conjunction says, in its source order:

1. For every date t, `π_t` equals the corresponding entry of `(0,1/3,2/3,1)`.
2. `b = (1,4,9,16)`; for every date t, c has corresponding entry `(3,6,11,18)`; and `b_0 ≠ b_1`.
3. `H(0)=69/4`, `H(1)=21/4`, `H(2)=−33/2`; `τ_E=2`; `E H=2`; and `Var H=1561/8`.
4. `D(0)=26/3`, `D(1)=10`, `D(2)=34/3`.
5. Applied to this D, `r(0)=1`, `r(1)=2/3`, `r(2)=1/3`.
6. For every integer k in `{0,1,2,3}`, `P(r(s) ≤ k/3)=k/3`.
7. For every real α, if `0≤α≤1`, then `P(r(s)≤α)≤α`.
8. `E H=τ_E`.

There are no free choices, omitted hypothesis binders, or existential witnesses hidden in the proposition: the assignment law, trend, effect and eligible set are fixed by the definitions.

Junk-value audit: division is total real division, so a zero denominator would give zero, but all denominators used in H are 1/3, 2/3 or 2, and the before-after arm sizes range from 1 to 3. Exposure probabilities 0 and 1 occur only at the two excluded dates. The uniform law and p-value divisor use the nonempty type `Fin 3`; the eligible set has two members. `averageEffect` and `htEstimate` would return zero on an empty eligible set, but no such set occurs. `Fin` numerals are modulo the type size in general; every index used here is within range. Counts are cast injectively from ℕ to ℝ. The annotated before-after subtraction is real subtraction and its operands make the denominator positive; there is no truncated-subtraction effect. There are no logarithms, roots, real powers, extended-real conversions, partial functions, infinite integrals, infima, suprema, limsups or liminfs.

## SAP.P024.T2

Source: `SAP/P024/Challenge/Part1.lean:17–20`; statement: `SAP/P024/Defs/Part4.lean:34–47`. This is the conjunction of two universally quantified results and four numerical/functional witness conclusions. The docstring describes overlap-based timing estimation, uniform sharp-null tests, and bias of the actual before-after statistic.

First, in binder order, for every finite type I of units/dates, every finite type Ω of assignments, every finite probability mass function a on Ω, every assignment function `z : Ω → I → Bool`, and every pair of fixed real potential-outcome functions `y0,y1 : I → ℝ`, define

`π_i = Σω a(ω) 1{z_ω(i)=true}` and `E = {i∈I : 0<π_i<1}`.

If E is nonempty, the conclusion is

`Σω a(ω) [ Σ(i∈E) (if z_ω(i) then y1_i/π_i else −y0_i/(1−π_i)) / |E| ] = Σ(i∈E)(y1_i−y0_i)/|E|`.

There are no independence, temporal ordering, common-probability, or constant-trend assumptions in this branch. The estimand concerns exactly the actual-overlap subset E.

Second, for every nonempty finite Ω, every real-valued statistic D on Ω, and every real α, if `0≤α≤1`, then, under uniform assignment,

`(1/|Ω|) Σω 1{ #{u∈Ω : D(ω)≤D(u)}/|Ω| ≤ α } ≤ α`.

This is an upper-tail, ties-included rank test for every fixed table of statistic values. In sharp-null use the fixed path supplies such a table; no stochastic outcome law is introduced by the statement.

Finally use the same four-date/three-onset construction as T1: `z_s(t)=1{s+2≤t+1}`, `b_t=(t+1)²`, `c_t=b_t+2`, and uniform s. Let `D(s)` be the mean of b on exposed dates minus its mean on unexposed dates, with arm sizes `3−s` and `s+1`. The observed outcome is `Y_s(t)=c_t` when exposed and `b_t` otherwise. Let `A(s)` use these observed outcomes in the same two group means. The remaining conclusions are `E D=10`, `E D≠0`, `∀s, A(s)=D(s)+2`, `E A=12`, and `E A≠2`.

Junk-value audit: the generic overlap hypothesis makes |E| positive and ensures all used π and 1−π denominators are positive. I may be empty syntactically, but then the nonempty-overlap hypothesis cannot hold; the theorem does have nonempty-overlap models. Ω cannot be empty if a `Design Ω` exists, since the empty sum cannot equal one. In the rank-test branch Ω is explicitly nonempty. The numerical witness has positive arm sizes. All sums are finite, with empty-sum value zero outside these nonempty hypotheses. Bool indicators and decidable finite-set filters have their literal meanings, with no partiality. Nat casts, Fin numerals, and real subtractions have the same harmless behavior as in T1. There are no infinite-domain or out-of-domain analytic operations.

## SAP.P024.T4

Source: `SAP/P024/Challenge/Part1.lean:22–29`; statement: `SAP/P024/Defs/Part5.lean:11–68`. This is an unconditional conjunction about a fixed sequence of finite populations and two assignment sequences. Its docstring says it refutes consistency based on a growing number of independently assigned clusters without a population-share condition.

For each natural k let `K=k+2`. A population consists of K clusters, each with a positive natural size `n_j` and real potential outcomes `y0_{ji},y1_{ji}` for individuals `i=0,…,n_j−1`. The cluster means are `b_j=Σi y0_{ji}/n_j` and `c_j=Σi y1_{ji}/n_j`. Its individual average effect is `τ=Σj n_j(c_j−b_j)/Σj n_j`, its cluster shares are `w_j=n_j/Σl n_l`, and its largest share is the maximum of those K real shares.

Here the population is fixed as follows: cluster 0 has `K²` individuals with `(y0,y1)=(1/2,3/4)`; each of the remaining K−1 singleton clusters has `(y0,y1)=(1/4,1/2)`. Given a treated subset s and an arbitrary real extension e on subsets, the estimator is e(s) if `s=∅` or s is all K clusters; otherwise it is the actual individual difference of observed means

`X_e(s) = Σ(j∈s)n_j c_j / Σ(j∈s)n_j − Σ(j∉s)n_j b_j / Σ(j∉s)n_j`.

Write `v(K,m,true)=1/4+(1/4)K²/(K²+m−1)` and `v(K,m,false)=1/4−(1/4)K²/(K²+K−m−1)`. All these expressions are real arithmetic. The proposition asserts:

1. For every k, total size is `K²+K−1`; for every k,j,i both potential outcomes are strictly between zero and one and their difference is 1/4; and for every k, `τ=1/4`.
2. For every k and treated subset s, if `s≠∅` and s is proper, `X_0(s)=v(K,|s|,1{0∈s})`, and `|X_0(s)−1/4| ≥ (1/4)K²/(K²+K−2) > 1/8`.
3. For every k, the uniform law on all `2^K` subsets has exactly the independent common-p Bernoulli masses at `p=1/2`: each s has mass `(Π(j∈s)1/2)(Π(j∉s)1/2)`. Its probability of two nonempty arms is `1−2/2^K`.
4. For every family of real extensions `e_k(s)`, for every k the probability under that full uniform law of `|X_{e_k}(s)−τ|>1/8` is at least `1−2/2^K`. As k tends to infinity these probabilities tend to one, and do not tend to zero. The extension quantifier precedes all three conclusions, so every extension is covered.
5. For every k the mean of `X_0` under the uniform law on all proper nonempty subsets is 1/4. This law is `conditionalNonemptyDesign`; its sample space contains exactly the two-arm assignments.
6. For every natural n put `K=2n+2`, choose uniformly a treated subset with exactly `m=n+1` clusters, and use the population with k=2n. Put `R_n=K²/(K²+n)`. The probability that cluster 0 is treated is 1/2. For every such subset the estimator is `1/4+(1/4)R_n` when cluster 0 is treated and `1/4−(1/4)R_n` otherwise. Its mean is 1/4, its variance is `R_n²/16`, `R_n>1/2`, and its probability of error greater than 1/8 is one.
7. `R_n→1`; the preceding complete-design variance tends to 1/16.
8. For every k the maximum cluster share is `K²/(K²+K−1)`, and it tends to one.
9. `v(6,3,true)=37/76` and `v(6,3,false)=1/76`. There are 20 three-treated subsets of six clusters, ten containing cluster 0; there are 64 subsets altogether. The full independent law's nonempty-arm probability is 62/64. Every size in the six-cluster population is 36 for cluster 0 and one otherwise. The half-treated six-cluster variance is 81/1444. Every proper nonempty six-cluster subset has absolute error at least 9/40, and there exists such a subset whose absolute error equals 9/40.

Quantifiers over k,n,j,i,s, and extensions occur separately within the corresponding conjuncts; no unmentioned asymptotic hypotheses are assumed. `Tendsto … atTop (nhds L)` is the ordinary real-sequence limit as the natural index tends to infinity. Non-convergence to zero is asserted explicitly for the independent error probabilities.

Junk-value audit: positive cluster sizes make each cluster mean defined; K≥2 makes the total population positive. Every two-arm subset has positive individual arm denominators. Empty-arm behavior is explicitly supplied by a user-quantified real function; it is not an implicit division-by-zero convention, and the asymptotic lower bound is uniform over it. The zero extension used in the pointwise and conditional clauses is never used on a sample with an empty arm. Uniform proper-subset laws are nonempty because `{0}` is a proper nonempty subset. The fixed-count subtype is nonempty because `0<n+1<2n+2`, so its cardinality/binomial divisor is positive. The finite maximum uses `Finset.sup'` with an actual nonempty proof, not an empty supremum or an arbitrary default. The rational formula denominators are positive in all applications (`1≤m≤K−1`, K≥2). Nat subtraction in the informal K−1 counts is harmless at K≥2; Lean's annotated displayed formulas use real subtraction. Powers have natural exponent two (or K on the positive real base two); no real-power domain convention occurs. No partial functions, extended-real conversions, infinite integrals, or limsup conventions occur.

## SAP.P024.T5

Source: `SAP/P024/Challenge/Part1.lean:31–44`; statement: `SAP/P024/Defs/WholeW1.lean:23–59`, including `SAP/P024/Defs/Part6.lean:11–27`. The statement combines a general consistency theorem and an equivalence with two specified witness families. The docstring describes a uniform outcome bound, a uniform treatment-probability margin, no dominant cluster, and both independent and complete assignment.

For each k, a population P_k has K=k+2 clusters of positive natural sizes n_{kj}, with fixed real potential outcomes for each individual. Define cluster means b_{kj},c_{kj} by the finite individual averages; total size `N_k=Σj n_{kj}`; individual effect `τ_k=Σj n_{kj}(c_{kj}−b_{kj})/N_k`; weights `w_{kj}=n_{kj}/N_k`; and `M_k=max_j w_{kj}`. For a proper nonempty treated set s the estimate is

`X_k(s)=Σ(j∈s)n_{kj}c_{kj}/Σ(j∈s)n_{kj} − Σ(j∉s)n_{kj}b_{kj}/Σ(j∉s)n_{kj}`.

On the two empty-arm subsets X_k instead equals an arbitrary real value e_k(s).

The first branch universally quantifies, in order: the population family P; a family d_k of probability laws on all subsets of the K clusters; a real sequence p_k; a family of empty-arm extension functions e_k; and two real constants B,η. The hypotheses, in order, are:

1. `B≥0` and `η>0`.
2. For every k,j,i, both `|y0_{kji}|≤B` and `|y1_{kji}|≤B`.
3. For every k, either every subset s has mass `p_k^{|s|}(1−p_k)^{K−|s|}` (the expression is actually products over the treated and untreated sets), or there exists a natural m with `0<m<K`, `p_k=m/K`, and mass `1 / choose(K,m)` for every size-m subset and zero for other subsets. The choice between these two laws may depend on k.
4. For every k, `η≤p_k≤1−η`, with the same η for the whole sequence.
5. `M_k→0`.

For every positive real ε, the conclusion is `Σs d_k(s) 1{|X_k(s)−τ_k|>ε}→0` as k→∞. The extension values need not be uniformly bounded; the potential outcomes must be. The outcome bound B and margin η are chosen before all indices k and before ε.

The second branch says for every population family P, `M_k→0` if and only if `Σj w_{kj}²→0`.

Next comes a specific 24-cluster population: cluster 0 has 46 individuals, each with potential outcomes (0,1); each other cluster has one individual with outcomes (0,0). The law is uniform on all subsets of exactly twelve clusters (the n=11 instance of the half-treated law). The statement asserts all individual potential outcomes belong to [0,1], the stated individual sizes, total size 69, `τ=2/3`, and, for every empty-arm extension, expected actual individual difference in means 23/57. It also asserts `23/57−2/3=−5/19` and the magnitude of this bias exceeds 1/4.

Finally it repeats an asymptotic counterexample with K=k+2: cluster 0 has K² individuals with outcomes (1/2,3/4), the K−1 other clusters are singletons with outcomes (1/4,1/2), and all subsets have uniform mass 2^(−K). For every k this is the product Bernoulli(1/2) law; for every k,j,i both outcome magnitudes are at most one; for every k the effect is 1/4; and the maximum population share tends to one. For every family e_k of empty-arm extensions, the probability that the estimate differs from its effect by more than 1/8 tends to one and does not tend to zero.

Junk-value audit: K≥2 and positive cluster sizes make all individual, cluster-mean and population denominators positive. `M_k` is a maximum of a nonempty finite set, supplied by a checked `sup'` nonemptiness proof. The full-law estimator is totalized by explicitly quantified empty-arm values; the consistency claim covers every such extension. In the complete branch the positive quota and its strict upper bound make the binomial divisor and both arms positive on the support; off-support extensions have mass zero. The common probability bounds imply p_k∈(0,1); they do not merely assert a vacuous numerical p condition unrelated to the actual law, because the full joint masses are fixed. The 24-cluster law has both arms nonempty on every sample, so its extension quantifier is harmless. An empty family of clusters is impossible here. All powers are integer powers or finite products. Counts and sizes use injective casts to real numbers, while the rate/limit statements use ordinary `Tendsto`, not a totalized limsup. There are no analytic-domain or integrability junk values.

## SAP.P024.T6

Source: `SAP/P024/Challenge/Part1.lean:46–66`; statement: `SAP/P024/Defs/WholeW2.lean:11–59`. This is the conjunction of four universal unbiasedness assertions. The docstring explicitly limits its scope to specified subclasses of equal-marginal individual assignment and excludes arbitrary dependent, varying-count laws.

For finite individuals J and fixed real potential outcomes `y0_j,y1_j`, the average effect is `τ=Σj(y1_j−y0_j)/|J|`. For any assignment z to individuals, the estimate is the observed treatment mean minus observed control mean:

`D(z)=Σ(j:z_j=true)y1_j / #{j:z_j=true} − Σ(j:z_j=false)y0_j / #{j:z_j=false}`.

This is `clusterDIM` specialized to unit sizes one, not a cluster-weighted estimand. Exposures depend only on assignment and individual identity; no random outcomes or cross-subject outcome dependence are included. The four assertions are:

1. In order: for every finite J and Ω, every probability mass function a on Ω, and every natural m, if `0<m<|J|`, then for every `z:Ω→J→Bool` and fixed `y0,y1:J→ℝ`, if (a) every assignment of nonzero mass has exactly m treated individuals and (b) every individual has actual probability `Σω a(ω)1{z_ω(j)=true}=m/|J|`, then `Σω a(ω)D(z_ω)=τ`. Constant counts are required only on the support; neither independence nor uniformity over size-m assignments is required.
2. For every natural N,m with `0<m<N`, every law d on subsets of `{0,…,N−1}` whose mass is `1/choose(N,m)` on size-m subsets and zero elsewhere, and every pair y0,y1 on these N individuals, `E_d D=τ`. The assignment for subset s treats exactly its members.
3. For every natural k, every real p with `0<p<1`, every law d on all subsets of K=k+2 individuals with exact product masses `d(s)=(Π(j∈s)p)(Π(j∉s)(1−p))`, and every fixed y0,y1, define A to be the proper nonempty subsets. Then `P_d(A)>0`; the finite sum `q=Σ(s∈A)(Π(j∈s)p)(Π(j∉s)(1−p))` equals `P_d(A)`; for every s∈A its conditional mass is `d(s)/P_d(A)`; and `Σ(s∈A)[d(s)/P_d(A)]D(s)=τ`. In the source the conditional mass is defined using q, and the equality identifies it with conditioning the supplied parent law d.
4. For every k and every finite law d on the type A of proper nonempty subsets of K=k+2 individuals, if `d(s)=d(t)` whenever `|s|=|t|`, then for every fixed y0,y1, `E_d D=τ`. Counts may vary; within each count stratum the full subset law must be uniform. Zero-probability strata are permitted.

There is no universal assertion for arbitrary equal-marginal dependent varying-count assignment. No uniform boundedness of outcome magnitudes is needed because each model is finite. The finite support laws, real-valued potential outcomes and ordinary group mean formula give the stated usual measurable/finite setting.

Junk-value audit: branches 1–2 have N≥2 and 1≤m≤N−1, so both arms and the population effect have positive denominators on the support. At a zero-mass sample the first two branches can have an empty arm, where Lean evaluates division by zero as zero; its contribution to the finite expectation is exactly zero and cannot change the assertion. Branch 3 asserts a strictly positive conditioning mass, and the raw conditional-mass definition is used only under 0<p<1, K≥2. Branch 4's sample type excludes empty arms. The raw definitions would otherwise divide by zero for p outside its stipulated range or for an empty conditioning event, but neither is used here. Binomial coefficients are positive at the quotas in branch 2. `treatedCount` is literally a filtered finite-set cardinality, and all casts into ℝ preserve that cardinality. Finite assignment laws on an empty Ω cannot exist, while the individual lower bounds preclude empty J. There are no default elements, partial function values, nonintegrable means, extended-real conversions, totalized order extrema, or analytic-domain conventions.
