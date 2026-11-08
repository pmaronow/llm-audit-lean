# Blind reading

Saved before opening `claims.json` or `record.json`. The sources read are the five target docstrings/statements and all their unit declarations listed in `closure.json`. `scratch/Inspect.lean` also prints the elaborated closure, including generated auxiliary proofs, constructors, projections, and the two-constructor bound-side eliminators. These helpers implement numerals, casts, finite-index bounds, and case distinctions; they add no statistical assumptions.

## SAP.P022.T11

Source: `SAP/P022/Challenge/Part1.lean:76–78`, `SAP/P022/Defs/Part1.lean:9–31`.

For real numbers, write `D(v,p)` for the closed interval condition `p-1/2000 ≤ v ≤ p+1/2000`. This is the complete unfolding of `DisplaysAs`; it allows either tie of a three-decimal display bin.

The first conjunct universally quantifies, in order, seven real numbers `Va,VH,z,L,U,LH,UH`. Assume `Va>0`, `VH>0`, `z>0`, and

* `D(L,-1.555)`, `D(U,0.192)`, `D(LH,-1.528)`, `D(UH,0.165)`;
* `(U-L)/2 = z sqrt(Va)` and `(UH-LH)/2 = z sqrt(VH)`.

Put `a=(U-L)/2`, `h=(UH-LH)/2`, and `r=100(1-VH/Va)`. The conclusion is the conjunction of:

1. `0.873 ≤ a ≤ 0.874`, `0.846 ≤ h ≤ 0.847`, and
   `r ≤ 100(1-(423/437)^2) = 1204000/190969`, with `r<6.5`;
2. **if additionally** `D(Va,0.199)` and `D(VH,0.186)`, then
   `2400/397 ≤ r ≤ 1204000/190969` and `5.5<r<6.5`.

The second, separate conjunct is the exact real arithmetic identity
`100(1-(0.186)/(0.199))=1300/199`.

The docstring describes closed rounding bins, a common positive Wald multiplier, endpoint-only upper bounds, the combined six-percent bounds, and the exact percentage for displayed inputs. The statement supplies no random data, experiment, or assertion that the displayed inputs are exact underlying variances.

Junk-value audit: every fixed denominator is nonzero; `Va` is strictly positive. Mathlib division is total with `x/0=0`, but that branch is excluded. `Real.sqrt` is zero on nonpositive inputs, but both variance inputs are positive here. There are no sums over potentially empty types, integrals, extrema, limits, natural subtraction, or partial-function defaults.

## SAP.P022.T12

Source: `SAP/P022/Challenge/Part1.lean:80–82`, `SAP/P022/Defs/Part6.lean:35–59`; dependent finite-experiment definitions are in `Defs/Part2.lean`.

A design consists of natural numbers `N,m,k` with `N≥4`, `m≥2`, `k≥2`, `m+k≤N`. An assignment is a permutation `π` of `{0,…,N-1}`, with uniform finite averaging over **all** `N!` permutations. Given a vector `y`, its treatment sample is `y(π(i))`, `0≤i<m`, and control sample is `y(π(m+j))`, `0≤j<k`. A finite mean is the sum divided by the cardinality. The design expectation is the sum over permutations divided by `N!`; a design variance is the average squared deviation from that mean.

For a sample vector `a` of length `s`, let `s²(a)=Σ_i(a_i-ā)²/(s-1)` and `M_N(a)=(N-1)s²(a)/N`. For real `v1,v0,cov`, the shared variance expression is
`[((N-m)/m)v1+((N-k)/k)v0+2cov]/(N-1)`, with all the subtractions in this expression performed in the reals.

For potential outcomes `y1,y0`, the estimated effect is the treatment mean of `y1` minus the control mean of `y0`, and the true variance is its uniform design variance. Given the two observed samples, let `A=M_N(treatment)`, `B=M_N(control)`. The upper Neyman estimator is the variance expression with inputs `A,B,sqrt(A B)` (the lower constructor, although not selected here, uses `-sqrt(A B)`). `BoundSide` is exactly the two-element type `H,L`; its generated equality and eliminators choose these branches.

The statement is a conjunction of six independent universal assertions:

1. For every design, proof `m+k=N`, and vector `y : Fin N → ℝ`, the design mean of the upper Neyman estimator with **both** potential-outcome vectors equal to `y` is at most the true design variance of their difference in observed means. This is a full-population, sharp-null assertion.
2. For every type `ι` in universe `u`, finite subset `s`, proof `s` is nonempty, function `v:ι→ℝ` nonnegative on `s`, and real `c`,
   `( |s|⁻¹ Σ_{i∈s} c sqrt(v_i) )² ≤ c² |s|⁻¹ Σ_{i∈s}v_i`.
3. For all real `c,q,d`, if `q≥391/2000`, `0≤d≤867/500`, and `d²=c²q`, then `c²≤44217/2875`.
4. For all real `c,w,M,V,b`, the hypotheses
   `c²≤44217/2875`, `M≥0`, `w≥3447/2000`, `w²≤c²M`,
   `V≤399/2000`, `b≤-13/2000`, and `M=V+b` imply `False`.
   This is deliberately a numerical incompatibility theorem, not an assertion that these numerical hypotheses coexist.
5. For all real `w,v`, if `w≥3447/2000` and `w²≤(98/25)²v`, then
   `v≥11881809/61465600` and `v>193/1000`.
6. For all real `V,b`, if `V≤399/2000` and `b≤-13/2000`, then `V+b≤193/1000`.

There is no explicit statement about 2000 Monte Carlo replications, their independence, or the probability of their reported sample means. The finite-set means in assertion 2 are abstract uniform means. Assertions 3–6 quantify scalar inputs without tying them to a particular experiment.

Junk-value audit: `N,m,k,N-1,m-1,k-1,N!` are positive, so all statistical divisions and finite averages have their ordinary meanings. The finite subset in assertion 2 is explicitly nonempty. Sample variances are nonnegative, as are `A,B`, so `sqrt(A B)` is within its usual domain; assertion 2 assumes each radicand nonnegative, including the legitimate zero case. Real subtraction is not truncated. No Bochner integrals, measure conversions, extrema, logarithms, powers with nonintegral exponents, or limsups occur. The contradiction in assertion 4 is the conclusion being established and is not an antecedent that silently empties a substantive theorem.

## SAP.P022.T2

Source: `SAP/P022/Challenge/Part1.lean:19–21`, `SAP/P022/Defs/Part5.lean:25–40`, and the closure in `Defs/Part2.lean` plus `Defs/Part3.lean:178`.

Universally quantify, in order, an experiment sequence `S`, joint probability law `H` on the Borel real plane, real `θ,ρ`, a proof of `Conditions123 S H θ ρ`, and a proof of `AtomLeftConvergence S H`.

An experiment sequence consists of a design at each natural index `q`, with `N_q=q+4`, and two fixed real sequences `y1,y0 : ℕ→ℝ`. Its row outcomes are the first `N_q` values of the relevant sequence. Thus populations are nested prefixes; arbitrary triangular arrays are not quantified. Every row has the design restrictions `m_q,k_q≥2`, `m_q+k_q≤N_q`, and uniform permutations and observed samples as described explicitly in the T12 section.

For `t=true` let `p_t` be the first coordinate, and for `t=false` the second. Set
`F_t(x)=H{p:p_t≤x}`, `F_t(x-)=H{p:p_t<x}`. The population CDF is
`F_{q,t}(x)=N_q⁻¹Σ_{i<N_q}1{y_t(i)≤x}`, and its left version uses `<`.
The sample CDF `Fhat_{q,true,π}` averages the indicators over the first `m_q` permuted treatment values, and `Fhat_{q,false,π}` over the next `k_q` permuted control values.

`Conditions123` is exactly:

* `0<θ≤1`, `0<ρ<1`;
* `m_q/N_q → θρ` and `(m_q+k_q)/N_q → θ`;
* for every bounded continuous real function `f` on `ℝ²`,
  `N_q⁻¹Σ_{i<N_q} f(y1(i),y0(i)) → ∫f dH`;
* for every `t,x` where the real function `F_t` is not continuous at `x`,
  `F_{q,t}(x)→F_t(x)`.

The added `AtomLeftConvergence` condition says, for every such `t,x`,
`N_q⁻¹Σ_{i<N_q}1{y_t(i)<x} → F_t(x-)`.

For functions `A,B:ℝ→ℝ`, the CDF distance is the real supremum
`d(A,B)=sup_{x∈ℝ}|A(x)-B(x)|`. For row events `E_q(π)`, the scaled tail functional is
`limsup_{q→∞} ofReal(N_q (N_q!)⁻¹Σ_π 1{E_q(π)})`, taken in the complete ordered set `[0,∞]`.

Define the single, explicit integer function `K(η)=2 ceil_nat(4/min(η,1))`, where `ceil_nat` is the least natural number above a nonnegative argument, and returns zero for a nonpositive argument. The conclusion is:

1. for every real `η>0`, `K(η)>0`;
2. for every real `0<a≤b`, `K(b)≤K(a)`;
3. for both `t`, `d(F_t,F_{q,t})→0`;
4. for every real `η>0`, both
   `limsup N_q P_q{d(F_true,Fhat_true)≥η} ≤ (1-θρ)K(η)/(θρ η²)` and
   `limsup N_q P_q{d(F_false,Fhat_false)≥η} ≤ (1-θ(1-ρ))K(η)/(θ(1-ρ)η²)`.
   Right sides are embedded into `[0,∞]` using `ENNReal.ofReal`.

The same integer function serves both arms and all sequences and laws. The inequalities use `≥η`, not strict tails.

Junk-value audit: finite populations and samples are nonempty, and permutation types contain the identity. All CDF values lie in `[0,1]`, so the real supremum has a nonempty, bounded range and cannot invoke the default value of an empty/unbounded real supremum (zero in Mathlib). The joint law is a probability measure, so all sets used for CDFs have mass at most one and `toReal(∞)=0` is never reached. The weak-convergence integrands are bounded continuous and hence integrable for `H`. Denominators `θρ η²` and `θ(1-ρ)η²` are strictly positive in the tail assertions, and `min(η,1)>0` wherever `K` is constrained; its other totalized values have no bearing on the conclusion. `ENNReal.ofReal` truncates negative real numbers to zero, but all converted probabilities and rate bounds here are nonnegative. The limsup is in `ℝ≥0∞`, so divergence is faithfully represented by `∞`, with no unbounded-real-limsup default. `N_q=q+4` is natural addition with no overflow. Index proofs ensure sample accesses are in range. No noninteger powers, logarithms, square roots, or partial-function defaults affect this statement.

## SAP.P022.T18

Source: `SAP/P022/Challenge/Part1.lean:112–114`, `SAP/P022/Defs/Part6.lean:154–157`, `SAP/P022/Defs/Part3.lean:13–26`, and `Defs/Part2.lean`.

There exist, in order, an experiment sequence `S`, joint probability law `H` on `ℝ²`, and real `θ,ρ` such that `Conditions123 S H θ ρ` holds and `Lemma2Conclusions S H θ ρ` does not hold.

Unfolding the setting: `S` is two fixed sequences of real numbers and row designs with `N_q=q+4≥4`, `m_q,k_q≥2`, `m_q+k_q≤N_q`. Population outcomes are prefixes. Assignments are all permutations of the `N_q` indices with uniform weights; treatment uses the first `m_q` and control the next `k_q` entries. Real finite means are sums divided by cardinality. The joint law is a Borel probability measure. Its marginal CDFs are `F_t(x)=H{p:p_t≤x}`. Population and sampled CDFs are normalized indicator sums; CDF distance is `sup_x|A(x)-B(x)|`.

The required conditions are `0<θ≤1`, `0<ρ<1`, `m_q/N_q→θρ`, `(m_q+k_q)/N_q→θ`, joint empirical convergence against every bounded continuous function, and convergence `F_{q,t}(x)→F_t(x)` at every discontinuity `x` of each limiting marginal CDF. No left-limit-at-atoms condition is assumed.

The negated proposition is the conjunction of:

1. for each arm `t`, `sup_x|F_t(x)-F_{q,t}(x)|→0`;
2. there exist two functions `K1,K0:ℝ→ℕ`, chosen **after** `S,H,θ,ρ`, positive at every positive argument, with `K1(b)≤K1(a)` and `K0(b)≤K0(a)` whenever `0<a≤b`, such that for every `η>0`,
   `limsup_q N_q P_q{d(F_true,Fhat_true)≥η} ≤ (1-θρ)K1(η)/(θρ η²)` and
   `limsup_q N_q P_q{d(F_false,Fhat_false)≥η} ≤ (1-θ(1-ρ))K0(η)/(θ(1-ρ)η²)`.

The probabilities are uniform averages over row permutations. Limsups and rate bounds are in `[0,∞]`, using `ENNReal.ofReal` on each real expression. The existential theorem needs failure of at least one part of this joint conclusion; it does not separately assert failure of both parts or present a specific witness in its statement. Its docstring calls this a refutation of printed Lemma 2.

Junk-value audit: the same positivity, nonempty-type, integrability, bounded-supremum, probability-mass, and extended-limsup checks stated explicitly for T2 apply here to every candidate `S,H,θ,ρ` satisfying the existential conjunction. In particular, all CDF distances are suprema of nonempty ranges in `[0,1]`; all `toReal` conversions are of masses at most one; bounded continuous tests are integrable; denominators in tail clauses are positive; and `ofReal` cannot conceal a negative rate bound. There are no quantiles, square roots, partial functions, or natural subtractions in this closure. No junk-value defect is apparent from the blind reading. Whether the existential counterexample contradicts the intended printed claim remains to be checked against its exact assumptions in step 2.

## SAP.P022.T3

Source: `SAP/P022/Challenge/Part1.lean:23–25`, `SAP/P022/Defs/Part5.lean:42–75`, and the relevant closures in `Defs/Part2.lean` and `Defs/Part3.lean:46–47`.

A design is natural `N,m,k` with `N≥4`, `m,k≥2`, `m+k≤N`. A design expectation or probability is the uniform finite mean over all permutations of the `N` indices; a probability is the mean of a zero/one event indicator. Observed treatment outcomes are `y1(π(i))` for `i<m`, and observed control outcomes are `y0(π(m+j))` for `j<k`.

For a nonempty real vector `v` of length `s`, let `μ(v)=Σv_i/s`, `V(v)=Σ(v_i-μ(v))²/s`, and `s²(v)=Σ(v_i-μ(v))²/(s-1)`. Sort `v` increasingly using list merge-sort. Define its rank statistic at natural `r` by the list entry with zero-based index `r-1`, using truncated natural subtraction and returning zero if that index is out of bounds. Its empirical quantile is that rank statistic at `ceil_nat(su)`.

For two vectors `a,b`, let
`C_H(a,b)=∫_0^1 Q_a(u)Q_b(u) du-μ(a)μ(b)`, and
`C_L(a,b)=∫_0^1 Q_a(u)Q_b(1-u) du-μ(a)μ(b)`.
These are ordinary real Lebesgue interval integrals. For `B∈{H,L}`, set
`W_B(y1,y0)=[((N-m)/m)V(y1)+((N-k)/k)V(y0)+2C_B(y1,y0)]/(N-1)`.
For the two observed sample vectors `a,b`, put `M_N(a)=(N-1)s²(a)/N` and define
`What_B(π)=[((N-m)/m)M_N(a)+((N-k)/k)M_N(b)+2C_B(a,b)]/(N-1)`.
These unfold `populationBound`, `estimatedVariance`, `estimateBound`, `marginalVarianceEstimate`, `varianceExpression`, and `sharpCovariance` completely.

For a bound `C`, let `F_v(x)=Σ_i1{v_i≤x}/|v|` and
`D1(π)=∫_{-C}^C |F_a(x)-F_y1(x)| dx`,
`D0(π)=∫_{-C}^C |F_b(x)-F_y0(x)| dx`.

The **finite** conjunct universally quantifies a design, real vectors `y1,y0:Fin N→ℝ`, and real `C,c`, then assumes `C≥0`, `|y1_i|≤C` and `|y0_i|≤C` for every `i`, `c>0`, `cN≤m`, `cN≤k`, and `2/c≤N`. It concludes all of:

* `E D1² ≤ C²(N-m)/((N-1)m) ≤ C²/(cN)`;
* `E D0² ≤ C²(N-k)/((N-1)k) ≤ C²/(cN)`;
* `E(D1+D0)² ≤ 4C²/(cN)`;
* for every bound side `B` and assignment `π`,
  `N|What_B(π)-W_B| ≤ (16/c+8) C(D1(π)+D0(π))+8C²/(c²N)`;
* for every real `ε>0` satisfying `16C²/(c²ε)≤N` and every `B`,
  `P{N|What_B-W_B|≥ε} ≤ 16(16/c+8)² C⁴/(cNε²)`.

The **asymptotic** conjunct independently universally quantifies an experiment sequence `S` (fixed potential-outcome sequences, row size `N_q=q+4`, row designs as above), real `θ,ρ,C`, and assumes `0<θ≤1`, `0<ρ<1`, `m_q/N_q→θρ`, `(m_q+k_q)/N_q→θ`, `C≥0`, and both fixed outcome sequences bounded in absolute value by `C`. It then quantifies real `ε,c` with `ε>0`, `c>0`, and `c<min(θρ,θ(1-ρ))`, followed by `B`, and concludes
`limsup_q N_q P_q{N_q|What_{q,B}-W_{q,B}|≥ε} ≤ 16(16/c+8)² C⁴/(cε²)`.
The limsup and right side are represented in `[0,∞]` through `ENNReal.ofReal`. This conjunct requires no limiting joint outcome law, convergence of empirical distributions, or moment-growth assumption beyond the given bounded outcomes and allocation limits.

Junk-value audit: all means and sample denominators are well-defined by `N≥4`, `m,k≥2`. Real `c` and positive tolerance `ε` prevent zero denominators; `N-m`, `N-k`, and `N-1` in variance formulas are real differences. In `orderStatistic`, natural `r-1` truncates at zero: rank zero returns the smallest element for nonempty vectors. Thus `Q(0)` is the smallest element rather than an infinite endpoint; at `u∈(0,1]`, ranks are valid, and at `u=1` the largest element is selected. Outside `[0,1]` negative `u` also selects the minimum, while an excessive positive rank can return the default zero. The covariance integrals only use arguments in `[0,1]` and changing the values at the two endpoints has no effect on the Lebesgue integral. Sample/population vectors are nonempty. Their quantile functions are bounded measurable finite step functions, so the Bochner integral's nonintegrability-default-zero branch cannot be used. Empirical CDF errors are bounded measurable step functions on the finite interval `[-C,C]`; at `C=0` the integral and bounds genuinely vanish. Sorting preserves list length and neither access to observed samples nor any relevant interior quantile access is out of range. All converted rates and probabilities are nonnegative. The limsup uses the complete lattice `ℝ≥0∞`, so it handles divergence without a real-valued default. No real logarithm, square root, or nonintegral power occurs in this closure. Generated auxiliary proofs of numeral classes and finite-index inequalities carry no extra mathematical condition.
