# Blind reading of P022-T13 through P022-T17

This file was written before opening `claims.json` or `record.json`. The source
statements, docstrings, and every entry of the five lists in `closure.json` were
read. Auxiliary declarations with line zero were inspected with `#print` in
`scratch/BlindPrint.lean`. No Solution or other review was consulted.

## Shared mathematical notation, fully unfolding the SAP definitions

The following expansions apply in each of the five sections below; the sections
specify which of them occur in that declaration.

* A **design** is a triple of natural numbers `(N,m,k)` with proofs of
  `N >= 4`, `m >= 2`, `k >= 2`, and `m+k <= N`. An **assignment** is a
  permutation of `{0,...,N-1}`. Its law is uniform over all `N!` permutations.
  Treatment consists of the first `m` permuted units, control of the next `k`,
  and the remaining units are unsampled. Thus the observed vectors are
  `a_i=y1[pi(i)]` and `b_j=y0[pi(m+j)]`.
* For a vector `v` of length `s`, write `mu(v) = (sum_i v_i)/s`,
  `vpop(v) = (sum_i (v_i-mu(v))^2)/s`, and
  `cpop(v,w) = (sum_i (v_i-mu(v))(w_i-mu(w)))/s` for equal lengths.
  These are `finiteMean`, `finiteVariance`, and `finiteCovariance`; the
  mean notation is Mathlib's finite arithmetic average, not an integral.
  `designExpectation` is the analogous average over all permutations;
  `designProbability(E)` is the average of `1_E`, and `designVariance(X)`
  is the average of `(X-average(X))^2`.
* `averageEffect` is `tau=mu(y1)-mu(y0)`;
  `estimatedEffect(pi)` is `T(pi)=mu(a)-mu(b)`;
  `trueVariance` is `V=Var_pi(T)`.
  Define
  `F(N,m,k;A,C,D) = (((N-m)/m) A + ((N-k)/k) C + 2 D)/(N-1)`.
  This is `varianceExpression`; every subtraction displayed here except the
  order-statistic index below takes place in the real numbers.
* `empiricalCDF(v)(x) = #{i:v_i<=x}/s`. Sort the list of entries ascending
  using Mathlib `List.mergeSort`; `sortedOutcomes` is that list and
  `sortedValues(v)_i` is its zero-based entry `i`. `orderStatistic(v,r)` is
  list entry `r-1`, using natural truncated subtraction and default zero for
  an out-of-range entry. `empiricalQuantile(v,u)=Q_v(u)` uses
  `r=Nat.ceil(s*u)` (natural-valued ceiling).
* `BoundSide` has exactly the constructors `H` and `L`. Put `r_H(u)=u` and
  `r_L(u)=1-u`. Then
  `D_B(v,w)=integral_0^1 Q_v(u) Q_w(r_B(u)) du - mu(v)mu(w)`.
  This is `sharpCovariance`. The integral is the Mathlib real Bochner interval
  integral with respect to Lebesgue measure. Define the population endpoint
  `B_B = F(N,m,k;vpop(y1),vpop(y0),D_B(y1,y0))`;
  this is `populationBound`.
* `sampleVariance(v)=s2(v)=(sum_i (v_i-mu(v))^2)/(s-1)`, and
  `marginalVarianceEstimate(N,v)=A_N(v)=((N-1)/N)s2(v)`.
  `estimateBound(N,a,b,B)=F(N,m,k;A_N(a),A_N(b),D_B(a,b))`, with
  `m=length(a), k=length(b)`. `estimatedVariance(...,B,pi)=hatB_B(pi)`
  applies that formula to the observed treatment/control vectors.
  `neymanEstimate(...,B,pi)` instead uses covariance
  `+sqrt(A_N(a)A_N(b))` for `H` and its negative for `L`.
  `conventionalEstimate = N/(N-1) * (A_N(a)/m + A_N(b)/k)`.
* An **experiment sequence** `S` consists of a design `d_q` for every natural
  `q`, the equality `N_q=q+4` for every `q`, and two fixed infinite real
  sequences `y1_i,y0_i`. Each row uses their first `N_q` entries
  (`rowOutcomes`). These are nested populations, not arbitrary triangular
  arrays. `JointLaw` is a Borel probability measure on `R^2`.
  `lawCDF(H,t,x)` is `H{p:p_t<=x}`, converted from extended nonnegative
  reals to reals, where `p_true=p.1`, `p_false=p.2`.
* `weakPopulationConvergence(S,H)` means that for every bounded continuous
  real function `f` on `R^2`, the row average of `f(y1_i,y0_i)` converges to
  its integral against `H`. `Conditions123(S,H,theta,rho)` is the conjunction
  `0<theta<=1`, `0<rho<1`, `m_q/N_q -> theta*rho`,
  `(m_q+k_q)/N_q -> theta`, the preceding weak convergence, and, for every
  arm and every discontinuity `x` of its limiting marginal CDF, convergence
  of the empirical marginal CDF at that same `x` to the limiting CDF there.
* `UniformSquareIntegrability(S)` means, for each arm, that
  `sup_q N_q^(-1) sum_{i<N_q} y_ti^2 1_{beta<=y_ti^2} -> 0` as the real
  cutoff `beta -> +infinity`, AND that the set whose real supremum is used
  is bounded above for every real cutoff. `BoundedThirdMoments(S)` means
  `exists M in R, forall q,t, N_q^(-1) sum_{i<N_q} |y_ti|^3 <= M`.
* `lawMean(H,t)=int p_t dH`,
  `lawVariance(H,t)=int (p_t-lawMean(H,t))^2 dH`, and
  `lawCovariance(H)=int (p.1-lawMean(H,true))(p.2-lawMean(H,false)) dH`.
  `compatibleLaws(H)` is the set of Borel probability laws with both marginal
  CDFs identical to those of `H`. `empiricalCompatibleLaws(y1,y0)` instead
  requires both CDFs to equal the two empirical CDFs.
* Write `c_H^max=sSup{lawCovariance(J):J in compatibleLaws(H)}` and similarly
  `c_H^min=sInf(...)`. Then
  `b_B(H,theta,rho)=((1-theta*rho)/(theta*rho))*lawVariance(H,true)
  +((1-theta*(1-rho))/(theta*(1-rho)))*lawVariance(H,false)
  +2*(c_H^max if B=H else c_H^min)` is `limitingBound`.
  Replacing the extremal covariance by `lawCovariance(H)` gives
  `s(H,theta,rho)=limitingTrueVariance`. `gamma=s/b_H`.
* `boundConsistency(S)` means: for every real `epsilon>0`, the probability
  that `max(N_q*|hatB_H-B_H|, N_q*|hatB_L-B_L|) >= epsilon`
  tends to zero. `scaledProbabilityLimsup(S,E)` is the limsup in the complete
  lattice `[0,infinity]` of `ENNReal.ofReal(N_q*P_pi(E_q))`.
* `NonsingularLaw(H)` means no nonzero pair `(a,b)` and real `c` satisfies
  `a*p.1+b*p.2=c` almost surely. `LawFunctionalsDefined(H)` asserts, for
  EVERY compatible law, integrability of each coordinate, its square, its
  centered square, and the centered cross product; it also asserts that the
  set of compatible covariances is nonempty, bounded above and bounded below.
  `LawThirdMomentsFinite(H)` asserts integrability of both absolute cubes.
* `normalCDF=Phi` is the CDF of Mathlib `gaussianReal 0 1`, converted to real.
  `normalCritical(alpha)=z_alpha` is the real infimum of
  `{x:1-alpha/2<=Phi(x)}`. `weakStandardNormal(S,Z)` means convergence of
  `E_pi f(Z_q)` to the standard Gaussian integral for EVERY bounded continuous
  real `f`. `designConvergence(d,X,a)` means for EVERY `eta>0`,
  `P_pi(eta<=|X_q-a|)->0`.
* `rowSize=N_q`, `rowTrueVariance=V_q`, `rowBound(S,B,q)=B_B,q`,
  `rowEstimate(S,B,q,pi)=hatB_B,q(pi)`, and `effectError=T_q-tau_q`.
  For an arbitrary real assignment-dependent input `W_q(pi)`,
  `waldCoverage(S,W,alpha,q)=P_pi(|T_q-tau_q|<=z_alpha*sqrt(W_q(pi)))`.
  `gaussianWaldCoverage(alpha,v,s)=2 Phi(z_alpha*sqrt(v/s))-1`.

Generated closure declarations are also accounted for: `Design.mk` and its
numeric projections and `ExperimentSequence.mk` and its projections are the
ordinary structure constructors/projections above. `BoundSide.rec`, `casesOn`,
`ctorIdx` (0 for H, 1 for L), and the derived equality decision and its two
proofs implement only this two-case type. `finiteMean._proof_1` supplies
`CharZero R`; `observedTreatment._proof_2` and `observedControl._proof_2`
prove the subscripts are less than N. `varianceExpression._proof_1`,
`cellMidpoint._proof_1`, and `bernoulliHalfCDF._proof_1` certify that numeral
2 has at least two values. `NonsingularLaw._proof_1` supplies the ordinary
outer-measure instance for a measure. The last two unrelated-looking auxiliary
numeral proofs are shared elaborator constants, not dependencies on the
mathematics of midpoint quadrature or a Bernoulli example.

## SAP.P022.T13

Source: `Challenge/Part1.lean:84-86`, `Defs/Part6.lean:61-88`.
Universally quantify a design `d`, then any two real vectors `y1,y0` of length N.
There are no hypotheses except the design's four numeric requirements. The
conclusion is the conjunction of:

1. `E_pi T=tau`, and `V=F(N,m,k;vpop(y1),vpop(y0),cpop(y1,y0))`.
2. For EVERY pair of vectors `z1,z0` of length N, IF each list of entries is a
   permutation (including multiplicities) of its corresponding original list,
   THEN `D_L<=cpop(z1,z0)<=D_H` AND `B_L<=Var_pi(T(z1,z0))<=B_H`.
3. Sorting both original vectors ascending attains variance `B_H`; sorting
   `y1` ascending and `y0` descending (the `Fin.rev` index `N-1-i`) attains
   variance `B_L`.
4. For EVERY probability law J whose marginals are the original empirical
   marginals, the raw product is integrable and its centered covariance lies
   in `[D_L,D_H]`.
5. For EACH side B there EXISTS such a law J whose covariance equals `D_B`,
   and for EVERY bounded continuous f on `R^2`, its J-integral equals
   `int_0^1 f(Q_y1(u),Q_y0(r_B(u))) du`.

The docstring describes unbiasedness, the exact variance, and boundedness and
attainment of the covariance/variance endpoints over rearrangements and couplings.
For general probability couplings the displayed variance functional is implicit
through the affine covariance formula; the formal conclusion directly states
their covariance bounds, not a new finite-population assignment construction.

Junk audit: N,m,k,N-1 are positive. All means are finite sums over nonempty
finite sets, and the permutation set contains the identity. Sorting preserves
length, so the zero default in `sortedValues` is unreachable. Quantile rank zero
at u=0 uses truncated `0-1=0`, hence selects the minimum rather than an infinite
generalized inverse; out-of-range ranks default to zero outside the unit
interval. On `(0,1]` ranks are valid, and endpoints do not affect these Lebesgue
integrals or the coupling identity. Quantiles here are bounded step functions,
so Bochner-integral fallback to zero is irrelevant. Compatible laws have finite
support in the product of the finite marginal supports, so all coordinate
moments and products exist and their CDF `toReal` never encounters infinity.
No extrema or limsup are used. No logarithm or real power occurs.

## SAP.P022.T14

Source: `Challenge/Part1.lean:88-90`, `Defs/Part6.lean:90-97`.
For EVERY design d, THEN a proof `m+k=N`, THEN ANY two length-N real vectors,
THEN EVERY permutation pi, the conclusion is the four simultaneous inequalities

`Neyman_L(pi) <= hatB_L(pi) <= hatB_H(pi) <= Neyman_H(pi)
 <= N/(N-1)*(A_N(a)/m+A_N(b)/k)`.

All five estimators are precisely the formulas in the shared expansion, including
the `(N-1)/N` correction inside each marginal variance estimate. The statement
is deterministic for each assignment. It assumes complete sampling, with both
arms having at least two units. It says nothing about partial sampling.
The docstring accurately describes that complete-sampling ordering.

Junk audit: m,k,N,N-1,m-1,k-1 are all positive, so no division-by-zero default
occurs. The square-root argument is `A_N(a)A_N(b)>=0`; zero is legitimate
for constant observed vectors and the ordinary square root is zero. In
particular, this use of sqrt does not assume positive marginal variance.
Quantile endpoint/truncated-index/default conventions are exactly those audited
for T13, with positive sample sizes m,k instead of N; they have no effect on
the integrals. All finite averages and step-function integrals exist. There
are no CDF measure conversions, extrema, or asymptotic filters in this target.

## SAP.P022.T15

Source: `Challenge/Part1.lean:92-94`, `Defs/Part6.lean:99-110`.
For EVERY experiment sequence S, probability law H, and real theta,rho, IF
`Conditions123(S,H,theta,rho)` AND `UniformSquareIntegrability(S)`, THEN:

1. For EVERY compatible probability law J, EVERY arm t, and EVERY natural
   exponent j<=2, the coordinate power `p_t^j` is integrable against J.
2. For EVERY compatible J the raw product `p.1*p.2` is integrable.
3. For EVERY side B, `N_q B_B,q -> b_B(H,theta,rho)` in real numbers.
4. For EVERY positive epsilon the joint upper/lower scaled estimation-error
   probability in the shared definition of `boundConsistency` tends to zero.

Thus the conclusions give both deterministic endpoint limits and joint
consistency at the `1/N` scale, not only unscaled consistency. The docstring
calls the premises conditions 1-4; condition 4 here is exactly uniform square
integrability. The experiments use all sizes N>=4 and fixed nested outcomes.

Junk audit: all finite divisions and quantile conventions are harmless for
the same reasons as T13/T14. The two allocation denominators theta*rho and
theta*(1-rho) are strictly positive. The set of compatible laws contains H,
so is nonempty. Real extrema would be meaningless as extrema on unbounded
sets, but the stated square-integrability premise and weak convergence imply
finite limiting marginal second moments and bounded covariances by
Cauchy-Schwarz; this prevents that pathology. Unlike an unguarded real supremum,
the supremum in uniform square integrability has an explicit bounded-above
condition for every cutoff and a nonempty range (q ranges over naturals).
Bounded continuous tests are integrable under probability laws. The theorem
concludes actual integrability of coordinate powers and products; there is
no use of nonintegrable Bochner integrals to replace these quantities by zero.
The exponent is a NATURAL power, including j=0 (constant one, also at a zero
coordinate), not `Real.rpow`. All measures involved are probabilities and
CDF conversions never use `toReal(infinity)`. No limsup is used here.

## SAP.P022.T16

Source: `Challenge/Part1.lean:96-98`, `Defs/Part6.lean:112-126`.
For EVERY law H, real theta,rho,C and proof `C>=0`, there EXIST THREE
real-valued functions `kappa1,kappa2,kappa3` on R. They are nonnegative at
every positive argument. These choices may depend on H,theta,rho AND C.
They precede the quantification over S, so cannot depend on S. No continuity,
positivity, monotonicity, or explicit formula is required of these functions.

For EVERY experiment sequence S satisfying conditions 1-3 with the selected
H,theta,rho AND `forall i, |y1_i|<=C and |y0_i|<=C`, for EVERY real
epsilon,epsilon1,epsilon2,epsilon3 with all three split tolerances strictly
positive and their sum epsilon, the following BOTH hold:

`limsup_q N_q P_pi(epsilon <= N_q |hatB_H,q(pi)-B_H,q|)
 <= C^4 kappa1(epsilon1)`,

`limsup_q N_q P_pi(epsilon <= N_q |hatB_L,q(pi)-B_L,q|)
 <= C^4 (1/epsilon1^2+kappa2(epsilon2)+kappa3(epsilon3))`.

Each limsup and comparison is in `[0,infinity]`; the finite right-hand real
number is embedded using `ENNReal.ofReal`. The upper event is centered at the
SHARP UPPER POPULATION BOUND, not at the actual randomization variance. The
lower event is centered at its corresponding lower population bound. The
docstring describes both bounds uniformly over S with common H and allocation.

Junk audit: the ENNReal limsup retains infinity for unbounded scaled
probabilities, rather than silently using a real conditional supremum. The
right sides are finite and nonnegative (all kappa evaluations here are
nonnegative), so `ofReal` does not truncate a negative number. The split
epsilon1 is positive, avoiding reciprocal division by zero; epsilon is
automatically positive. C=0 is permitted and forces both infinite outcome
sequences identically zero, giving actual zero errors. Invalid theta,rho or
unrealizable H make the later S-premise impossible for that parameter choice,
but ordinary valid parameter choices are available; this is not by itself a
vacuity defect. The remaining finite sums, quantiles, integrations, casts,
and all integer subtractions are as audited for T13/T14. Law CDFs in the
premises are finite. No law covariance extremum occurs in this target.

## SAP.P022.T17

Source: `Challenge/Part1.lean:100-110`, `Defs/WholeW1.lean:425-501`.
This target uses `T17WholeStatement`, NOT the older `T17Statement` in Part6.
It is a conjunction of the following universally quantified assertions.

For EVERY S,H,theta,rho satisfying conditions 1-3, bounded empirical absolute
third moments, and no almost-sure affine relation under H:

1. `0<gamma<=1`, `N_q V_q -> s(H,theta,rho)`, and
   `(T_q-tau_q)/sqrt(gamma*hatB_H,q)` converges weakly to N(0,1), using
   the bounded-continuous-test definition. For EVERY `0<alpha<1`, the
   coverage of the Wald interval based on `hatB_H` converges to
   `2 Phi(z_alpha/sqrt(gamma))-1`, and that real number is at least `1-alpha`.
2. `LawFunctionalsDefined(H)` and `LawThirdMomentsFinite(H)` hold;
   `0<s(H,theta,rho)<=b_H(H,theta,rho)`; and `N_q B_H,q -> b_H`.
   Thus the existence of limiting moments/extrema is a conclusion.
3. For EVERY assignment-dependent real input W and real v, IF W is
   nonnegative at every row/assignment, `v>=0`, and `N_q W_q -> v` in design
   probability, THEN for EVERY `0<alpha<1`, its Wald coverage converges to
   `2 Phi(z_alpha*sqrt(v/s(H,theta,rho)))-1`.
4. For EVERY `v>=0`, `AssuredLeadingVariance(H,theta,rho,v)` is EQUIVALENT
   to `b_H(H,theta,rho)<=v`.
5. For EVERY `0<=v<b_H`, there EXIST a compatible probability law J and a
   nested experiment sequence R, with conditions 1-3 at J and the same
   theta,rho, bounded empirical third moments, nonsingular J, and
   `v<s(J,theta,rho)`. For EVERY nonnegative input W whose `N_q W_q`
   converges in design probability to v, and EVERY `0<alpha<1`, its coverage
   converges to `2 Phi(z_alpha*sqrt(v/s(J,theta,rho)))-1 < 1-alpha`.

The definition in item 4 expands as: v is nonnegative AND for EVERY compatible
law J, EVERY nested R satisfying conditions 1-3, bounded empirical third moments
and nonsingularity at J, EVERY nonnegative W consistent for leading variance v,
and EVERY `0<alpha<1`, there EXISTS a real c such that coverage converges to c
and `c>=1-alpha`. This is uniform assurance over joint laws and realizing
sequences, within the specified class of nonnegative Wald inputs with a
deterministic leading limit and fixed Gaussian critical value.

The docstring says that the core corollary follows without assuming positivity
of every finite estimate, that the upper endpoint is the least assuring leading
variance input in this class, and that every smaller input has a nonsingular,
realizable countermodel. The witnesses in item 5 are countermodels to smaller
inputs, not a declaration that the canonical corollary itself is false.

Junk audit: gamma's denominator and both limiting allocation denominators are
positive under the actual premises and conclusions; finiteness and bounded
extrema follow from the moment premises and are also explicitly concluded.
For the studentized statistic some finite estimates can be zero: real division
by zero gives zero; `Real.sqrt` also gives zero for a nonpositive argument.
The statement deliberately defines these exceptional statistics by those total
operations rather than requiring all finite estimates to be positive. The
positive limiting scale and consistency are needed to make such exceptional
events asymptotically negligible; otherwise this convention would affect the
normal-limit meaning. Nonnegative arbitrary W may equal zero, including v=0;
then a zero-width interval is literal and the asserted Gaussian coverage is
zero. Its limiting denominator s is strictly positive. For `0<alpha<1` the
normal CDF is a genuine probability CDF and the defining set for z_alpha is
nonempty and bounded below, so its real infimum is the usual finite positive
Gaussian quantile. The measure conversions cannot encounter infinity.
All other Bochner integrals, finite nonempty means, quantile defaults,
natural/real casts, and sorting bounds are as audited above. No `Real.log`,
`Real.rpow`, or conditional real limsup appears. The only actual uses of
unbounded-order conventions are guarded real covariance extrema and the
normal quantile infimum; neither takes an empty or unbounded-below defining
set in the admissible cases.
