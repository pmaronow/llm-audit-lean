# Blind reading

Saved before opening either `claims.json` or `record.json`. Sources read: the five
Challenge docstrings and statements; every declaration in their computed closures
in `closure.json`; the corresponding Defs sources; and Mathlib's definitions of
variance, covariance, event conditioning, Bernoulli measures, and Gaussian
measures. `scratch/BlindChecks.lean` compiled successfully and prints all 103
distinct closure declarations, including every listed generated proof constant.
The generated constants prove numeral facts, positivity/normalization, or
`2 ≤ M → 0 < M`; they add no mathematical hypothesis. Its output is retained in
`scratch/BlindChecks.out`.

## SAP.P027b.T14

### Objects, definitions, and quantifiers

There are no outer hypotheses. The conclusion is a conjunction of fixed finite
equalities and two universally quantified implications about Gaussian populations.

The finite probability design used throughout has population
`U = Fin M × Fin 2` and sample space `Ω = Fin M × Fin M`, where `Fin M` is the set
of natural numbers less than M. For positive natural M, every ordered pair
ω = (i,j) has real probability 1/M². It selects exactly (i,0) and (j,1).
Thus the stratum draws are independent and uniform. More generally a `Design`
is a finite type of units, a finite type of samples, nonnegative real weights
summing to one, and a Boolean selection function; its constructor and projections
have their ordinary record meanings.

Here is the full expansion of the estimators in this statement. For the preceding
design, or any such finite design D, write

* I_k(ω) = 1 when k is selected and 0 otherwise;
* E_D f = Σ_ω w(ω) f(ω);
* p_k = Σ_ω w(ω) I_k(ω), p_kl = Σ_ω w(ω) I_k(ω) I_l(ω),
  and Δ_kl = p_kl − p_k p_l;
* Var_D f = Σ_ω w(ω)(f(ω) − Σ_η w(η)f(η))²;
* t_y(ω) = Σ_k I_k(ω)y_k/p_k and m_y(ω) = t_y(ω)/|U|;
* h_y(ω) = Σ_k Σ_l 1_{p_kl>0} I_k(ω)I_l(ω)
  (Δ_kl/p_kl)(y_k/p_k)(y_l/p_l), with the summand explicitly zero
  outside the indicated positive-pair case;
* q_y(ω) = Σ_{k≠l, p_kl=0}
  [I_k(ω)y_k²/(2p_k) + I_l(ω)y_l²/(2p_l)], an **ordered** pair sum;
* c_y = h_y + q_y;
* cs_y(i,j) = (y_(i,0) − y_(j,1))²/4.

These expand `indicator`, `expect`, `pi`, `joint`, `inclusionCov`, `variance`,
`htTotal`, `htMean`, `htVarianceEstimator`, `quadraticCorrection`, `c2Estimator`,
and `collapsedEstimator`, respectively. All sums are ordinary finite sums of reals.

For M=5, define d = (3/2, −3/2, 1/2, −1/2, 0) and the fixed outcomes
y^α_(i,0) = α+d_i, y^α_(i,1) = −α+d_i. This expands `deviations5`,
`stratumMeans`, and `fixedStrata5`. Define V_α = Var_D m_(y^α),
H_α = E_D h_(y^α)/100, C_α = E_D c_(y^α)/100, and
CS_α = E_D cs_(y^α). The first conjunct (`T14Statement`) says

| α | V_α | H_α | C_α | CS_α | C_α−V_α | CS_α−V_α |
|---|---|---|---|---|---|---|
| 0 | 1/2 | 2/5 | 4/5 | 1/2 | 3/10 | 0 |
| 2 | 1/2 | 2 | 4 | 9/2 | 7/2 | 4 |

and asserts CS_0−V_0 < C_0−V_0 and C_2−V_2 < CS_2−V_2. It also states
|Fin 5 × Fin 5| = 25 and that every sample weight is 1/25.

For generated populations let Ξ be any type with a measurable space, μ any
probability measure on it, and ε_k : Ξ → ℝ for all k in the finite population.
`GaussianNoise μ ε 1` means each ε_k is μ-almost-everywhere measurable,
its pushforward law is the real Gaussian distribution of mean zero and variance
one, and the entire finite family is mutually independent (independence of the
generated coordinate sigma algebras, equivalently finite product event laws).
Set y_(i,s)(ξ) = (α if s=0, otherwise −α) + ε_(i,s)(ξ).
For each ξ define

* v_α(ξ) = Var_D m_(y(ξ));
* h_α(ξ) = E_D h_(y(ξ))/(2M)²;
* c_α(ξ) = E_D c_(y(ξ))/(2M)²;
* s_α(ξ) = E_D cs_(y(ξ)).

These are `wholeStrataV`, `wholeStrataH`, `wholeStrataC`, and `wholeStrataCS`.
`outcomeE μ f` is the real Bochner integral ∫ f dμ.
`WholeStrataIntegrable` is the conjunction that v, h, c, s, c−v, and s−v
are all Bochner integrable.

The next conjunct universally quantifies, **in order**, Ξ, its measurable space,
μ, a probability-measure instance, and ε for M=5. Assuming the Gaussian-noise
predicate, it concludes the six integrability statements at each of α=0 and α=2
and, writing BC_α = ∫(c_α−v_α)dμ and BS_α = ∫(s_α−v_α)dμ,
BC_0=2/5, BS_0=1/10, BS_0<BC_0, BC_2=18/5, BS_2=41/10, BC_2<BS_2.

The last conjunct independently universally quantifies Ξ, its measurable space,
μ, a probability instance, and ε for M=500. Assuming independent standard
Gaussian noise, at α=0 it concludes the six integrability statements and,
with V=∫v_0 dμ, C=∫c_0 dμ, CS=∫s_0 dμ,
V=499/1000, C=499/500, CS=1/2, V>0,
(C−V)/V=1 and (CS−V)/V=1/499.

The docstring describes these numerical identities and distinguishes rounded
simulation context from exact expectation assertions.

### Junk-value audit

Real division is total, with x/0=0. Generic HT definitions would therefore
silently accept zero p_k and empty populations. Here M=5 or 500, |U|=2M>0,
p_k=1/M>0, and the h summand divides by p_kl only on its positive branch.
Zero-pair terms in q have positive p_k. The scaling denominators 100 and (2M)²
are positive. Relative biases use V, whose positivity is an explicit conclusion.
No division-by-zero convention contributes to any asserted value.

Bochner integrals default to zero for nonintegrable functions. Gaussian finite
second moments and finite polynomial sums ensure all used integrands are
integrable; integrability is also explicitly concluded. The Gaussian helper
converts a real variance parameter with `toNNReal` (negative values become zero),
and the zero-variance Gaussian is a Dirac measure, but this statement uses only
variance parameter 1. All finite indices are in range; there is no partial
array lookup or default value. Natural cardinalities are cast to reals before
division. There is no truncated subtraction, real power with nonintegral
exponent, square root, logarithm, infimum/supremum, or limsup/liminf here.

## SAP.P027b.T15

### Objects, definitions, and quantifiers

There are no outer hypotheses. This is the conjunction of a samplewise universal
statement, a model universal implication, and three limits for every real α.
The finite design, I_k, E_D, p_k, p_kl, Δ_kl, t_y, m_y, h_y, q_y, c_y,
and cs_y have exactly the finite-sum expansions given in the T14 section; in
particular q is over ordered distinct zero-inclusion pairs and c=h+q.

First, for every natural M, every proof M≥2, and every real-valued array
y : Fin M × Fin 2 → ℝ, let N=2M and sample (i,j) uniformly from M² pairs.
For **every** such sample, `StrataFixed` asserts

* m_y(i,j) = (y_(i,0)+y_(j,1))/2;
* h_y(i,j)/N² = (M−1)/(4M) [y_(i,0)²+y_(j,1)²];
* c_y(i,j)/N² = (M−1)/(2M) [y_(i,0)²+y_(j,1)²];
* c_y(i,j)/N² = 2 h_y(i,j)/N²;
* cs_y(i,j) = (y_(i,0)−y_(j,1))²/4.

It also asserts Var_D m_y = (v_0+v_1)/4, where
v_s = (Σ_i y_(i,s)²)/M − ((Σ_i y_(i,s))/M)². This is
`stratumVariance`, the divisor-M population variance within stratum s.

Second, universally quantify Ξ, a measurable space on Ξ, a measure μ, its
probability instance, M : ℕ, M≥2, α : ℝ, and
ε : (Fin M × Fin 2) → Ξ → ℝ, **in that order**.
`NoiseMoments μ ε 1` assumes for every k that ε_k is integrable and ∫ε_k dμ=0,
and for every k,l that ε_k ε_l is integrable with integral 1 if k=l and 0
otherwise. It assumes neither normality nor independence; zero cross moments
are the stated hypotheses. The conclusion `StrataModel` concerns generated
outcomes y_(i,0)=α+ε_(i,0), y_(i,1)=−α+ε_(i,1).
Define V=∫Var_D m_y dμ, H=∫E_D(h_y/N²)dμ,
C=∫E_D(c_y/N²)dμ, CS=∫E_D(cs_y)dμ and
BH=H−V, BC=C−V, BS=CS−V. All integrals here are real Bochner integrals.
The conclusion is the complete conjunction

* V=(M−1)/(2M), H=(M−1)(1+α²)/(2M), C=(M−1)(1+α²)/M,
  CS=α²+1/2;
* BH=(M−1)α²/(2M), BC=(M−1)(1+2α²)/(2M), BS=α²+1/(2M);
* BH≥0, BC≥0, BS≥0;
* BC−BS=(M−2−2α²)/(2M)=1/2−(1+α²)/M;
* BC<BS iff M<2(1+α²), BC=BS iff M=2(1+α²),
  and BS<BC iff 2(1+α²)<M;
* BC<BS iff (M−2)/(M−1)<α²/(α²+1/2);
* C/CS=(1−1/M)(1+α²)/(1/2+α²)
  =(1−1/M)(2−α²/(α²+1/2));
* C−CS=1/2−(1+α²)/M.

This fully expands the helper bias formulas and `heterogeneity`.

Finally for every real α, as natural M tends to infinity,
(1−1/M)(2−α²/(α²+1/2)) tends to 2−α²/(α²+1/2),
1/2−(1+α²)/M tends to 1/2, and (M−1)/(2M) tends to 1/2.
These are Mathlib filter `Tendsto` assertions from `atTop` to the indicated
real neighborhood filters. The docstring describes sample formulas, model
expectations, nonnegative biases, parameter-qualified ranking, ratios and limits.

### Junk-value audit

All non-limit finite clauses require M≥2, so M, 2M, 4M, N², and M−1
in denominators are positive. The design gives p_k=1/M>0, and the h sum guards
its joint-inclusion denominators. CS=α²+1/2>0 makes C/CS a genuine ratio.
The heterogeneity denominator is always positive. Subtractions involving M
in these real formulas take place **after** casting to ℝ, so are not natural
truncated subtraction. The three limit sequences are defined also at M=0
using real x/0=0; changing finitely many terms does not affect any `atTop` limit.
Thus their junk initial values do not determine the assertion.

The noise moment predicate supplies integrability of each coordinate and each
quadratic cross product, so finite polynomial integrands in V,H,C,CS are
integrable. Bochner's zero-on-nonintegrability convention cannot create the
conclusions. All sums have nonempty relevant index types; probability measures
cannot live on an empty measurable space. No log, sqrt, nonintegral rpow,
extended-real conversion, empty extremum, limsup/liminf, or partial function
appears in this closure.

## SAP.P027b.T16

### Objects, definitions, and quantifiers

There are no outer hypotheses. The conclusion first asserts numerical identities
about two fixed stratum means and then a universally quantified Gaussian-pair
implication. For α : ℝ, the means are b_0=α and b_1=−α,
their average is (b_0+b_1)/2, their divisor-1 variance is
Σ_{s=0,1}(b_s−(b_0+b_1)/2)²/(2−1), and their divisor-2 variance is
Σ_{s=0,1}(b_s−(b_0+b_1)/2)²/2. At α=1/2, the first conjunct says
their average is 0, divisor-1 variance is 1/2,
α²/(α²+1/2) equals that divisor-1 variance divided by one plus itself,
and divisor-2 variance is 1/4.

Then, in order, for every type Ξ, measurable space on it, measure μ,
probability-measure instance, and family X : Fin 3 → Ξ → ℝ,
assume `WholeGaussianPair μ X`. This means:

* all three coordinate functions are measurable;
* the pushforward law of X_0 is (1/2)δ_1+(1/2)δ_{−1};
* the laws of X_1 and X_2 are each real Gaussian with mean 0 and variance 1;
* X_0,X_1,X_2 are mutually independent.

The Bernoulli definition used by `wholeFairSignLaw` is exactly the two-Dirac
mixture just displayed; the auxiliary proof checks 1/2∈[0,1].
Let S=X_0, ε=X_1, ε'=X_2, Y=(1/2)S+ε and Y'=(1/2)S+ε'.
`wholePairY` and `wholePairY'` have exactly these formulas.

The conclusion includes `PairMoments`: S=1 or −1 almost surely, ∫S dμ=0,
S,ε,ε' are integrable, ∫ε dμ=∫ε' dμ=0, ε² and ε'² are integrable with
integral 1, Sε,Sε',εε' are integrable with integrals all zero.
It also states every X_i, Y, and Y' is in Mathlib `MemLp _ 2 μ`, meaning
almost-everywhere strong measurability and finite L² norm.

For a probability measure ν define E_ν Z=∫Z dν,
Var_ν Z=(∫⁻|Z−E_ν Z|²dν).toReal,
Cov_ν(Z,W)=∫(Z−E_ν Z)(W−E_ν W)dν, and
ρ_ν(Z,W)=Cov_ν(Z,W)/sqrt(Var_ν Z Var_ν W).
These expand Mathlib variance/covariance and SAP `wholePearson` completely.
The asserted unconditional values are
E_μY=E_μY'=0, Var_μY=Var_μY'=5/4, Cov_μ(Y,Y')=1/4,
ρ_μ(Y,Y')=1/5, (1/2)²/((1/2)²+1/2)=1/3,
1/3−ρ_μ(Y,Y')=2/15, and ρ_μ(Y,Y')≠1/3.
Furthermore Var_μ((1/2)S) equals the divisor-2 variance 1/4.

Finally, for every real s satisfying s=1 or s=−1, the event
A_s={ξ | X_0(ξ)=s} has μ-probability 1/2. For
ν=(μ A_s)⁻¹ • μ.restrict A_s, it asserts that ν is a probability measure,
Y,Y'∈L²(ν), Var_νY=Var_νY'=1, Cov_ν(Y,Y')=0, and ρ_ν(Y,Y')=0.
This is conditioning on a positive-probability event, not a conditional-law
construction on a zero-probability fiber.

The docstring says precisely that these computations compare a printed ratio
with ordinary Pearson correlation, without identifying intended terminology.

### Junk-value audit

The generic Pearson helper would return zero at a zero variance product, and
`Real.sqrt` is zero on negative real arguments. Here the asserted variances
are positive 5/4 (unconditionally) or 1 (conditionally), so neither convention
affects the correlations. Mathlib's real variance uses `ENNReal.toReal`, which
maps infinity to zero, but the explicit L² conclusions exclude infinite
variance. All first and cross moments are genuine integrals by those L²
conclusions and the stated `PairMoments` integrability clauses.

Conditioning rescales by an extended-real reciprocal. A null or infinite event
would engage degenerate normalization conventions; each event here has mass
1/2 and is measurable because X_0 is measurable. The two divisor denominators
are 1 and 2, never zero. Fin 2 and Fin 3 have all used numeral indices in range.
The Gaussian variance and Bernoulli weights are valid and positive. There is
no clipped real variance conversion here, no natural subtraction affecting a
formula, no logarithm, rpow, extremum, limsup/liminf, or partial-function default.

## SAP.P027b.T17

### Objects, definitions, and quantifiers

There are no outer hypotheses. First universally quantify, in order, Ξ,
its measurable space, μ, its probability instance, α : ℝ, and
S,ε,ε' : Ξ → ℝ. Assume `PairMoments`, which explicitly means

* S∈{1,−1} μ-almost surely, ∫S dμ=0, and S is integrable;
* ε,ε' are integrable and have zero integrals;
* ε²,ε'² are integrable and have integral 1;
* Sε,Sε',εε' are integrable and have integrals 0.

There is no Gaussianity or independence hypothesis; these moment conditions
are exactly the premise. For Y=αS+ε and Y'=αS+ε', `PairCorrelation` concludes
E Y=E Y'=0, E Y²=E Y'²=α²+1, E YY'=α², and
E YY'/sqrt((E Y²)(E Y'²))=α²/(α²+1), where all E are real Bochner integrals.
The supplied moments imply finite second moments, so these are genuine
variances, covariance, and Pearson correlation under the zero means.

Independently, for every real α let b_0=α, b_1=−α,
v=Σ_s(b_s−(b_0+b_1)/2)²/(2−1),
q=α²/(α²+1/2), and r=α²/(α²+1).
The theorem asserts the full conjunction

* (b_0+b_1)/2=0 and v=2α²;
* q=v/(v+1)=2α²/(2α²+1);
* q−r=α²/((α²+1)(2α²+1))≥0;
* q=r iff α=0;
* r=q/(2−q);
* α²=q/(2(1−q)).

It further asserts that the real function q↦q/(2−q) is strictly increasing on
[0,1): for all a,b in that interval, a<b implies f(a)<f(b).
Its left-hand limit at 1 is 1, in the Mathlib neighborhood-within filter sense.
Finally, the six exact decimal inputs have these exact rational outputs:
0.33↦33/167, 0.50↦1/3, 0.67↦67/133,
0.82↦41/59, 0.90↦9/11, and 0.99↦99/101.
Lean decimal literals here are exact reals with the displayed finite decimal
expansions, not floating-point approximations.

The docstring calls q the printed heterogeneity parameter using divisor-1
stratum-mean variance, and describes its conversion to ordinary same-stratum
correlation. `stratumMeans`, `stratumMeansVariance`, `heterogeneity`,
`pairCorrelationFormula`, `outcomeE`, `PairMoments`, and `PairCorrelation`
have all been unfolded in the preceding paragraphs.

### Junk-value audit

α²+1/2, α²+1, 2α²+1, and v+1 are strictly positive. Also
q=α²/(α²+1/2) always satisfies 0≤q<1, making 2−q and 1−q positive.
The square-root input in the correlation is (α²+1)²>0.
All moments used in the conclusions are integrable consequences of the premise,
so neither Bochner's zero convention nor sqrt on negative arguments is used.
Although f(q)=q/(2−q) is globally totalized at q=2, the monotonicity interval
and a neighborhood of the left-limit point q=1 avoid that point entirely.
Divisor 2−1 is real 1. The left neighborhood filter at 1 is nontrivial.
No extended-real variance, empty index set, truncated subtraction, logarithm,
nonintegral power, extremum, limsup/liminf, or partial-function default is used.

## SAP.P027b.T18

### Objects, definitions, and quantifiers

There are no outer hypotheses. The first conjunct universally quantifies a
natural M and a proof M>0, then uses units U=Fin M × Fin 2 and samples
Ω=Fin M × Fin M with each ordered pair probability 1/M². Sample (i,j)
selects exactly (i,0) and (j,1); thus the two draws are independent and uniform.
The `Design` record consists precisely of these weights, their nonnegativity
and normalization proofs, and that selection function.

For each k let I_k(i,j) be its selection indicator in {0,1}.
Expand p_k=Σ_ω I_k(ω)/M²,
p_kl=Σ_ω I_k(ω)I_l(ω)/M²,
Δ_kl=p_kl−p_k p_l, and
Var_D I_k=Σ_ω(I_k(ω)−Σ_η I_k(η)/M²)²/M².
These are exactly `indicator`, `expect`, `pi`, `joint`, `inclusionCov`,
and finite `variance` unfolded down to finite real sums.
For **every** unit k and, where relevant, every ordered pair k,l, it asserts

* p_k=1/M;
* p_kl=1/M if k=l; 0 if k≠l and k,l have the same stratum;
  1/M² if they have different strata;
* Δ_kl=(1/M)(1−1/M) if k=l; −1/M² if k≠l in the same stratum;
  0 if their strata differ;
* Var_D I_k=(1/M)(1−1/M).

The second conjunct gives the explicit diagonal instance M=2,
p_((0,0),(0,0))=1/2.

The docstring describes these inclusion and covariance formulas. It separately
points to the outcome-index definition `stratumOutcomes`; that definition is
not part of this theorem's elaborated closure and no outcome-index equality is
asserted by T18 itself.

### Junk-value audit

M>0 rules out zero division and empty unit/sample types. The boundary M=1
is included legitimately: diagonal and cross-stratum joint probabilities are
one, indicator variances/covariances are zero, and no distinct same-stratum
unit pair exists. This does not trivialize the quantification for other M.
All subtractions are real; the explicit Fin 2 indices are valid. Finite sums
have no integrability/default-integral issue. No log, sqrt, rpow, extended-real
conversion, empty extremum, limsup/liminf, or partial-function default appears.
