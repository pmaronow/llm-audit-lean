import SAP.P009b.Defs
import SAP.P009b.Defs.WholeW1
import SAP.P009b.Defs.WholeW2
import SAP.P009b.Defs.WholeW3
import SAP.P009b.Defs.WholeW4

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

/-- P009-T18; Supplement A, pp. 9–10, Lemma A12 and its proof.
Complete randomization gives both incoming-count hypergeometric laws, the
zero-count case, the scalar likelihood-ratio identity with its strict bracket
bounds and every link of the scalar bound, and the supported-vector bound
(equivalently the finite-support maximum bound). Each supported-vector
likelihood ratio equals its treated-incoming-count likelihood ratio. -/
theorem SAP.P009b.T18 : SAP.P009b.T18WholeStatement := by sorry

/-- The printed claim is false: P009-T19; Supplement A, proof of Lemma A7: the sentence beginning 'Definition 7 gives', foot of p. 5 and top of p. 6. Definition 7: p. 685 (PDF p. 13).
The specified six-unit experiment has pair-dependence indicator one and three witnesses, refuting the printed equality between the indicator and its witness count. -/
theorem SAP.P009b.T19 : SAP.P009b.T19Statement := by sorry

/-- P009-T20; Supplement A, pp. 5–6, Lemma A7 and its proof; Definition 7,
p. 685 (PDF p. 13).
For every reflexive binary interference array and every involutive pairing
map, the pair-dependence indicator is bounded by both witness counts. The
complete normalized proof chain bounds average pair dependence by the triple
sum, factors it into outgoing-count products, bounds those by paired squares,
splits the two sums, reindexes by the pairing permutation, and identifies the
result with C_2 squared. The real inequality 2xy <= x^2+y^2 holds universally.
Only the positive sample size presupposed by the averages is required. -/
theorem SAP.P009b.T20 : SAP.P009b.T20WholeStatement := by sorry

/-- The printed B₂ evaluation is false: P009-T21; Supplement B, p. 8,
Section 1.4, the display after 'It follows that'.
For every realization of the independent U[0,3] covariates and U[0,7] errors
in their support, the six-unit fair one-source experiment has d_AVG = 3,
MSQ = 1, B₂ = 1/3 rather than the printed 2/3, B₁ = (1+2c₀)/3, and both
the aggregate decomposition and expected normalized variance gap equal
−(1+2c₀)/3, where c₀ is the source covariate-plus-error baseline.
Restriction: Retains the feasible full-support sampling-model refutation of
the exact B₂ evaluation and the correct aggregate formulas. Drops the six
individual pair covariance values, separate BER and HT-variance evaluations,
and the numerical c₀ = −1/4 specialization. The paper's c₀ = −1/4
hypothetical is outside the uniform-baseline support and is only an algebraic
auxiliary; this theorem makes no assertion refuting its printed convergence
display. -/
theorem SAP.P009b.T21 : SAP.P009b.T21Statement := by sorry

/-- P009-T22; Supplement B, p. 8, Section 1.4: the B₂ display and the display after
"Taken together, we can conclude that".
The fair one-source model has all corrected finite aggregate formulas and every individual
pair/arm conditional covariance identity. Under the standing regularity assumptions, its
normalized variance gap converges in probability about both the corrected and printed centres.
If a_n / sqrt(n) tends to zero its limit is one; if n / a_n² tends to zero its limit is minus one.
For comparable order the gap is asymptotic in probability to (1-a_n²/n)/(1+a_n²/n);
a ratio limit lambda > 0 gives (1-lambda²)/(1+lambda²), whose positive, zero and negative
possibilities are all realized by regular one-source studies. Comparability alone does not
assert existence of a limit. -/
theorem SAP.P009b.T22 : SAP.P009b.T22WholeStatement := by sorry

/-- The printed claim is false: P009-T23; Supplement B, p. 3, the paragraph after Figure B1, last sentence. Rows $a_n = n$ of Tables B1 and B3 (pp. 14 and 16) and of Tables B2 and B4 (pp. 15 and 17). Data generating process: p. 2; complete interference: p. 6.
Under independent uniform baselines the sampling-averaged signed bias is −1 and the design variances and mean squared errors have the stated exact formulas for both estimators and designs.
Restriction: Retains the uniform-baseline sampling integrals of both signed biases, both design variances, both mean squared errors, and the complete-design squared-bias/variance ratio. Adds integrability of each of the twelve sampling integrands. Drops the universal fixed-baseline clauses (a)–(d), the supportwise balance/outcome/effect/estimator/marginal identities, the claimed divergence of the squared-bias/variance ratios, and any identification of the integrals of design variances with a variance on a joint sampling-and-assignment space. The auxiliary 100-unit zero-baseline row is not used. -/
theorem SAP.P009b.T23 : SAP.P009b.T23Statement := by sorry

/-- P009-T24; Supplement B, p. 3, the paragraph after Figure B1, last sentence. Rows $a_n = n$ of Tables B1 and B3 (pp. 14 and 16).
In the complete-interference exception both estimators have signed bias −1, absolute bias one, and mean squared error equal to variance plus one.
Restriction: Retains the finite complete-interference exception for every positive even sample size, arbitrary fixed baselines, and both balanced complete and paired designs, including supportwise identities, both signed and absolute biases, and both mean squared errors. Drops the blanket empirical assertion that bias is negligible in all other settings and sample sizes, and does not certify the printed Monte Carlo table entries. -/
theorem SAP.P009b.T24 : SAP.P009b.T24Statement := by sorry

/-- P009-T25; Supplement B: captions of Table B1 (p. 14), Table B3 (p. 16), Table B5 (p. 18) and Table B7 (p. 20); rows $a_n = n$ of Panels B and C of Tables B1 and B3.
The modeled Monte Carlo statistic is |R⁻¹ ∑ᵣ (estimateᵣ − 1)|, the absolute signed mean error, and the full-interference population has negative signed bias with magnitude one.
Restriction: Formalizes the generic reporting formula, its loss of sign, and the complete-interference population bias. Does not assert that the deposited code computes this formula, that the four published captions use the corrected wording, or that the particular 50,000-draw table entries have the stated finite values. -/
theorem SAP.P009b.T25 : SAP.P009b.T25Statement := by sorry

/-- P009-T26; p. 688 (PDF p. 16), Remark 2, fourth sentence; Definition 9, p. 687.
No interference makes I and d diagonal, the masked other-treatment vector zero and the internal
mixing coefficient zero, so Assumption 6 holds. Standing regularity bounds every potential
outcome by k^(1+1/q) <= k^(3/2), supplies every finite moment order and attained infinite
maximal orders, and selects external exponent one. Under common Bernoulli(p) assignment,
the masked pair coefficient is alpha(T,T)=p(1-p), and the external coefficient at any specified
exponent theta is (n-1)[p(1-p)]^theta. For every exponent theta in [0,1] (the range of
(q-2)/q), its ratio to n tends to [p(1-p)]^theta > 0, it lies eventually between positive
multiples of n, and Assumption 5 fails. At exponent one p=1/2 gives (n-1)/4 and ratio to n/4
tending to one; p=1/3 gives 2(n-1)/9 and ratio tending to 8/9, hence no asymptotic
equivalence to n/4. -/
theorem SAP.P009b.T26 : SAP.P009b.T26WholeStatement := by sorry

/-- P009-T27; Supplement A, p. 37, proof of Proposition 11, first paragraph;
f_n^* is defined on p. 36.
Bernoulli prefixes have full support of size 2^b and both atom bounds. Finite
small-atom laws have disjoint three-point approximations. Minimizing maps and
minimizing sequences exist; every choice of minimizers has error at most twice
the geometric atom bound, that bound tends to zero, and both endpoint masses
tend to alpha/2. The explicit heavy-atom laws satisfy the printed lower bound
but cannot have both positive endpoint limits, showing why that lower bound
alone does not justify the limits. -/
theorem SAP.P009b.T27 : SAP.P009b.T27WholeStatement.{u} := by sorry

/-- P009-T28; Supplement A, p. 38, proof of Proposition 11, the sentence beginning 'Hence, for any fixed $s$' and the display after it.
A three-point variable has the stated mean and centering identities, and a mean tending to zero eventually preserves every CDF event away from the three atoms. -/
theorem SAP.P009b.T28 : SAP.P009b.T28Statement.{u} := by sorry

/-- P009-T29; Supplement A, p. 3, Lemma A3 and the first display of its proof.
For any positive finite population and any assignment design, Assumption 1B
with k > 0 and finite real q >= 2 implies the entire corrected covariance
moment chain for every real a in [0,q/2] whose ordinary outcome powers exist
on positive-probability assignments. The j arm uses Y_j. The chain includes
Cauchy--Schwarz, the second-moment bound, real-order Jensen interpolation,
Assumption 1B's moment bound, both square-root equalities, and the endpoint
Cov <= k^(2a); the same chain bounds absolute covariance. The printed first
line, using Y_i in both arm variables, is also a true Cauchy--Schwarz bound.
Ordinary powers follow `OrdinaryPowerW3`, preserving signed integer powers
and odd-denominator fractional powers; every zeroth power, including 0^0,
is one. Both a = 0 and 2a = q are included. Only the two outcomes entering
a covariance need powers on the design support. The usual measure-theoretic
conditions are assumed and hold automatically on this finite assignment space. -/
theorem SAP.P009b.T29 : SAP.P009b.T29WholeStatement_W3 := by sorry

/-- P009-T30; Supplement A, p. 34 (proof of Proposition 9) and p. 35 (proof of Proposition 10), the sentence beginning 'The second premise is satisfied by Corollary A4'. Definitions of the estimators: pp. 691–693 (PDF pp. 19–21).
MAX and SR are the specified multiples of BER, and the corresponding printed AVG identities hold exactly under the stated equality-or-zero alternatives. -/
theorem SAP.P009b.T30 : SAP.P009b.T30Statement := by sorry

/-- P009-T31; Supplement A, p. 38, proof of Proposition 11, last display. Definition A4: p. 36.
The corrected three-point CDF holds at every real threshold, and convergence of both outer masses gives pointwise CDF convergence including at the jumps. -/
theorem SAP.P009b.T31 : SAP.P009b.T31Statement.{u} := by sorry

/-- P009-T32; Supplement B, p. 6, the paragraphs beginning 'To understand this behavior' and 'Now consider the same situation'. Definition of $\mathrm{bal}(G_i)$ and of the outcomes: p. 2.
A treatment flip changes unweighted balance by two, with the specified integer multiplier crossings and paired-flip changes. -/
theorem SAP.P009b.T32 : SAP.P009b.T32Statement := by sorry

/-- P009-T33; Supplement B, p. 8, Section 1.4, the paragraph beginning 'Recall that'. Definition of $\xi_{ij}(z)$: p. 690 (PDF p. 18).
The one-source model has zero untreated spillover, the specified treated spillovers, vanishing reciprocal products, source weighted mean, and printed B₁ formula. -/
theorem SAP.P009b.T33 : SAP.P009b.T33Statement := by sorry

/-- P009-T34; Supplement A, p. 17, proof of Lemma A17, last display and the
sentence after it. Lemma A17: p. 16. Lemma A4: p. 3.
Under paired randomization and Assumption 1, full and masked outcomes agree.
Both treatment probabilities are one half; treatments in distinct pairs are
independent, whole pairs are mutually independent, and each own treatment is
independent of the joint vector outside its pair. Each absolute conditional
potential-mean shift equals half the difference between the two conditional
means, is at most its unconditional absolute first moment, and that moment is
at most k. Noninterfering-partner terms vanish. Moreover k ≥ 2 and the two-arm
sum is at most 2k ≤ 2k². The complete weighted proof chain gives the unchanged
Lemma A17 bound |ADSE − EATE| ≤ 2k² n⁻¹ R_SUM. The usual measure-theoretic
conditions are assumed and hold automatically on this finite assignment space.
The corrected independence assertion requires distinct units in different pairs;
the factorization assertions state the stronger joint independence actually used. -/
theorem SAP.P009b.T34 : SAP.P009b.T34WholeStatement_W4 := by sorry

