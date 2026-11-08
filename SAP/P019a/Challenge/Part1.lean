import SAP.P019a.Defs
import SAP.P019a.Defs.WholeW1
import SAP.P019a.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P019a

/-- P019-T1; supplement Appendix C, pp. 2–3, Figure A1 lower-left panel.
The printed and coded ceiling mechanisms have different response vectors and exact mixture contrasts.
Restriction: Uses the deterministic mixture after affected status has been integrated out; omits a joint
random-variable model and its conditional-observable-mean identification. The counterexample concerns the
mechanism description and contains no numerical power guarantee. -/
theorem SAP.P019a.T1 : T1Statement := by sorry

/-- P019-T2; supplement Appendix C, pp. 2–3, Figure A1 lower-left panel.
The corrected ceiling response has the stated subject increments and both exact mixture-contrast formulas.
Restriction: Drops the assertion of about 80 percent power with 800 affirmative respondents and 20 percent
affected. Uses the integrated deterministic mixture rather than constructing the joint population and
identifying its observable conditional means. -/
theorem SAP.P019a.T2 : T2Statement := by sorry

/-- P019-T3; Lemma 2, p. 48; Appendix B, pp. 62–63, displays (6), (9), and the following sentence.
The four independent fair-bit population has the complete stated cell and observable laws. Its printed
ratios have positive empty-cell probabilities for every sample size; zero completion gives the stated
nonzero covariances. Conditional binomial counts expose the missing mass for every k. At n=4 the six
occupied-cell moments refute the exact product-variance formula, and the realized treatment count need
not equal its expectation. The comparison uses the specified completion and conditioning. -/
theorem SAP.P019a.T3 : SAP.P019a.T3WholeStatement := by sorry

/-- P019-T4; corrected Lemma 2, p. 48, and Appendix B, pp. 62–63, displays (6)–(9).
For iid observations from any bounded count-valued population satisfying Assumptions 1–4, the empty-cell
probabilities, conditional binomial law and missing-mass sums hold for every n, including zero and one.
K=n(1-Ybar). On occupied cells, the stated pattern-conditional means, variances and covariances give the
corrected Lemma 2 and exact product-variance identity. Its discrepancy from the printed product expression
is Cov(A²,h | D), of order n⁻² with the stated limit coefficient. The unconditional direct-response moments
and population contrast identities hold, and n gamma is the expected treatment count; the realized count
is n gammaHat. Conditional moments are asserted only on positive-probability events. -/
theorem SAP.P019a.T4.{u} : SAP.P019a.T4WholeStatement.{u} := by sorry

/-- P019-T5; Section 4.1, p. 50, final distribution-comparison sentence.
The independent fair X,W,Z population with Y=X satisfies all four assumptions. Every cell and marginal
variance is positive as specified. The full conditional laws of control V and treated V+1 have disjoint
supports {0,1} and {2,3}. The preceding displayed identity is true for every real t: control V has the
same conditional law as treated V-1, including equality of all distribution functions. -/
theorem SAP.P019a.T5 : SAP.P019a.T5WholeStatement := by sorry

/-- P019-T6; corrected Section 4.1 distribution-comparison sentence, p. 50.
Under Assumptions 1–3 and positive affirmative-cell probabilities, control V and treated V-1 have
identical conditional point probabilities, both equal to the baseline law given an affirmative response. -/
theorem SAP.P019a.T6.{u} : T6Statement.{u} := by sorry

/-- P019-T7; supplement Appendix C, p. 2, first paragraph; Section 4.1, p. 50.
Both the sixteen-atom and eight-atom fair-bit constructions satisfy Monotonicity, No Liars and No Design
Effects, and Non-Degeneracy, with delta zero and beta two. The first has the stated latent classes,
cell moments, potential-response independence, marginal Y independence, and explicit zero-versus-1/32
failure of whole-triple independence. Thus Treatment Independence supplies a missing cause of beta
being different from one, while false confession and list design effects are absent in both examples. -/
theorem SAP.P019a.T7 : SAP.P019a.T7WholeStatement := by sorry

/-- P019-T8; corrected supplement Appendix C, p. 2, first paragraph.
The baseline-composition decomposition yields beta one under Assumptions 1–3 and both corrected
failure diagnoses when the population contrast differs from one. -/
theorem SAP.P019a.T8.{u} : T8Statement.{u} := by sorry

/-- P019-T9; Section 5.3, p. 56, the Fisher joint-test reference distribution.
The seven independent fair coordinates give the stated ordered five-list construction, each list's
Assumptions 1–4 and beta one, exact cell summaries, influence functions, and root-n linearization.
The joint Gaussian limit has standard normal margins and correlations 1/2 and 1/sqrt(2); every marginal
p-value tends to the uniform law. Fisher's limit is the stated Gaussian transform, with variance
20+12 Var(h(E5))+8 Cov(h(E5),g(E5)) greater than 20, whereas chi-square ten has variance 20.
Every expectation defining h(t) is integrable, for every real t.
The statistics are defined with probability tending to one and their limits hold for every completion.
Thus these per-list assumptions and independent assignments do not ensure Fisher calibration. -/
theorem SAP.P019a.T9 : SAP.P019a.T9WholeStatement := by sorry

/-- P019-T10; corrected Section 5.3, p. 56.
The full joint assignment premise gives beta one, zero cross-influence moments, independent normal
and uniform limits, and the chi-square ten Fisher limit.
Restriction: Omits the reported statistic 12.143, p-value 0.276 and empirical nonrejection.
Uses zero completions for empty cells and unavailable variances, and statistic zero when the variance
estimate is nonpositive. -/
theorem SAP.P019a.T10.{u} : T10Statement.{u} := by sorry

/-- P019-T11; Lemma 1 proof and equation (2), p. 48; Corollary 1, p. 49;
Lemma 2 proof, p. 62; Proposition 2 proof, p. 64.
For any probability space with the standing bounded count and binary observations,
the corrected treatment-arm means, affirmative-response sensitive mean, and
affirmative-cell list-mean shift hold under their respective stated assumptions.
Under Assumptions 1-4, the printed Wald interval is defined with probability
tending to one and its coverage tends to 1-alpha for every 0 < alpha < 1,
independently of fixed completions outside its domain. No quantile-set premise
is needed. The correction in (d) labels the negative responders and has no
independent mathematical assertion. -/
theorem SAP.P019a.T11.{u} : SAP.P019a.T11WholeStatement.{u} := by sorry
