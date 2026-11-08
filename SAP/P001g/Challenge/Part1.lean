import SAP.P001g.Defs.WholeW1
import SAP.P001g.Defs.WholeW2
import SAP.P001g.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

universe u v w z u1 v1

/-- P001-T115. Location: Definition 7.1.9, p. 244 (PDF p. 262);
Theorem 7.1.10, p. 245 (PDF p. 263); decomposition, p. 247 (PDF p. 265).
The usual measure-theoretic conditions are assumed. Random assignment identifies the population ATE. For arbitrary assignment the
observed arm difference equals the potential-outcome arm difference, then the
sum-of-effect-and-control arm difference, then ATT plus selection bias.
The plug-in estimates of the two identified potential-outcome means under the
empirical observed law are the two displayed arm averages, and their difference
is the difference-in-means estimator, whenever both sample arm counts are positive. -/
theorem SAP.P001g.T115 : SAP.P001g.T115WholeStatement := by sorry

/-- The usual measure-theoretic conditions are assumed. Strong ignorability gives discrete and conditional ATE identification and all three propensity-score conclusions, with a separate moment-free domain for the score result.
P001-T116. Location: Definition 7.1.12: p. 247 (PDF p. 265). Theorem 7.1.13: p. 248 (PDF p. 266). Theorem 7.1.14: p. 249 (PDF p. 267). Definition 7.1.15: p. 250 (PDF p. 268). Theorem 7.1.16: p. 251 (PDF p. 269), proof on pp. 251–252. -/
theorem SAP.P001g.T116 : SAP.P001g.T116Statement.{u, v, w, z, u1, v1} := by sorry

/-- P001-T117. Location: Theorem 7.2.5, pp. 265–266 (PDF pp. 283–284);
Theorem 7.2.8, pp. 267–269 (PDF pp. 285–287).
The usual measure-theoretic conditions are assumed. Strong ignorability gives
the population IPW identity. The augmented ATE identity holds if either both
outcome regressions are correct and the approximating propensity has overlap,
or the propensity is correct. Only the complete augmented score is required
to be integrable; separate integrability of the nuisance regressions is not
assumed in the correct-propensity alternative. -/
theorem SAP.P001g.T117 : SAP.P001g.T117WholeStatement := by sorry

/-- The printed claim is false: Hadamard differentiability need not yield a positive-variance plug-in normal limit, and finite second moments do not ensure supremum-norm Hadamard differentiability of the mean.
P001-T118. Location: p. 120 (PDF p. 138). -/
theorem SAP.P001g.T118 : SAP.P001g.T118Statement.{u} := by sorry

/-- The explicitly specified integrated squared-risk consistency assertion for polynomial least-squares sieves is false under the printed degree-rate conditions.
P001-T119. Location: Definition 4.3.9 and the attached consistency claim, pp. 168–169 (PDF pp. 186–187).
Restriction: The usual measure-theoretic conditions are assumed, including existence of population squared errors in the canonical BLP setting, enforced by MemLp (Y 0) 2 μ. Refutes only the specified integrated squared-risk interpretation; no refutation of the book's undefined regional, pointwise or prediction-measure consistency assertion is claimed. Uses the target-authorized squared-residual correction and makes no assertion about the literal unsquared argmin. Retains the universe-zero domain, covariate density positive exactly on a nondegenerate compact interval and literal ContDiff ℝ ⊤ CEF premise. Fits are not assumed measurable; risk-event probabilities use measure outer values. -/
theorem SAP.P001g.T119 : SAP.P001g.T119Statement := by sorry

/-- P001-T121. Location: Section 5.2.5, p. 199 (PDF p. 217), second paragraph;
Definitions 5.1.1 and 5.2.2; unique arg max convention, Glossary p. 285.
The printed claim is false: in this compact two-component mixture on three
outcomes, the sample likelihood has a unique maximizer for every sample of
every positive size, so the book's unique arg max estimator is defined
everywhere. The first component alone characterizes the true law, but this
estimator cannot be consistent for every true full vector (1,b), where the
unused component's parameter b ranges over the unit circle. The refuted
assertion does not assume identification of the full vector. Failure of
consistency refutes the consistency-and-asymptotic-efficiency conjunction;
no separate definition or refutation of efficiency is needed. The usual
measure-theoretic conditions are assumed; all sample statistics are measurable. -/
theorem SAP.P001g.T121 : SAP.P001g.T121WholeStatement.{u} := by sorry

/-- The printed claim is false: At nominal level one half, an iid conditional-independence placebo null has limiting rejection probability one, even when rejections require nonsingular regressions, positive residual risk and positive residual degrees of freedom.
P001-T124. Location: p. 270 (PDF p. 288). -/
theorem SAP.P001g.T124 : SAP.P001g.T124Statement := by sorry

/-- The iid sample mean converges in probability to its expectation with a finite second moment, including zero variance.
P001-T125. Location: p. 100 (PDF p. 118). Definition 3.2.6: p. 99 (PDF p. 117). -/
theorem SAP.P001g.T125 : SAP.P001g.T125Statement.{u} := by sorry

/-- Both printed CLT forms hold for iid data of finite positive variance, with the finite standardization identity and moments.
P001-T126. Location: p. 109 (PDF p. 127). Definition 3.2.23: p. 109. Definition 3.2.22: p. 108 (PDF p. 126). -/
theorem SAP.P001g.T126 : SAP.P001g.T126Statement.{u, v, w} := by sorry

/-- The rectangular-kernel density estimator is pointwise consistent for a continuous density when positive bandwidths tend to zero and n times bandwidth tends to infinity.
P001-T127. Location: p. 122 (PDF p. 140); proof sketch on p. 123 (PDF p. 141); the continuity condition is stated on p. 121 (PDF p. 139). -/
theorem SAP.P001g.T127 : SAP.P001g.T127Statement.{u} := by sorry

/-- P001-T128. Location: Theorem 3.4.2, pp. 125–126 (PDF pp. 143–144);
Definition 3.4.1 and footnote 34, p. 124 (PDF p. 142).
The usual measure-theoretic conditions are assumed. For an asymptotically
normal estimator with finite positive asymptotic variance and a nonnegative
sampling-variance estimator consistent at the n scale, the displayed open sets
have limiting coverage at least 1-alpha for every alpha in (0,1).
Restriction: Proves limiting coverage at least 1-alpha for the displayed open sets under the stated nonnegative variance-estimator and n-scale consistency assumptions. Omits footnote 34's requirement that the two endpoints be strictly ordered almost surely at every positive sample size; the displayed sets may be empty at finite sample sizes. -/
theorem SAP.P001g.T128 : SAP.P001g.T128Statement.{u} := by sorry

/-- Actual-product maximum-likelihood estimators are consistent under explicit uniform regularities, and a separate true-model lemma characterizes the maximum expected log likelihood and equality.
P001-T129. Location: Theorem 5.2.6: p. 193 (PDF p. 211). Proof sketch: pp. 193–194 (PDF pp. 211–212).
Restriction: Retains actual-product MLE consistency under compactness, finite observed logs, parameterwise almost-sure observed-density positivity, continuity and unique maximization of the expected log likelihood, and an additional finite error envelope dominating the empirical-log error for every sample size, sample point and parameter, converging in probability to zero. The expected-log maximum and density-equality characterization have an independent domain requiring only a true normalized model, support domination and finite observed logs. Omits the separate product-log/sample-average identity, the unique sample-maximizer assertion, the pointwise WLLN assertion as a separate conclusion, and any derivation of the uniform error-envelope premise from the printed informal regularities. -/
theorem SAP.P001g.T129 : SAP.P001g.T129Statement.{u, v} := by sorry

/-- Both printed missing-outcome bound estimators are unbiased at every positive sample size and consistent for their displayed endpoints under iid observable pairs.
P001-T130. Location: pp. 211–212 (PDF pp. 229–230); proof on p. 212. -/
theorem SAP.P001g.T130 : SAP.P001g.T130Statement.{u} := by sorry

