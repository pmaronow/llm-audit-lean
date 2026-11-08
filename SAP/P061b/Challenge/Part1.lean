import SAP.P061b.Defs
import SAP.P061b.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P061-T12; main text pp. 2, 6, 8–10, Condition 5.2 and Table 3.
Global stability identifies the positive-cell potential outcomes and their contrasts independently
of design, and housemate exposure gives AEED one for every positive household design. -/
theorem SAP.P061b.T12 : SAP.P061b.T12Statement := by sorry

/-- P061-T13; main text pp. 2 and 8, Condition 5.1.
Support stability identifies supported-cell outcomes and contrasts, is implied by global stability,
and gives exactly the same possible observed-data laws as global stability under a fixed design. -/
theorem SAP.P061b.T13 : SAP.P061b.T13Statement := by sorry

/-- P061-T14; main text pp. 8–10, Section 5.2 and Tables 1–2.
The household voting schedule has AEEDs minus one, one and zero under the three printed designs,
with the printed AEPOs, support stability, and an explicit off-support failure of global stability. -/
theorem SAP.P061b.T14 : SAP.P061b.T14Statement := by sorry

/-- P061-T15; main text pp. 11–12, Sections 6.1–6.2 and Tables 4–5.
The printed attenuation, amplification and hidden-version schedules give the stated contrasts
under both designs and satisfy support stability while failing global stability. -/
theorem SAP.P061b.T15 : SAP.P061b.T15Statement := by sorry

/-- P061-T16; supplement pp. 1–2, Equations (1) and (3); main text pp. 13–14.
The usual measure-theoretic existence conditions are assumed, expressed as exposure-restricted
absolute first moments for every unit at each exposure used.
With positive exposure probabilities, the HT mean and contrast have finite ordinary expectations
and are unbiased for the AEPO and AEED without stability assumptions. -/
theorem SAP.P061b.T16 : SAP.P061b.T16Statement := by sorry

/-- P061-T17; supplement pp. 1–2, Equation (2) and the take-away sentence.
Equal positive exposure margins reduce HT to the fixed-denominator exposed mean,
which is the sample mean when the exposed count is fixed. A simple random sample
without replacement, including the census, has sample mean
unbiased for the AEPO on arbitrary raw assignment spaces. A completely randomized
binary experiment on any feasible set containing the binary cube has difference
in means unbiased for the AEED. No stability assumption is needed. The usual
measure-theoretic conditions are assumed; survey exposure first moments make
the conditional means defined, and the experiment supplies its moments. -/
theorem SAP.P061b.T17 : SAP.P061b.T17WholeStatement := by sorry

/-- P061-T18; supplement pp. 2–4, Equations (4), (5) and (9).
Under support stability, the revealed-value reduction and both printed variance expressions,
the covariance expression and the variance-of-contrast identity hold on general atomic designs. -/
theorem SAP.P061b.T18 : SAP.P061b.T18Statement := by sorry

/-- P061-T19; supplement pp. 3–4, Equations (6)–(8).
Under individual positivity and NURVA, the joint-positive HT variance estimator
is unbiased with the printed covariance-sum expectation, and the Young-corrected
estimator is conservative in expectation. Each pair's Young bound admits an
integrable unbiased estimator using only marginal exposure probabilities.
If a joint exposure probability is zero, the two target cells are never jointly
revealed on support, and no single observed-data statistic is unbiased for their
EPO product for every NURVA outcome schedule. All sums include ordered diagonal
pairs. The usual measure-theoretic conditions are assumed; all displayed moments
follow from positivity and NURVA even with infinite raw support. -/
theorem SAP.P061b.T19 : SAP.P061b.T19WholeStatement := by sorry

/-- P061-T20; supplement p. 7, Equation (10); main text p. 14.
With the ordinary moments required by the claim's definitions, calibrated predictions give
integrable unbiased adjustment without stability, including independent or mean-independent predictions. -/
theorem SAP.P061b.T20 : SAP.P061b.T20Statement := by sorry

/-- P061-T21; supplement pp. 5–6, Conditions 1.1–1.3 and Proposition 1.
The three printed boundedness and dependence conditions together with support stability imply
convergence in probability of the HT estimation error to zero along growing positive populations. -/
theorem SAP.P061b.T21 : SAP.P061b.T21Statement := by sorry
