import SAP.P001d.Defs
import SAP.P001d.Defs.WholeW1
import SAP.P001d.Defs.WholeW2
import SAP.P001d.Defs.WholeW3

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

/-- Definitions 3.3.7 and 3.3.9, pp. 121,123 (PDF pp. 139,141);
Definition 3.3.2, p. 118 (PDF p. 136).
The printed claim is false: the admitted even normalized signed kernel gives a
negative integrated estimate at a-1 and a strictly decreasing estimate on (a-2,a-1).
For the continuous triangular population density on [5/4,7/4], every nonempty
sample in that interval gives an integrated estimate at zero in [-3/8,-1/8].
Thus with probability one it is outside the CDF domain of the fixed functional
G ↦ sqrt(G(0)), and its value at zero has no real square root. -/
theorem SAP.P001d.T58 : SAP.P001d.T58WholeStatement := by sorry

/-- P001-T59; p. 123 (PDF p. 141), Definition 3.3.9; Definition 3.3.7, p. 121 (PDF p. 139).
A nonnegative normalized even kernel gives a nonnegative normalized kernel density and a continuous CDF with the required endpoint limits, hence a valid argument for a statistical functional on CDFs. -/
theorem SAP.P001d.T59 : SAP.P001d.T59Statement := by sorry

/-- P001-T60; p. 123 (PDF p. 141), Definition 3.3.9, last line.
The corrected integrated estimator is the average of shifted kernel integrals, and the rectangular-kernel estimator has the empirical-CDF difference formula away from its excluded endpoint. -/
theorem SAP.P001d.T60 : SAP.P001d.T60Statement := by sorry

/-- P001-T61, p. 131 (PDF p. 149), with footnote 31, p. 120 (PDF p. 138).
The printed claim is false: the specified half-uniform, quarter-positive and
quarter-negative heavy-tail population has the stated exact survival probabilities,
local affine CDF and unique median zero. Its odd-size median has both normal weak
limits but its scaled bootstrap variance exceeds 5 with probability at least 3/16.
The specified CDF functional T0 is locally affine, Hadamard differentiable in every
bounded sup-norm direction, and, along all positive sizes, has marginal and conditional
bootstrap limits N(0,1/4). Its scaled bootstrap variance still exceeds 5 with probability
at least 3/16 at every odd size at least 5, and cannot converge to 1/4.
The resamples repeating a high and a central observation give exactly those observations. -/
theorem SAP.P001d.T61 : SAP.P001d.T61WholeStatement := by sorry

/-- P001-T62, p. 131 (PDF p. 149); Definition 3.2.32, pp. 113–114 (PDF pp. 131–132).
Assume the estimator has the stated root-n normal limit. For the exact finite
with-replacement bootstrap, conditional weak convergence to N(0,phi^2), phi>0,
makes the real-cutoff square-tail condition equivalent to convergence of n times
the bootstrap variance to phi^2. If these equivalent conditions hold, the scaled
bootstrap standard deviation converges to phi. The usual measure-theoretic
conditions are assumed; only the observed and resampled statistics must be
measurable. The finite-variance sample-mean formula and consistency, and the all-size
median case under a positive continuous local density, a unique median and a finite
positive-order absolute moment, hold as well. -/
theorem SAP.P001d.T62 : SAP.P001d.T62WholeStatement := by sorry

/-- P001-T63; Sentence: p. 138 (PDF p. 156). Definitions 3.5.1, 3.5.2: p. 136 (PDF p. 154). Theorems 3.5.3–3.5.5: p. 137 (PDF p. 155). Theorem 3.5.6: p. 138 (PDF p. 156).
IID cluster averages have the stated sample-mean, expectation, variance, covariance-sum and weak-law formulas. -/
theorem SAP.P001d.T63 {Ω : Type*} [MeasurableSpace Ω] : SAP.P001d.T63Statement Ω := by sorry

/-- P001-T64; Example 3.5.8: pp. 140–141 (PDF pp. 158–159). Block bootstrap
steps: p. 141 (PDF p. 159). Theorem 3.5.5: p. 137 (PDF p. 155).
IID clusters with common finite variances and common correlations between
distinct units have the stated diagonal and off-diagonal covariances, their
explicit count expansion, the design-effect variance, and both endpoint formulas.
Correlation requires positive standard deviations only for distinct pairs;
singleton clusters may have zero variance. The corrected block bootstrap draws
l intact clusters independently and uniformly, retains lm observation slots,
applies the estimator to each resample, permits any finite number of independent
repetitions, and uses the estimator's conditional standard deviation. -/
theorem SAP.P001d.T64 : SAP.P001d.T64WholeStatement := by sorry

/-- P001-T65; Theorem 4.1.4 and the stacked system: p. 148 (PDF p. 166);
rest of the proof and Theorem 4.1.5: p. 149 (PDF p. 167); proof of 4.1.5:
p. 150 (PDF p. 168). Definitions 4.1.2–4.1.3: pp. 146–148.
For every nonempty intercept design the correctly indexed scalar residuals stack
as Y-Xb, and the squared criterion is their dot product. Normalizing by n leaves
its minimizers unchanged, and a minimizer exists. An invertible Gram matrix gives
the unique inverse-formula minimizer. Every minimizer, including those of singular
designs, satisfies the normal equations and has zero residual mean, zero empirical
residual-regressor cross moments, and zero empirical residual-regressor covariances.
These identities hold for every realized sample, hence for IID samples. -/
theorem SAP.P001d.T65 : SAP.P001d.T65WholeStatement := by sorry

/-- P001-T66; p. 153 (PDF p. 171) and p. 155 (PDF p. 173).
The usual measure-theoretic conditions are assumed.
For a sample of size at least two with an intercept and invertible Gram matrix,
the OLS residuals are centered and their unbiased empirical variance is the
residual sum of squares divided by n - 1. The normalized outer-product formulas
equal the robust and classical matrix covariance estimates. Both estimates have
nonnegative diagonals, and the standard error of coefficient k is the square
root of entry (k,k), the book's ordinal row and column k + 1. -/
theorem SAP.P001d.T66 : SAP.P001d.T66WholeStatement := by sorry

/-- P001-T67; p. 155 (PDF p. 173); sandwich form p. 152 (PDF p. 170).
Under the stated measurability and finite-moment conditions, conditional mean zero and
constant conditional residual variance give the conditional second moment, weighted
population moment factorization, and exact sandwich simplification.
Restriction: Only the exact conditional-second-moment, population factorization, and sandwich identities are formalized. The corrected large-sample OLS covariance approximation and asymptotic normality are omitted; the equivalence between linearity of the response CEF and zero conditional BLP residual mean is not asserted. -/
theorem SAP.P001d.T67 {Ω : Type*} [MeasurableSpace Ω] : SAP.P001d.T67Statement Ω := by sorry
