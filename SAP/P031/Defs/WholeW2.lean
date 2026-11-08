import Mathlib
import SAP.P031.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031

open scoped BigOperators Topology
open Filter Finset

noncomputable section

/-- Uniform boundedness of the two divisor-N fourth population moments,
as in Condition 1 of the CLT cited in Section 3. -/
def BoundedFourthMomentsW2 (P : ℕ → Population) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
    (∑ i, ((P n).y1 i) ^ 4) / (P n).N ≤ B ∧
    (∑ i, ((P n).y0 i) ^ 4) / (P n).N ≤ B

/-- The limiting actual randomization variance on the N-times-variance scale. -/
def LeadingTrueVarianceW2 (p v1 v0 c : ℝ) : ℝ :=
  (1 - p) / p * v1 + p / (1 - p) * v0 + 2 * c

/-- The deterministic limit of N times the Neyman/HC2 variance estimate. -/
def ConservativeVarianceLimitW2 (p v1 v0 : ℝ) : ℝ := v1 / p + v0 / (1 - p)

/-- The regular finite-population regime carried by the cited CLT:
growing populations, an interior allocation limit, bounded fourth moments,
finite first and centered second/mixed moment limits, positive marginal
variance limits, and a nondegenerate centered treatment contrast.
The allocation and moment conditions express the cited regular regime.
Strictly positive limiting contrast variance is an additional restriction
of this candidate. The D=0 coverage case is not established here.
These are substantive conditions, not measurability or existence guards.
Centering at population means supplies the cited mean-zero normalization;
the population average treatment effect is unrestricted. Rows need no joint law. -/
structure RegularRegimeW2 (P : ℕ → Population) (p μ1 μ0 v1 v0 c : ℝ) : Prop where
  growingW2 : GrowingPopulations P
  pPositiveW2 : 0 < p
  pLessOneW2 : p < 1
  allocationW2 : Tendsto (fun n => ((P n).M : ℝ) / (P n).N) atTop (𝓝 p)
  fourthW2 : BoundedFourthMomentsW2 P
  mean1W2 : Tendsto (fun n => groupMean univ (P n).y1) atTop (𝓝 μ1)
  mean0W2 : Tendsto (fun n => groupMean univ (P n).y0) atTop (𝓝 μ0)
  variance1W2 : Tendsto (fun n => popVariance (P n).y1) atTop (𝓝 v1)
  variance0W2 : Tendsto (fun n => popVariance (P n).y0) atTop (𝓝 v0)
  covarianceW2 : Tendsto (fun n => popCovariance (P n).y1 (P n).y0) atTop (𝓝 c)
  variance1PositiveW2 : 0 < v1
  variance0PositiveW2 : 0 < v0
  contrastPositiveW2 : 0 < LeadingTrueVarianceW2 p v1 v0 c

/-- Section 3, p. 367; p. 368 after Corollary 1 and footnote 2.
Under uniform complete randomization Neyman's finite bias is exactly the
divisor-N population variance of individual treatment effects divided by
N-1, hence nonnegative, and HC2 equals Neyman on every legal assignment.
In the regular finite-population asymptotic regime of the cited CLT, the
assumptions are N tending to infinity, M/N tending to p in (0,1), uniformly
bounded divisor-N fourth moments, finite limits of first and second/mixed
population moments, positive limiting marginal variances, and a positive
finite limiting N-times-actual-variance contrast. The strictly positive
contrast limit D is an extra restriction: D=0 coverage is not proved here.
Under that regime the centered estimator standardized by its actual variance
has a standard normal limit. HR, HC1 and HC3 are first-order equivalent to HC2,
and every fixed-z normal interval based on Neyman, HC2, HR, HC1 or HC3 has
asymptotically correct
or conservative coverage, with limit inferior at least 2 Phi(z)-1 for z>0.
The usual measure-theoretic conditions are assumed; each row here has a
finite assignment space, so all statistics are measurable and all moments
exist. No independence across rows or between treatment indicators is assumed. -/
def T5CitedRegimeStatement : Prop :=
  (∀ P : Population,
    expectation P.M (neymanEstimator P) - trueVariance P =
      popVariance (fun i => P.y1 i - P.y0 i) / ((P.N : ℝ) - 1) ∧
    0 ≤ expectation P.M (neymanEstimator P) - trueVariance P ∧
    ∀ s ∈ (univ : Finset (Fin P.N)).powersetCard P.M,
      hc2Estimator P s = neymanEstimator P s) ∧
  (∀ (P : ℕ → Population) (p μ1 μ0 v1 v0 c : ℝ),
    RegularRegimeW2 P p μ1 μ0 v1 v0 c →
    StandardizedNormalLimit P ∧
    FirstOrderEquivalent P hrEstimator hc2Estimator ∧
    FirstOrderEquivalent P hc1Estimator hc2Estimator ∧
    FirstOrderEquivalent P hc3Estimator hc2Estimator ∧
    ∀ z : ℝ, 0 < z →
      ConservativeCoverage P neymanEstimator z ∧
      ConservativeCoverage P hc2Estimator z ∧
      ConservativeCoverage P hrEstimator z ∧
      ConservativeCoverage P hc1Estimator z ∧
      ConservativeCoverage P hc3Estimator z)

end
end SAP.P031
