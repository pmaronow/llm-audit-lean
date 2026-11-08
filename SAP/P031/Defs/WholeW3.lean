import Mathlib
import SAP.P031.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031

open scoped BigOperators Topology
open Finset Filter

noncomputable section

/-- The divisor-N fourth raw moment of a finite potential-outcome schedule. -/
def fourthMomentW3 {N : ℕ} (y : Fin N → ℝ) : ℝ :=
  groupMean univ (fun i => y i ^ 4)

/-- The uniform population fourth-moment bound in the cited asymptotic regime.
This bounds averages, and does not require uniformly bounded individual outcomes. -/
def UniformFourthMomentsW3 (P : ℕ → Population) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
    fourthMomentW3 (P n).y1 ≤ C ∧ fourthMomentW3 (P n).y0 ≤ C

/-- The regular finite-population moment regime inferred from Section 3's
cited theorem, with an additional D>0 restriction:
growing populations, interior limiting allocation, bounded fourth moments,
convergent first, second and mixed moments, and positive limiting arm and
sqrt-N contrast variances. All designs are uniform fixed-size designs in
`Population`; outcomes are fixed. The strictly positive contrast limit D
is an extra restriction, not an inherited condition. Normality is supplied
separately for coverage. Sample-variance consistency must be proved. -/
structure RegularMomentsW3 (P : ℕ → Population)
    (p μ1 μ0 v1 v0 c : ℝ) : Prop where
  growing : GrowingPopulations P
  allocation_pos : 0 < p
  allocation_lt_one : p < 1
  allocation : Tendsto (fun n => ((P n).M : ℝ) / (P n).N) atTop (𝓝 p)
  fourth : UniformFourthMomentsW3 P
  mean_treatment : Tendsto (fun n => groupMean univ (P n).y1) atTop (𝓝 μ1)
  mean_control : Tendsto (fun n => groupMean univ (P n).y0) atTop (𝓝 μ0)
  variance_treatment : Tendsto (fun n => popVariance (P n).y1) atTop (𝓝 v1)
  variance_control : Tendsto (fun n => popVariance (P n).y0) atTop (𝓝 v0)
  covariance : Tendsto (fun n => popCovariance (P n).y1 (P n).y0) atTop (𝓝 c)
  variance_treatment_pos : 0 < v1
  variance_control_pos : 0 < v0
  contrast_variance_pos : 0 < (1 - p) / p * v1 + p / (1 - p) * v0 + 2 * c

/-- Existence of finite limiting moments in the cited regular regime. -/
def RegularFamilyW3 (P : ℕ → Population) : Prop :=
  ∃ p μ1 μ0 v1 v0 c : ℝ, RegularMomentsW3 P p μ1 μ0 v1 v0 c

/-- P031-T6; Section 4, p. 369 (PDF p. 5), with Section 3, pp. 367-368.
In regular unbalanced completely randomized finite-population sequences, OLS and
the constant-effects imputation variance can have a probability limit below or
above the actual variance on the N-times-variance scale. A sequence with a
nondegenerate Gaussian limit gives strictly below-nominal limiting normal-interval
coverage for both estimators at every fixed positive critical value. In contrast,
Neyman and HC2 have approximately correct or conservative coverage in the cited
regular regime with its nondegenerate Gaussian limit. The usual measure-theoretic
conditions are assumed; here all row probabilities are finite uniform averages.
The allocation and moment conditions express the cited regular regime.
The strictly positive limiting contrast variance D is an additional
restriction; D=0 coverage is not proved here. Section 4 does not restate
the regime. Sample-variance consistency is proved rather than assumed. -/
def T6CitedRegimeStatement : Prop :=
  (∃ (P : ℕ → Population) (a v : ℝ),
    RegularFamilyW3 P ∧ UnbalancedVarianceLimit P a v ∧ a < v ∧
    StandardizedNormalLimit P ∧ ∀ z : ℝ, 0 < z →
      ∃ q : ℝ, q < 2 * normalCDF z - 1 ∧
        Tendsto (fun n => coverage (P n) olsEstimator z) atTop (𝓝 q) ∧
        Tendsto (fun n => coverage (P n) ceEstimator z) atTop (𝓝 q)) ∧
  (∃ (P : ℕ → Population) (a v : ℝ),
    RegularFamilyW3 P ∧ UnbalancedVarianceLimit P a v ∧ v < a) ∧
  (∀ (P : ℕ → Population), RegularFamilyW3 P → StandardizedNormalLimit P →
    ∀ z : ℝ, 0 < z →
      ConservativeCoverage P neymanEstimator z ∧
      ConservativeCoverage P hc2Estimator z)

end
end SAP.P031
