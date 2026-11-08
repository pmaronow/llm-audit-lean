import SAP.P031.Defs.WholeW2
import SAP.P031.Bridge
import SAP.P031.WH.W2.Tools
import AronowAudit.Shared.MapTailB.PermutationArray

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031.WH.W2

/-! This blueprint assembles the cited-regime positive candidate under D>0.
Its seven proposition leaves still require separately compiled proofs. -/

open scoped BigOperators Matrix Topology
open Filter Finset MeasureTheory ProbabilityTheory

noncomputable section

/-- The first M positions of a uniform permutation give a uniform M-subset. -/
def permutationTreatedW2 (Q : Population) (π : Equiv.Perm (Fin Q.N)) :
    Finset (Fin Q.N) :=
  ((univ : Finset (Fin Q.N)).filter (fun i => i.val < Q.M)).image π

/-- A doubly centered permutation array whose permutation sum is the
actual-variance standardized treatment contrast. Positivity of the actual
variance is required wherever its normalization is used. -/
def contrastArrayW2 (Q : Population) : Matrix (Fin Q.N) (Fin Q.N) ℝ :=
  fun i j =>
    ((if i.val < Q.M then 1 else 0) - (Q.M : ℝ) / Q.N) *
      ((Q.y1 j - groupMean univ Q.y1) / Q.M +
        (Q.y0 j - groupMean univ Q.y0) / ((Q.N : ℝ) - Q.M)) /
      Real.sqrt (trueVariance Q)

/-- Uniform complete randomization is the pushforward of a uniform
permutation by taking its first M entries. Prove by equal fiber counts
M! (N-M)! (or by permutation transitivity and invariance of the finite
average). This is finite counting, with no independence assumption.
Estimated proof size: 120-220 lines. -/
def T5_L1 : Prop :=
  ∀ (Q : Population) (f : Finset (Fin Q.N) → ℝ),
    expectation Q.M f =
      (∑ π : Equiv.Perm (Fin Q.N), f (permutationTreatedW2 Q π)) /
        (Fintype.card (Equiv.Perm (Fin Q.N)) : ℝ)

/-- Algebraic reduction to a normalized permutation array. Sum centered
outcomes and centered treatment-position indicators to obtain zero row
and column sums. Expand the sum of squares and use the proved
randomization_variance_alternative to get energy N-1. Splitting a
permutation into the first M positions and the complement gives its
standardized contrast. All divisions are guarded by the Population
certificates and the positive true-variance premise.
Estimated proof size: 220-350 lines. -/
def T5_L2 : Prop :=
  ∀ Q : Population, 0 < trueVariance Q →
    (∀ i, ∑ j, contrastArrayW2 Q i j = 0) ∧
    (∀ j, ∑ i, contrastArrayW2 Q i j = 0) ∧
    (∑ i, ∑ j, (contrastArrayW2 Q i j) ^ 2) = (Q.N : ℝ) - 1 ∧
    ∀ π : Equiv.Perm (Fin Q.N),
      (pointEstimate Q (permutationTreatedW2 Q π) - populationEffect Q) /
        Real.sqrt (trueVariance Q) = ∑ i, contrastArrayW2 Q i (π i)

/-- The maximal normalized permutation-array entry vanishes in the cited
fourth-moment regime. Use scaled_true_variance_limit and the positive
contrast limit. The fourth-moment bound gives max |y| = O(N^(1/4));
centering costs a factor two, the allocation denominators are of order N,
and sqrt(V) is of order N^(-1/2). Thus entries are O(N^(-1/4)). One may
use two nested square roots instead of real powers. Choose a finite
maximum for beta, or the explicit bound described above.
Estimated proof size: 180-300 lines. -/
def T5_L3 : Prop :=
  ∀ (P : ℕ → Population) (p μ1 μ0 v1 v0 c : ℝ),
    RegularRegimeW2 P p μ1 μ0 v1 v0 c →
    ∃ β : ℕ → ℝ, Tendsto β atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ i j, |contrastArrayW2 (P n) i j| ≤ β n

/-- Weak convergence of finite-design laws to a standard Gaussian implies
CDF convergence at every real threshold. Package each uniform finite
assignment law as a ProbabilityMeasure, use the bounded-continuous
integral criterion and the portmanteau theorem for Iic x; Gaussian
singletons have zero measure. Finite sums need no integrability premise;
bounded continuous functions are integrable under the Gaussian law.
Estimated proof size: 100-200 lines. -/
def T5_L4 : Prop :=
  ∀ (P : ℕ → Population) (X : VarianceEstimator),
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => expectation (P n).M (fun s => f (X (P n) s)))
        atTop (𝓝 (∫ x, f x ∂gaussianReal 0 1))) →
    ∀ x : ℝ, Tendsto (fun n => eventProbability (P n) (fun s => X (P n) s ≤ x))
      atTop (𝓝 (normalCDF x))

/-- Both sample arm variances converge to their divisor-N population
variances under the cited fourth-moment conditions. Apply the exact
without-replacement sample-mean second-moment identity to y and y^2;
bounded fourth moments bound the required second moments. Chebyshev
gives convergence of the raw first and second sample moments. Expand
sampleVariance with group_sse_raw, and use growing arm sizes. For the
control arm use expectation_compl. Alternatively transport the proved
P053 fourth-moment SRS variance-consistency theorem.
Estimated proof size: 220-350 lines. -/
def T5_L5 : Prop :=
  ∀ (P : ℕ → Population) (p μ1 μ0 v1 v0 c : ℝ),
    RegularRegimeW2 P p μ1 μ0 v1 v0 c → ArmSecondMomentsConverge P

/-- Relative equivalence preserves a scaled probability limit, including
zero reference estimates. Bound the scaled reference by |b|+1 off its
vanishing error event, then bound the scaled difference by eta(|b|+1)
off the relative-error event. A union bound at eta chosen from epsilon
proves the result. No independence is used.
Estimated proof size: 80-140 lines. -/
def T5_L6 : Prop :=
  ∀ (P : ℕ → Population) (A B : VarianceEstimator) (b : ℝ),
    FirstOrderEquivalent P A B →
    ConvergesInProbability P (fun Q s => (Q.N : ℝ) * B Q s) b →
    ConvergesInProbability P (fun Q s => (Q.N : ℝ) * A Q s) b

/-- Gaussian approximation plus concentration of the variance ratio at a
finite constant c >= 1 gives conservative feasible normal coverage.
For 0<t<z, use the half-open event -t<Z<=t for the standardized contrast Z.
Its probability is exactly F_n(t)-F_n(-t), which converges to 2 Phi(t)-1;
this avoids any finite-law endpoint assumption. On the positive-variance
tail, this event is contained in coverage outside {Vhat/V < (t/z)^2}.
That exceptional probability vanishes by ratio concentration. Let t
increase to z using Gaussian continuity. Positive actual variance is
supplied eventually by StandardizedNormalLimit. This proves the
eventual-epsilon form of the limit-inferior bound. The proposition is
unchanged from the first submission.
Estimated proof size: 160-280 lines. -/
def T5_L7 : Prop :=
  ∀ (P : ℕ → Population) (A : VarianceEstimator) (c : ℝ),
    StandardizedNormalLimit P → 1 ≤ c →
    ConvergesInProbability P (fun Q s => A Q s / trueVariance Q) c →
    ∀ z : ℝ, 0 < z → ConservativeCoverage P A z

/-- The proved general permutation-array CLT supplies the only central
limit theorem used here. The leaves supply its finite-design reduction,
entry bound, and conversion from weak convergence to CDF convergence. -/
theorem normalLimitW2 (h1 : T5_L1) (h2 : T5_L2) (h3 : T5_L3) (h4 : T5_L4)
    (P : ℕ → Population) (p μ1 μ0 v1 v0 c : ℝ)
    (h : RegularRegimeW2 P p μ1 μ0 v1 v0 c) : StandardizedNormalLimit P := by
  have hPos := trueVarianceEventuallyPositiveW2 P p μ1 μ0 v1 v0 c h
  obtain ⟨β, hβ, hBound⟩ := h3 P p μ1 μ0 v1 v0 c h
  have hArray : ∀ᶠ n in atTop, 2 ≤ (P n).N ∧
      (∀ i, ∑ j, contrastArrayW2 (P n) i j = 0) ∧
      (∀ j, ∑ i, contrastArrayW2 (P n) i j = 0) ∧
      (∑ i, ∑ j, (contrastArrayW2 (P n) i j) ^ 2) = ((P n).N : ℝ) - 1 ∧
      (∀ i j, |contrastArrayW2 (P n) i j| ≤ β n) := by
    filter_upwards [hPos, hBound] with n hn hb
    obtain ⟨hr, hc, he, _⟩ := h2 (P n) hn
    exact ⟨by have := (populationSizesW2 (P n)).2.2.2; omega, hr, hc, he, hb⟩
  have hCLT := TailB_permutation_array_clt (fun n => (P n).N) h.growingW2
    (fun n => contrastArrayW2 (P n)) β hβ hArray
  refine ⟨hPos, ?_⟩
  apply h4 P (fun Q s =>
    (pointEstimate Q s - populationEffect Q) / Real.sqrt (trueVariance Q))
  intro f
  apply (hCLT f).congr'
  filter_upwards [hPos] with n hn
  symm
  rw [h1 (P n)]
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  rw [(h2 (P n) hn).2.2.2 π]

/-- The seven new leaves suffice for the restricted positive statement under D>0.
Finite bias, exact HC2 equality, vanishing leverages, deterministic variance
limits, probability-limit arithmetic, and the conservative comparison are
proved here or in Tools from existing proved project results. -/
theorem T5_assembly (h1 : T5_L1) (h2 : T5_L2) (h3 : T5_L3) (h4 : T5_L4)
    (h5 : T5_L5) (h6 : T5_L6) (h7 : T5_L7) : T5CitedRegimeStatement := by
  constructor
  · intro Q
    exact ⟨(finiteBiasW2 Q).1, (finiteBiasW2 Q).2, hc2NeymanW2 Q⟩
  · intro P p μ1 μ0 v1 v0 c h
    have hNormal := normalLimitW2 h1 h2 h3 h4 P p μ1 μ0 v1 v0 c h
    obtain ⟨hHR, hHC1, hHC3⟩ := robustEquivalenceW2 P p μ1 μ0 v1 v0 c h
    have hNeyman := scaledNeymanLimitW2 P p μ1 μ0 v1 v0 c h (h5 P p μ1 μ0 v1 v0 c h)
    have hHC2 : ConvergesInProbability P (fun Q s => (Q.N : ℝ) * hc2Estimator Q s)
        (ConservativeVarianceLimitW2 p v1 v0) := by
      apply probabilityCongrW2 P _ _ _ ?_ hNeyman
      intro n s hs
      rw [hc2NeymanW2 (P n) s hs]
    have hScaledHR := h6 P hrEstimator hc2Estimator _ hHR hHC2
    have hScaledHC1 := h6 P hc1Estimator hc2Estimator _ hHC1 hHC2
    have hScaledHC3 := h6 P hc3Estimator hc2Estimator _ hHC3 hHC2
    have hConservative : 1 ≤ ConservativeVarianceLimitW2 p v1 v0 /
        LeadingTrueVarianceW2 p v1 v0 c := by
      apply (le_div_iff₀ h.contrastPositiveW2).mpr
      simpa only [one_mul] using conservativeLimitComparisonW2 P p μ1 μ0 v1 v0 c h
    have hCover : ∀ (A : VarianceEstimator),
        ConvergesInProbability P (fun Q s => (Q.N : ℝ) * A Q s)
          (ConservativeVarianceLimitW2 p v1 v0) →
        ∀ z : ℝ, 0 < z → ConservativeCoverage P A z := by
      intro A hA
      exact h7 P A _ hNormal hConservative
        (estimatorRatioLimitW2 P A p μ1 μ0 v1 v0 c h hA)
    exact ⟨hNormal, hHR, hHC1, hHC3, fun z hz =>
      ⟨hCover neymanEstimator hNeyman z hz, hCover hc2Estimator hHC2 z hz,
        hCover hrEstimator hScaledHR z hz, hCover hc1Estimator hScaledHC1 z hz,
        hCover hc3Estimator hScaledHC3 z hz⟩⟩

end
end SAP.P031.WH.W2
