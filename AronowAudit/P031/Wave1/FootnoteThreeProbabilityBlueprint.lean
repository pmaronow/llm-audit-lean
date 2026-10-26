import AronowAudit.P031.P031_Variance

/-!
# P031-T11: corrected footnote 3, stochastic clauses

Corrected footnote 3 (p. 369) with explicit conditions: `N → ∞`,
`M/N → p ∈ (0,1)`, and convergent population variances and covariance.
Uniformly bounded potential outcomes imply consistency of both centred arm
sample variances. This sample condition (or bounded outcomes) gives
`N V̂_OLS →p v1/(1-p) + v0/p` and, when the limiting leading true variance
`D` is positive, `V̂_OLS / V →p U/D`, where `U = v1/(1-p) + v0/p`.
All probabilities are the rows' actual finite uniform designs; no common
probability space is used.
-/

namespace AronowAudit.P031.Wave1.FootnoteThreeProbability
noncomputable section
open scoped BigOperators Matrix Topology
open Filter

/-- Sample-variance consistency and the OLS probability limits for corrected footnote 3. -/
def Target : Prop :=
  ∀ (P : ℕ → Population), GrowingPopulations P →
    ∀ (p v1 v0 c : ℝ), 0 < p → p < 1 →
    Tendsto (fun n => ((P n).M : ℝ) / (P n).N) atTop (nhds p) →
    Tendsto (fun n => popVariance (P n).y1) atTop (nhds v1) →
    Tendsto (fun n => popVariance (P n).y0) atTop (nhds v0) →
    Tendsto (fun n => popCovariance (P n).y1 (P n).y0) atTop (nhds c) →
    (UniformlyBoundedOutcomes P → ArmSecondMomentsConverge P) ∧
    ((ArmSecondMomentsConverge P ∨ UniformlyBoundedOutcomes P) →
      ConvergesInProbability P (fun Q s => (Q.N : ℝ) * olsEstimator Q s)
        (v1 / (1 - p) + v0 / p) ∧
      (0 < (1 - p) / p * v1 + p / (1 - p) * v0 + 2 * c →
        ConvergesInProbability P (fun Q s => olsEstimator Q s / trueVariance Q)
          ((v1 / (1 - p) + v0 / p) / ((1 - p) / p * v1 + p / (1 - p) * v0 + 2 * c))))

/-- Deterministic weight of the treated sample variance in `N V̂_OLS`. -/
def olsWeightT (Q : Population) : ℝ :=
  (Q.N : ℝ) / ((Q.N : ℝ) - 2) * (1 / (Q.M : ℝ) + 1 / ((Q.N : ℝ) - Q.M)) * ((Q.M : ℝ) - 1)

/-- Deterministic weight of the control sample variance in `N V̂_OLS`. -/
def olsWeightC (Q : Population) : ℝ :=
  (Q.N : ℝ) / ((Q.N : ℝ) - 2) * (1 / (Q.M : ℝ) + 1 / ((Q.N : ℝ) - Q.M)) *
    (((Q.N : ℝ) - Q.M) - 1)

/-! ## Auxiliary statements -/

/-- Pointwise bound on the centred sample-variance error of one size-`M` sample:
`|s²-σ²| ≤ 2|ν̂-ν| + 4B|μ̂-μ| + B²/(M-1)` (exact identity
`s²-σ² = M/(M-1)((ν̂-ν)-(μ̂²-μ²)) + σ²/(M-1)`, `group_sse_raw`, `pop_variance_raw`,
`bounded_population_variance`). -/
def SampleVariancePointwise : Prop :=
  ∀ (N M : ℕ) (v : Fin N → ℝ) (B : ℝ) (s : Finset (Fin N)), 2 ≤ M → s.card = M → 0 ≤ B →
    (∀ i, |v i| ≤ B) →
    |sampleVariance s v - popVariance v| ≤
      2 * |groupMean s (fun i => v i ^ 2) - groupMean Finset.univ (fun i => v i ^ 2)| +
        4 * B * |groupMean s v - groupMean Finset.univ v| + B ^ 2 / ((M : ℝ) - 1)

/-- `E|X| ≤ √(E X²)` for the uniform size-`M` design (finite Cauchy–Schwarz). -/
def ExpectationAbsSqrt : Prop :=
  ∀ (N M : ℕ) (f : Finset (Fin N) → ℝ), M ≤ N →
    expectation M (fun s => |f s|) ≤ Real.sqrt (expectation M (fun s => f s ^ 2))

/-- Finite row-probability calculus for the P031 `eventProbability`: nonnegativity,
monotonicity on the assignment set, union bound and complement. -/
def EventCalculus : Prop :=
  ∀ Q : Population,
    (∀ E : Finset (Fin Q.N) → Prop, 0 ≤ eventProbability Q E) ∧
    (∀ (E F : Finset (Fin Q.N) → Prop),
      (∀ s ∈ (Finset.univ : Finset (Fin Q.N)).powersetCard Q.M, E s → F s) →
      eventProbability Q E ≤ eventProbability Q F) ∧
    (∀ (E F : Finset (Fin Q.N) → Prop),
      eventProbability Q (fun s => E s ∨ F s) ≤ eventProbability Q E + eventProbability Q F) ∧
    (∀ E : Finset (Fin Q.N) → Prop,
      eventProbability Q (fun s => ¬ E s) = 1 - eventProbability Q E)

/-- Bounded centred sample-variance L1 bound:
`E|s² - σ²| ≤ 6B²√f + B²/(m-1)`, `f = (N-m)/(m(N-1))`, for the uniform size-`m` design.
The proof uses the exact identity
`s²-σ² = m/(m-1)((ν̂-ν)-(μ̂²-μ²)) + σ²/(m-1)`,
`bounded_raw_sample_moment_errors`, and `E|X| ≤ √(E X²)` for the finite uniform average. -/
def SampleVarianceL1 : Prop :=
  ∀ (N M : ℕ) (v : Fin N → ℝ) (B : ℝ), 2 ≤ M → M ≤ N → 0 ≤ B → (∀ i, |v i| ≤ B) →
    expectation M (fun s : Finset (Fin N) => |sampleVariance s v - popVariance v|) ≤
      6 * B ^ 2 * Real.sqrt (((N : ℝ) - M) / ((M : ℝ) * ((N : ℝ) - 1))) +
        B ^ 2 / ((M : ℝ) - 1)

/-- Bounded outcomes suffice for the sample condition, under growth and interior allocation only. -/
def BoundedArmConsistency : Prop :=
  ∀ (P : ℕ → Population), GrowingPopulations P →
    ∀ p : ℝ, 0 < p → p < 1 →
    Tendsto (fun n => ((P n).M : ℝ) / (P n).N) atTop (nhds p) →
    UniformlyBoundedOutcomes P → ArmSecondMomentsConverge P

/-- Exact assignmentwise identity `N V̂_OLS = A_N s1² + B_N s0²`,
using `residual_sse` and `gramInverse`. -/
def OLSWeightedIdentity : Prop :=
  ∀ (Q : Population) (s : Finset (Fin Q.N)), s ∈ (Finset.univ).powersetCard Q.M →
    (Q.N : ℝ) * olsEstimator Q s =
      olsWeightT Q * sampleVariance s Q.y1 + olsWeightC Q * sampleVariance sᶜ Q.y0

/-- Limits of the two deterministic weights. -/
def OLSWeightLimits : Prop :=
  ∀ (P : ℕ → Population), GrowingPopulations P →
    ∀ p : ℝ, 0 < p → p < 1 →
    Tendsto (fun n => ((P n).M : ℝ) / (P n).N) atTop (nhds p) →
    Tendsto (fun n => olsWeightT (P n)) atTop (nhds (1 / (1 - p))) ∧
    Tendsto (fun n => olsWeightC (P n)) atTop (nhds (1 / p))

/-- Finite-row probability calculus for weighted sums: bounded convergent
deterministic weights times errors tending to zero in row probability,
plus a convergent deterministic term. -/
def WeightedSumLimit : Prop :=
  ∀ (P : ℕ → Population) (F G H : Population → ℝ) (e1 e0 : VarianceEstimator)
    (a b h : ℝ),
    Tendsto (fun n => F (P n)) atTop (nhds a) →
    Tendsto (fun n => G (P n)) atTop (nhds b) →
    Tendsto (fun n => H (P n)) atTop (nhds h) →
    ConvergesInProbability P e1 0 → ConvergesInProbability P e0 0 →
    ConvergesInProbability P (fun Q s => F Q * e1 Q s + G Q * e0 Q s + H Q) h

/-- Ratio with a positive deterministic limit. -/
def RatioLimit : Prop :=
  ∀ (P : ℕ → Population) (X : VarianceEstimator) (D : Population → ℝ) (U D0 : ℝ),
    ConvergesInProbability P X U →
    Tendsto (fun n => D (P n)) atTop (nhds D0) → 0 < D0 →
    ConvergesInProbability P (fun Q s => X Q s / D Q) (U / D0)

/-! ## Implications between auxiliary statements -/

/-- Pointwise sample-variance error bound. -/
def N1 : Prop := SampleVariancePointwise
/-- `E|X| ≤ √(E X²)`. -/
def N2 : Prop := ExpectationAbsSqrt
/-- Combine the pointwise bound and finite Cauchy–Schwarz inequality with
`bounded_raw_sample_moment_errors`. -/
def N3 : Prop := SampleVariancePointwise → ExpectationAbsSqrt → SampleVarianceL1
/-- Treat the treated arm directly and the control arm through `expectation_compl`;
apply Markov's inequality through `probability_limit_of_mean_absolute_error`. -/
def N4 : Prop := SampleVarianceL1 → BoundedArmConsistency
/-- Assignmentwise OLS identity. -/
def N5 : Prop := OLSWeightedIdentity
/-- Weight limits. -/
def N6 : Prop := OLSWeightLimits
/-- Finite row-probability calculus. -/
def N7 : Prop := EventCalculus
/-- Weighted-sum convergence in row probability, two-event union bound. -/
def N8 : Prop := EventCalculus → WeightedSumLimit
/-- Ratio convergence in row probability. -/
def N9 : Prop := EventCalculus → RatioLimit

/-- The auxiliary statements imply the target (with the proved `scaled_true_variance_limit`,
`probability_limit_congr` and `population_sizes`). -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7)
    (h8 : N8) (h9 : N9) : Target := by
  intro P hN p v1 v0 c hp hp1 hAlloc hV1 hV0 hCov
  have hBounded : UniformlyBoundedOutcomes P → ArmSecondMomentsConverge P :=
    h4 (h3 h1 h2) P hN p hp hp1 hAlloc
  refine ⟨hBounded, ?_⟩
  intro hS
  have hArm : ArmSecondMomentsConverge P := hS.elim id hBounded
  obtain ⟨hWT, hWC⟩ := h6 P hN p hp hp1 hAlloc
  have hH : Tendsto (fun n => olsWeightT (P n) * popVariance (P n).y1 +
      olsWeightC (P n) * popVariance (P n).y0) atTop (nhds (v1 / (1 - p) + v0 / p)) := by
    have hl := (hWT.mul hV1).add (hWC.mul hV0)
    have he : 1 / (1 - p) * v1 + 1 / p * v0 = v1 / (1 - p) + v0 / p := by ring
    rw [he] at hl
    exact hl
  have hX := h8 h7 P olsWeightT olsWeightC
    (fun Q => olsWeightT Q * popVariance Q.y1 + olsWeightC Q * popVariance Q.y0)
    (fun Q s => sampleVariance s Q.y1 - popVariance Q.y1)
    (fun Q s => sampleVariance sᶜ Q.y0 - popVariance Q.y0)
    (1 / (1 - p)) (1 / p) (v1 / (1 - p) + v0 / p) hWT hWC hH hArm.1 hArm.2
  have hOLS : ConvergesInProbability P (fun Q s => (Q.N : ℝ) * olsEstimator Q s)
      (v1 / (1 - p) + v0 / p) := by
    apply probability_limit_congr P _ _ hX
    intro n s hs
    rw [h5 (P n) s hs]
    ring
  refine ⟨hOLS, ?_⟩
  intro hD
  have hT := scaled_true_variance_limit P hN p v1 v0 c hp hp1 hAlloc hV1 hV0 hCov
  have hR := h9 h7 P (fun Q s => (Q.N : ℝ) * olsEstimator Q s)
    (fun Q => (Q.N : ℝ) * trueVariance Q) _ _ hOLS hT hD
  apply probability_limit_congr P _ _ hR
  intro n s _
  have hN0 : ((P n).N : ℝ) ≠ 0 := by
    have := (population_sizes (P n)).2.2.2
    have h4' : (4 : ℝ) ≤ ((P n).N : ℝ) := by exact_mod_cast this
    linarith
  exact (mul_div_mul_left _ _ hN0).symm


end
end AronowAudit.P031.Wave1.FootnoteThreeProbability
