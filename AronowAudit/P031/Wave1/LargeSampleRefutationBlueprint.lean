import AronowAudit.P031.Wave1.FootnoteThreeProbabilityBlueprint

/-!
# P031-T5: counterexample to the printed large-sample assertions

The target asserts that an explicit growing population sequence satisfies
`StandardizedNormalLimit` and violates HR/HC2 equivalence, and negates
the universal conjunction of three first-order equivalences and five
coverage clauses. The theorem `assemble` derives this target conditional
on the stated auxiliary propositions. No undercoverage theorem is claimed here.

Witness: row `n` has `r = n+1`, `k = 4r²`,
`N = 2^k`, `M = 2`; the `N` units are the `k`-digit binary vectors (`finFunctionFinEquiv`),
`q_i = (Σ_j ±1)/(2r)`, `y1_i = q_i / 2^(2r²)`, `y0 = 0`. The standardized estimator of a
treated pair is `(q_I+q_J)/√2 · √((N-1)/(N-2))`; comparing the distinct-pair design with
independent uniform draws (error `≤ 1/N`) turns it into a normalized sum of `2k` fair
signs, to which Mathlib's iid CLT applies. Ties `q_I = q_J` have probability
`≤ C(2k,k)/4^k + 1/N → 0`, and off ties the HR/HC2 relative error is `1/2 > 1/4`.
-/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- A normally convergent population sequence violating HR/HC2 equivalence,
and the resulting negation of the printed universal conjunction. -/
def Target : Prop :=
  (∃ P : ℕ → Population,
    GrowingPopulations P ∧ StandardizedNormalLimit P ∧
    ¬ FirstOrderEquivalent P hrEstimator hc2Estimator) ∧
  ¬ (∀ P : ℕ → Population,
    GrowingPopulations P → StandardizedNormalLimit P →
    FirstOrderEquivalent P hrEstimator hc2Estimator ∧
    FirstOrderEquivalent P hc1Estimator hc2Estimator ∧
    FirstOrderEquivalent P hc3Estimator hc2Estimator ∧
    ∀ z : ℝ, 0 < z →
      ConservativeCoverage P neymanEstimator z ∧
      ConservativeCoverage P hc2Estimator z ∧
      ConservativeCoverage P hrEstimator z ∧
      ConservativeCoverage P hc1Estimator z ∧
      ConservativeCoverage P hc3Estimator z)

/-! ## The witness population sequence -/

/-- Number of sign coordinates in row `n`: `k = 4 r²`, `r = n+1`. -/
def hcK (n : ℕ) : ℕ := 4 * (n + 1) ^ 2

/-- Population size in row `n`: `N = 2^k`. -/
def hcN (n : ℕ) : ℕ := 2 ^ hcK n

/-- The fair sign of a binary digit. -/
def sgn2 (d : Fin 2) : ℝ := if d = 0 then -1 else 1

/-- The `k` binary digits of unit `i`. -/
def hcDigits (n : ℕ) (i : Fin (hcN n)) : Fin (hcK n) → Fin 2 :=
  (finFunctionFinEquiv (m := 2) (n := hcK n)).symm i

/-- `q_i = (Σ_j sign_ij)/(2r) = (Σ_j sign_ij)/√k`. -/
def hcQ (n : ℕ) (i : Fin (hcN n)) : ℝ :=
  (∑ j, sgn2 (hcDigits n i j)) / (2 * ((n : ℝ) + 1))

theorem hcN_ge (n : ℕ) : 16 ≤ hcN n := by
  unfold hcN hcK
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ (4 * (n + 1) ^ 2) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have h1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos n)
      omega

/-- Row `n` of the witness: `M = 2`, `y1 = q/√N` with `√N = 2^(2r²)`, `y0 = 0`. -/
def hypercubePopulation (n : ℕ) : Population where
  N := hcN n
  M := 2
  y1 := fun i => hcQ n i / (2 : ℝ) ^ (2 * (n + 1) ^ 2)
  y0 := fun _ => 0
  hM := by norm_num
  hMN := by have := hcN_ge n; omega

/-- The fair-coin product measure on `ℕ → Fin 2`. -/
def coinMeasure : Measure (ℕ → Fin 2) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype (Fin 2)).toMeasure)

instance : IsProbabilityMeasure coinMeasure := by
  unfold coinMeasure
  infer_instance

/-! ## Auxiliary statements -/

/-- `N → ∞`. -/
def HypercubeGrowth : Prop := GrowingPopulations hypercubePopulation

/-- Sign orthogonality: `Σ q_i = 0` and `Σ q_i² = N` (mean 0, mean square 1). -/
def HypercubeMoments : Prop :=
  ∀ n : ℕ, (∑ i, hcQ n i) = 0 ∧ (∑ i, hcQ n i ^ 2) = (hcN n : ℝ)

/-- Exact true variance `(N-2)/(2N(N-1))` and zero average effect (via the proved
`randomization_variance_alternative`). -/
def HypercubeTrueVariance : Prop :=
  ∀ n : ℕ,
    trueVariance (hypercubePopulation n) =
      ((hcN n : ℝ) - 2) / (2 * (hcN n : ℝ) * ((hcN n : ℝ) - 1)) ∧
    populationEffect (hypercubePopulation n) = 0

/-- Distinct-pair versus independent-pair comparison for `M = 2`: for a symmetric pair
relation the actual design probability differs from the ordered with-replacement
frequency by at most `1/N`. -/
def PairComparison : Prop :=
  ∀ (Q : Population) (R : Fin Q.N → Fin Q.N → Prop), Q.M = 2 → (∀ i j, R i j → R j i) →
    |eventProbability Q (fun s => ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ R i j) -
      ((Finset.univ.filter (fun ij : Fin Q.N × Fin Q.N => R ij.1 ij.2)).card : ℝ) /
        ((Q.N : ℝ) ^ 2)| ≤ 1 / (Q.N : ℝ)

/-- Independent uniform pairs of hypercube units are uniform `2k`-digit vectors, and
`q_I + q_J` is the sum of their `2k` signs divided by `2r`. -/
def PairCountRademacher : Prop :=
  ∀ (n : ℕ) (E : ℝ → Prop),
    ((Finset.univ.filter (fun ij : Fin (hcN n) × Fin (hcN n) =>
        E (hcQ n ij.1 + hcQ n ij.2))).card : ℝ) =
      ((Finset.univ.filter (fun v : Fin (2 * hcK n) → Fin 2 =>
        E ((∑ j, sgn2 (v j)) / (2 * ((n : ℝ) + 1))))).card : ℝ)

/-- Standard input: the iid central limit theorem for fair signs on the coin product
space (Mathlib `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`, independence of
coordinates `ProbabilityTheory.iIndepFun_infinitePi`, identical laws from
`Measure.infinitePi_map_eval`). -/
def CoinCLTDistribution : Prop :=
  TendstoInDistribution
    (fun (m : ℕ) (ω : ℕ → Fin 2) => (Real.sqrt m)⁻¹ * ∑ j ∈ Finset.range m, sgn2 (ω j))
    atTop (fun z : ℝ => z) (fun _ => coinMeasure) (ProbabilityTheory.gaussianReal 0 1)

/-- CDF form of the coin CLT at every real threshold (Portmanteau
`MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`; the
Gaussian has no atoms, `ProbabilityTheory.nullSingletonClass_gaussianReal`). -/
def CoinCLTMeasure : Prop :=
  ∀ x : ℝ, Tendsto (fun m : ℕ => (coinMeasure
      {ω | (Real.sqrt m)⁻¹ * ∑ j ∈ Finset.range m, sgn2 (ω j) ≤ x}).toReal)
    atTop (nhds (normalCDF x))

/-- Cylinder events of the coin measure are digit counts divided by `2^m`. -/
def CoinCylinderCount : Prop :=
  ∀ (m : ℕ) (x : ℝ),
    (coinMeasure {ω | (Real.sqrt m)⁻¹ * ∑ j ∈ Finset.range m, sgn2 (ω j) ≤ x}).toReal =
      ((Finset.univ.filter (fun v : Fin m → Fin 2 =>
        (Real.sqrt m)⁻¹ * ∑ j, sgn2 (v j) ≤ x)).card : ℝ) / 2 ^ m

/-- Threshold and subsequence transfer for CDF limits (monotone CDFs, limit continuous at
`x`, thresholds `c n * x` with `c n → 1`, comparison error `ε n → 0`). -/
def ThresholdTransfer : Prop :=
  ∀ (F : ℕ → ℝ) (G : ℕ → ℝ → ℝ) (Φ : ℝ → ℝ) (φ : ℕ → ℕ) (c ε : ℕ → ℝ) (x : ℝ),
    (∀ m, Monotone (G m)) → ContinuousAt Φ x →
    (∀ y, Tendsto (fun m => G m y) atTop (nhds (Φ y))) →
    Tendsto φ atTop atTop → Tendsto c atTop (nhds 1) → Tendsto ε atTop (nhds 0) →
    (∀ n, |F n - G (φ n) (c n * x)| ≤ ε n) → Tendsto F atTop (nhds (Φ x))

/-- The exact standardized estimator of a treated pair. -/
def StandardizationIdentity : Prop :=
  ∀ (n : ℕ) (s : Finset (Fin (hypercubePopulation n).N)),
    s ∈ (Finset.univ).powersetCard (hypercubePopulation n).M →
    (pointEstimate (hypercubePopulation n) s - populationEffect (hypercubePopulation n)) /
        Real.sqrt (trueVariance (hypercubePopulation n)) =
      (∑ i ∈ s, hcQ n i) / Real.sqrt 2 * Real.sqrt (((hcN n : ℝ) - 1) / ((hcN n : ℝ) - 2))

/-- Continuity of the standard normal CDF. -/
def NormalCDFContinuous : Prop := ∀ x : ℝ, ContinuousAt normalCDF x

/-- On a treated pair the HR/HC2 relative-error event at `ε = 1/4` is exactly the
non-tie event (proved `two_treated_zero_controls`: `HR = HC2/2`, `HC2 ≥ 0`). -/
def HypercubeErrorEvent : Prop :=
  ∀ (n : ℕ) (s : Finset (Fin (hypercubePopulation n).N)),
    s ∈ (Finset.univ).powersetCard (hypercubePopulation n).M →
    ((1/4 : ℝ) * |hc2Estimator (hypercubePopulation n) s| <
        |hrEstimator (hypercubePopulation n) s - hc2Estimator (hypercubePopulation n) s| ↔
      ¬ ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ hcQ n i = hcQ n j)

/-- Ordered tie pairs: `#{(i,j) : q_i = q_j} = C(2k,k)` (equal digit sums; Vandermonde
`Nat.sum_range_choose_sq`). -/
def TieCount : Prop :=
  ∀ n : ℕ, (Finset.univ.filter (fun ij : Fin (hcN n) × Fin (hcN n) =>
      hcQ n ij.1 = hcQ n ij.2)).card = (2 * hcK n).choose (hcK n)

/-- Central binomial decay `C(2k,k)/4^k ≤ 1/√(k+1)` (induction; the squared step is
`(2k+1)²(k+2) ≤ 4(k+1)³`). -/
def CentralBinomDecay : Prop :=
  ∀ k : ℕ, ((2 * k).choose k : ℝ) / 4 ^ k ≤ 1 / Real.sqrt ((k : ℝ) + 1)

/-- The actual tie probability vanishes. -/
def TieProbabilityVanishes : Prop :=
  Tendsto (fun n => eventProbability (hypercubePopulation n)
    (fun s => ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ hcQ n i = hcQ n j)) atTop (nhds 0)

/-! ## Implications between auxiliary statements -/

/-- Growth of the witness population sizes. -/
def N1 : Prop := HypercubeGrowth
/-- Moments. -/
def N2 : Prop := HypercubeMoments
/-- Exact true variance. -/
def N3 : Prop := HypercubeMoments → HypercubeTrueVariance
/-- Pair-law comparison. -/
def N4 : Prop := PairComparison
/-- Pair count as a Rademacher count. -/
def N5 : Prop := PairCountRademacher
/-- The iid CLT for fair signs, expressed as convergence in distribution. -/
def N6 : Prop := CoinCLTDistribution
/-- CDF form of the coin CLT. -/
def N7 : Prop := CoinCLTDistribution → CoinCLTMeasure
/-- Coin cylinder events as counts. -/
def N8 : Prop := CoinCylinderCount
/-- Threshold transfer. -/
def N9 : Prop := ThresholdTransfer
/-- Standardization identity. -/
def N10 : Prop := HypercubeTrueVariance → StandardizationIdentity
/-- Continuity of the standard normal CDF. -/
def N11 : Prop := NormalCDFContinuous
/-- The full `StandardizedNormalLimit`: positivity from the variance formula;
for each `x` the event is a symmetric pair event, compared with the coin count
at `m = 2k` and threshold `√((N-2)/(N-1)) x`. -/
def N12 : Prop :=
  HypercubeTrueVariance → PairComparison → PairCountRademacher → CoinCLTMeasure →
    CoinCylinderCount → ThresholdTransfer → StandardizationIdentity → NormalCDFContinuous →
    StandardizedNormalLimit hypercubePopulation
/-- HR/HC2 error event. -/
def N13 : Prop := HypercubeErrorEvent
/-- Tie count. -/
def N14 : Prop := TieCount
/-- Central binomial decay. -/
def N15 : Prop := CentralBinomDecay
/-- Tie probability vanishes. -/
def N16 : Prop :=
  FootnoteThreeProbability.EventCalculus → PairComparison → TieCount → CentralBinomDecay →
    TieProbabilityVanishes
/-- The event calculus, the non-tie error identity, and vanishing tie
probability imply failure of HR/HC2 first-order equivalence. -/
def N17 : Prop :=
  FootnoteThreeProbability.EventCalculus → HypercubeErrorEvent → TieProbabilityVanishes →
    ¬ FirstOrderEquivalent hypercubePopulation hrEstimator hc2Estimator

/-- The auxiliary statements imply the target. `hEC` supplies the finite-design
event inequalities (`FootnoteThreeProbability.EventCalculus`). -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7)
    (h8 : N8) (h9 : N9) (h10 : N10) (h11 : N11) (h12 : N12) (h13 : N13) (h14 : N14)
    (h15 : N15) (h16 : N16) (h17 : N17) (hEC : FootnoteThreeProbability.N7) :
    Target := by
  have hV : HypercubeTrueVariance := h3 h2
  have hNormal : StandardizedNormalLimit hypercubePopulation :=
    h12 hV h4 h5 (h7 h6) h8 h9 (h10 hV) h11
  have hFail : ¬ FirstOrderEquivalent hypercubePopulation hrEstimator hc2Estimator :=
    h17 hEC h13 (h16 hEC h4 h14 h15)
  refine ⟨⟨hypercubePopulation, h1, hNormal, hFail⟩, ?_⟩
  intro h
  exact hFail (h hypercubePopulation h1 hNormal).1

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
