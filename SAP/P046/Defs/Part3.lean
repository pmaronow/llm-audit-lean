import SAP.P046.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

/-- Strict noncoverage probability of the closed printed interval. -/
def strictNoncoverage (M : Study) (n : ℕ) (alpha : ℝ) : ℝ :=
  (sampleLaw M n {a | printedRadius M alpha a < |ht M a - mu M|}).toReal

/-- The concrete continuous-law undercoverage witness and its exact mass. -/
def T1Statement : Prop :=
  ValidStudy IntervalExample.study ∧
  Measure.map W IntervalExample.study.law = unitUniform ∧
  mu IntervalExample.study = 3/5 ∧
  strictNoncoverage IntervalExample.study 100 (1/10000000) =
    (IntervalExample.certifiedNumerator : ℝ) / (100 : ℝ)^100 ∧
  IntervalExample.certifiedNumerator =
    11979291069795625472576722625601454579193931030581441019247695948117336197717708252113744670235734049700195915329948439938976976688794607547282140972800735873954434550061258658968400997158933003 ∧
  (119/1000000000 : ℝ) < strictNoncoverage IntervalExample.study 100 (1/10000000) ∧
  (1/10000000 : ℝ) < 119/1000000000 ∧
  (∑ k ∈ Finset.range 101, ∑ s ∈ Finset.range (k+1),
    if IntervalExample.xiK k * Real.log 20000000 / 200 < ((s : ℝ)-39)^2 / 65^2
      then (1 : ℕ) else 0) = 1946

/-- Failure of the population-centred conditional bound on a positive event. -/
def T2Statement : Prop :=
  ValidStudy ConditionalExample.study ∧
  Measure.map W ConditionalExample.study.law = unitUniform ∧
  mu ConditionalExample.study = 1/2 ∧
  sampleLaw ConditionalExample.study 100 ConditionalExample.E =
    ENNReal.ofReal ((1/2 : ℝ)^100) ∧
  0 < sampleLaw ConditionalExample.study 100 ConditionalExample.E ∧
  (∀ a : Sample 100, xi ConditionalExample.study a = 100/81) ∧
  (∀ a : Sample 100, printedRadius ConditionalExample.study (1/20) a =
    Real.sqrt (Real.log 40 / 162)) ∧
  Real.log 40 / 162 < (1/4 : ℝ) ∧
  Real.sqrt (Real.log 40 / 162) < (1/2 : ℝ) ∧
  2 * Real.exp (-Real.log 40) = (1/20 : ℝ) ∧
  ∀ᵐ a ∂(sampleLaw ConditionalExample.study 100).restrict ConditionalExample.E,
    condExp (sampleCovariateSigma 100) (sampleLaw ConditionalExample.study 100)
      (fun b => if printedRadius ConditionalExample.study (1/20) b ≤
        |ht ConditionalExample.study b - mu ConditionalExample.study|
          then (1 : ℝ) else 0) a = 1 ∧ (1 : ℝ) > 1/20

/-- Corrected population coverage, its width rate, and the known-bound alternative. -/
def T3Statement : Prop := ∀ (M : Study), ValidStudy M →
  (∀ (alpha : ℝ), 0 < alpha ∧ alpha < 1 →
    (∀ n : ℕ, 0 < n →
      tailProb M (ht M) (correctedRadius M alpha (n := n)) ≤ alpha) ∧
    (∀ n : ℕ, 0 < n → ∀ᵐ a ∂sampleLaw M n,
      correctedRadius M alpha a <
        (M.delta⁻¹+1) * Real.sqrt (Real.log (4/alpha)/(2*n))) ∧
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ᵐ a ∂sampleLaw M n,
      2 * correctedRadius M alpha a ≤ C / Real.sqrt n) ∧
  (∀ (b : ℝ), 0 < b → (∀ᵐ o ∂M.law, b ≤ M.pi (W o)) →
    ∀ (n : ℕ), 0 < n → ∀ (alpha : ℝ), 0 < alpha ∧ alpha < 1 →
      tailProb M (ht M)
        (fun _ : Sample n => b⁻¹ * Real.sqrt (Real.log (2 / alpha) / (2 * n))) ≤ alpha)

/-- The explicit balanced empirical-fit witness with reversed efficiency ordering. -/
def T4Statement : Prop :=
  ValidStudy RegressionExample.study ∧
  Measure.map W RegressionExample.study.law = unitUniform ∧
  mu RegressionExample.study = 1/20 ∧
  Balanced RegressionExample.fits ∧
  (∀ j, L2InProbability RegressionExample.study RegressionExample.fits j
    (RegressionExample.prediction 0)) ∧
  (∀ n j, ∀ᵐ a ∂sampleLaw RegressionExample.study n, ∀ theta,
    empiricalRisk RegressionExample.study
      (Finset.univ.filter (fun i => (RegressionExample.fits n).fold i ≠ j)) a
      (RegressionExample.prediction 0) ≤
    empiricalRisk RegressionExample.study
      (Finset.univ.filter (fun i => (RegressionExample.fits n).fold i ≠ j)) a
      (RegressionExample.prediction theta)) ∧
  (∀ n : ℕ, 0 < n →
    (∫ a, ht RegressionExample.study a ∂sampleLaw RegressionExample.study n) =
      mu RegressionExample.study ∧
    (∫ a, adjusted RegressionExample.study (RegressionExample.fits n) a
      ∂sampleLaw RegressionExample.study n) = mu RegressionExample.study ∧
    variance (ht RegressionExample.study (n := n)) (sampleLaw RegressionExample.study n) =
      79/(400*n) ∧
    variance (adjusted RegressionExample.study (RegressionExample.fits n))
      (sampleLaw RegressionExample.study n) = 169/(400*n)) ∧
  (∀ (n : ℕ) (a : Sample n), adjusted RegressionExample.study (RegressionExample.fits n) a =
    fixedAdjusted RegressionExample.study (RegressionExample.prediction 0) a) ∧
  NormalLimit RegressionExample.study (fun _ => ht RegressionExample.study) (79/400) ∧
  NormalLimit RegressionExample.study
    (fun n => adjusted RegressionExample.study (RegressionExample.fits n)) (169/400) ∧
  (79/400 : ℝ) < 169/400 ∧
  (169/400 : ℝ) - 79/400 = 9/40 ∧
  (169/400 : ℝ) / (79/400) = 169/79 ∧
  (∀ theta, weightedNormSq RegressionExample.study (RegressionExample.prediction theta) =
    3/8 + theta^2/6) ∧
  risk RegressionExample.study (fun _ => 0) = 3/20 ∧
  risk RegressionExample.study (RegressionExample.prediction 0) = 3/8

end
end SAP.P046
