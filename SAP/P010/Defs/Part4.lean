import SAP.P010.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P010

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical Topology BigOperators

def T1Statement : Prop :=
    Disjoint (sampleInterval preferCount 0) (sampleInterval preferCount 1) ∧
    Disjoint (sampleInterval preferCount 0) (sampleInterval preferCount 2) ∧
    ¬ (∀ a b : Fin 3, ∃ x : ℝ,
      x ∈ sampleInterval preferCount a ∧ x ∈ sampleInterval preferCount b) ∧
    ¬ (∃ x : ℝ, ∀ a : Fin 3, x ∈ sampleInterval preferCount a)


def T2Statement : Prop :=
    ((∀ a : Fin 3, passers a = (![509,356,493] : Fin 3 → ℕ) a) ∧
    (∀ a : Fin 3, trimShare a =
      (![32239072/72978893,10871635/51611456,31403827/72143648] : Fin 3 → ℚ) a) ∧
    (∀ a : Fin 3, keptLower a = (![284,281,278] : Fin 3 → ℕ) a) ∧
    (∀ a : Fin 3, keptUpper a = (![285,282,279] : Fin 3 → ℕ) a) ∧
    (∀ a : Fin 3, sampleBounds preferCount a =
      (![(0,61/285),(87/281,27/47),(56/139,1)] : Fin 3 → ℚ × ℚ) a) ∧
    (∀ a : Fin 3, sampleBounds approveCount a =
      (![(0,64/95),(113/281,2/3),(109/278,1)] : Fin 3 → ℚ × ℚ) a))
    ∧ (∀ (a : Fin 3) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j ≤ passers a),
    (((j : ℚ) / passers a < 1 - trimShare a) ↔ j ≤ keptLower a) ∧
    (((j : ℚ) / passers a > trimShare a) ↔ passers a - keptUpper a < j))
    ∧ ((∀ a : Fin 3, (1/2 : ℝ) ∈ sampleInterval approveCount a) ∧
    (1/2 : ℝ) ∈ sampleInterval preferCount 1 ∧
    (1/2 : ℝ) ∈ sampleInterval preferCount 2 ∧
    (sampleBounds preferCount 0).2 < (sampleBounds preferCount 1).1 ∧
    (sampleBounds preferCount 0).2 < (sampleBounds preferCount 2).1 ∧
    (sampleBounds preferCount 1).1 - (sampleBounds preferCount 0).2 = 7654/80085 ∧
    (sampleBounds preferCount 2).1 - (sampleBounds preferCount 0).2 = 7481/39615 ∧
    (0 : ℚ) < 7654/80085 ∧ (0 : ℚ) < 7481/39615 ∧
    minAlwaysShare = 40739821/77997088 ∧ 0 < minAlwaysShare ∧
    (∀ a : Fin 3, fractionalPreference a =
      (![(0,8745997/40739821),(12614477/40739821,23486112/40739821),
        (16448045/40739821,1)] : Fin 3 → ℚ × ℚ) a) ∧
    (fractionalPreference 1).1 - (fractionalPreference 0).2 = 3868480/40739821 ∧
    (fractionalPreference 2).1 - (fractionalPreference 0).2 = 7702048/40739821 ∧
    (0 : ℚ) < 3868480/40739821 ∧ (0 : ℚ) < 7702048/40739821)


def T8Statement : Prop :=
    ∀ {K d : ℕ} (μ : Measure (Population K d))
    (h : populationAssumptions μ) (hC : μ sameCheck = 1)
    (a : Fin K) (ha : Integrable (potentialOutcome a) μ),
    (check =ᵐ[μ] potentialCheck a) ∧
    IndepFun (fun ω => (potentialOutcome a ω, check ω)) arm μ ∧
    (∀ t, passRate μ t = (μ passed).toReal ∧ 0 < passRate μ t) ∧
    (passed =ᵐ[μ] allPass) ∧
    meanOn μ response (passed ∩ assigned a) =
      meanOn μ (potentialOutcome a) (passed ∩ assigned a) ∧
    meanOn μ (potentialOutcome a) (passed ∩ assigned a) = meanOn μ (potentialOutcome a) passed ∧
    meanOn μ (potentialOutcome a) passed = meanOn μ (potentialOutcome a) allPass


def T11Statement : Prop :=
    (sigmoid (Real.log (1/3)) = (1/4:ℝ) ∧
    sigmoid (Real.log (1/3)+Real.log 9) = (3/4:ℝ) ∧
    (∀ q₀ q₁ : ℝ, 0 < q₀ → q₀ < 1 → 0 < q₁ → q₁ < 1 →
      Real.log q₀+3*Real.log (1-q₀)+3*Real.log q₁+Real.log (1-q₁) ≤
        Real.log (1/4)+3*Real.log (3/4)+3*Real.log (3/4)+Real.log (1/4) ∧
      (Real.log q₀+3*Real.log (1-q₀)+3*Real.log q₁+Real.log (1-q₁) =
        Real.log (1/4)+3*Real.log (3/4)+3*Real.log (3/4)+Real.log (1/4) ↔
        q₀=1/4 ∧ q₁=3/4)))
    ∧ ((∀ x : Fin 2, 0 < originalDistribution x ∧ 0 < replicationDistribution x ∧
      0 < cellPropensity x ∧ cellPropensity x < 1) ∧
    cellPropensity 0 = 1/4 ∧ cellPropensity 1 = 3/4 ∧
    odds (cellPropensity 0) = 1/3 ∧ odds (cellPropensity 1) = 3 ∧
    replicationDistribution 0*odds (cellPropensity 0) = 1/12 ∧
    replicationDistribution 1*odds (cellPropensity 1) = 9/4 ∧
    (∑ x : Fin 2, replicationDistribution x*odds (cellPropensity x)) = 7/3 ∧
    normalizeMass replicationDistribution (fun x => odds (cellPropensity x)) 1 = 27/28 ∧
    normalizeMass replicationDistribution (fun x => odds (cellPropensity x)) 1 ≠ originalDistribution 1 ∧
    (∀ x : Fin 2, normalizeMass replicationDistribution (fun x => reverseOdds (cellPropensity x)) x = originalDistribution x))


def T17Statement : Prop :=
    ∀ {K d : ℕ} (μ : Measure (Population K d))
    (hp : IsProbabilityMeasure μ) (h : randomAssignment μ)
    (hP : ∀ a, 0 < μ (wouldPass a)),
    ∀ a, 0 < (μ (passed ∩ assigned a)).toReal / (μ (assigned a)).toReal


def T18Statement : Prop :=
    ∀ {K d : ℕ} (μ : Measure (Population K d))
    (h : populationAssumptions μ) (hC : μ sameCheck = 1) (a b : Fin K)
    (ha : Integrable (potentialOutcome a) μ)
    (hb : Integrable (potentialOutcome b) μ),
    meanOn μ response (passed ∩ assigned a) -
      meanOn μ response (passed ∩ assigned b) =
    meanOn μ (fun ω => potentialOutcome a ω - potentialOutcome b ω) allPass


def T19Statement : Prop :=
    ∀ {K d : ℕ} (μ : Measure (Population K d))
    (hp : IsProbabilityMeasure μ) (h : randomAssignment μ)
    (a b : Fin K) (ha : Integrable (potentialOutcome a) μ) (hb : Integrable (potentialOutcome b) μ),
    meanOn μ response (assigned a) = ∫ ω, potentialOutcome a ω ∂μ ∧
    meanOn μ response (assigned b) = ∫ ω, potentialOutcome b ω ∂μ ∧
    meanOn μ response (assigned a) - meanOn μ response (assigned b) =
      ∫ ω, (potentialOutcome a ω - potentialOutcome b ω) ∂μ


def T20Statement : Prop :=
    ∀ {K d : ℕ} (μ : Measure (Population K d))
    (hp : IsProbabilityMeasure μ) (h : randomAssignment μ) (hC : μ sameCheck = 1),
    IndepFun check arm μ


def T21Statement : Prop :=
    ∃ μ : Measure (Population 2 1), populationAssumptions μ ∧
    IndepFun check arm μ ∧ 0 < μ allPass ∧
    0 < μ (passed ∩ assigned 1) ∧ 0 < μ (passed ∩ assigned 0) ∧
    Integrable response (μ.restrict (passed ∩ assigned 1)) ∧
    Integrable response (μ.restrict (passed ∩ assigned 0)) ∧
    Integrable (fun ω => potentialOutcome 1 ω - potentialOutcome 0 ω) (μ.restrict allPass) ∧
    meanOn μ response (passed ∩ assigned 1) - meanOn μ response (passed ∩ assigned 0) ≠
      meanOn μ (fun ω => potentialOutcome 1 ω - potentialOutcome 0 ω) allPass


def T22Statement : Prop :=
    ∀ {K d : ℕ} (μ : Measure (Population K d))
    (hp : IsProbabilityMeasure μ) (h : covariateRandomAssignment μ) (hC : μ sameCheck = 1),
    covariateBalance μ


def T23Statement : Prop :=
    ∃ μ : Measure (Population 2 1),
    IsProbabilityMeasure μ ∧ positivePassRates μ ∧ covariateRandomAssignment μ ∧
    covariateBalance μ ∧ 0 < μ (allPass ∩ {ω | features ω = fun _ => 0}) ∧
    0 < μ ((passed ∩ assigned 1) ∩ {ω | features ω = fun _ => 0}) ∧
    0 < μ ((passed ∩ assigned 0) ∩ {ω | features ω = fun _ => 0}) ∧
    Integrable response (μ.restrict ((passed ∩ assigned 1) ∩ {ω | features ω = fun _ => 0})) ∧
    Integrable response (μ.restrict ((passed ∩ assigned 0) ∩ {ω | features ω = fun _ => 0})) ∧
    Integrable (fun ω => potentialOutcome 1 ω - potentialOutcome 0 ω)
      (μ.restrict (allPass ∩ {ω | features ω = fun _ => 0})) ∧
    meanOn μ response ((passed ∩ assigned 1) ∩ {ω | features ω = fun _ => 0}) -
      meanOn μ response ((passed ∩ assigned 0) ∩ {ω | features ω = fun _ => 0}) ≠
      meanOn μ (fun ω => potentialOutcome 1 ω - potentialOutcome 0 ω)
        (allPass ∩ {ω | features ω = fun _ => 0})



/-- Corrected transport, including Bayes' rule and scale cancellation.
The printed-odds clause applies when its squared-density ratio is integrable.
No claim about an infinite total weighted mass is included. -/
def T12Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (ν : Measure Ω) (π : ℝ) (fR fO : Ω → ℝ),
    0 < π → π < 1 →
    (∀ᵐ x ∂ν, 0 < fR x) → (∀ᵐ x ∂ν, 0 < fO x) →
    Integrable fR ν → Integrable fO ν →
    (∫ x, fR x ∂ν) = 1 → (∫ x, fO x ∂ν) = 1 →
    (∀ᵐ x ∂ν,
      0 < propensity π (fR x) (fO x) ∧ propensity π (fR x) (fO x) < 1 ∧
      odds (propensity π (fR x) (fO x)) = π/(1-π)*(fR x/fO x) ∧
      fO x/fR x = π/(1-π)*reverseOdds (propensity π (fR x) (fO x))) ∧
    (∫ x, fR x*reverseOdds (propensity π (fR x) (fO x)) ∂ν) = (1-π)/π ∧
    ((fun x => normalizeDensity ν fR
      (fun u => reverseOdds (propensity π (fR u) (fO u))) x) =ᵐ[ν] fO) ∧
    (∀ c : ℝ, 0 < c →
      (fun x => normalizeDensity ν fR
        (fun u => c*reverseOdds (propensity π (fR u) (fO u))) x) =ᵐ[ν] fO) ∧
    (Integrable (fun x => (fR x)^2/fO x) ν →
      0 < (∫ x, (fR x)^2/fO x ∂ν) ∧
      ((fun x => normalizeDensity ν fR
        (fun u => odds (propensity π (fR u) (fO u))) x) =ᵐ[ν]
        (fun x => (fR x)^2/fO x / ∫ u, (fR u)^2/fO u ∂ν)) ∧
      (((fun x => normalizeDensity ν fR
        (fun u => odds (propensity π (fR u) (fO u))) x) =ᵐ[ν] fO) ↔ fR =ᵐ[ν] fO))


end SAP.P010
