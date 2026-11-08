import SAP.P047.Defs
import AronowAudit.P047.P047_Identification
import AronowAudit.P047.Wave1.Impossibility

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace SAP.P047.Bridge

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

/-- Copy the population data and its identifying assumptions. -/
def toProject (L : CausalLaw) : AronowAudit.P047.CausalLaw where
  measure := L.measure
  probability := L.probability
  propensity := L.propensity
  measurable_propensity := L.measurable_propensity
  ignorability := L.ignorability

def fromProject (L : AronowAudit.P047.CausalLaw) : CausalLaw where
  measure := L.measure
  probability := L.probability
  propensity := L.propensity
  measurable_propensity := L.measurable_propensity
  ignorability := L.ignorability

theorem from_to (L : CausalLaw) : fromProject (toProject L) = L := by
  cases L
  rfl

theorem to_from (L : AronowAudit.P047.CausalLaw) : toProject (fromProject L) = L := by
  cases L
  rfl

theorem covariate_eq : covariate = AronowAudit.P047.covariate := rfl

theorem arm_eq : arm = AronowAudit.P047.arm := rfl

theorem potential_eq : potential = AronowAudit.P047.potential := rfl

theorem observed_eq : observed = AronowAudit.P047.observed := rfl

theorem covariateSigma_eq : covariateSigma = AronowAudit.P047.covariateSigma := rfl

theorem armPropensity_eq : armPropensity = AronowAudit.P047.armPropensity := rfl

theorem ignorable_eq : Ignorable = AronowAudit.P047.Ignorable := rfl

theorem boundedOverlap_iff (L : CausalLaw) (B ε : ℝ) :
    BoundedOverlap L B ε ↔ AronowAudit.P047.BoundedOverlap (toProject L) B ε := Iff.rfl

theorem score_eq (L : CausalLaw) : score L = AronowAudit.P047.score (toProject L) := rfl

theorem ate_eq (L : CausalLaw) : ate L = AronowAudit.P047.ate (toProject L) := rfl

theorem treatedMean_eq (L : CausalLaw) :
    treatedMean L = AronowAudit.P047.treatedMean (toProject L) := rfl

theorem sampleLaw_eq (P : Measure UnitData) [IsProbabilityMeasure P] :
    sampleLaw P = AronowAudit.P047.sampleLaw P := rfl

theorem estimator_eq (L : CausalLaw) :
    estimator L = AronowAudit.P047.estimator (toProject L) := rfl

/-- Consistency identifies the potential-outcome contribution with the
observed-data formula, using the credited existing observability identity. -/
theorem treatedScore_eq (L : CausalLaw) :
    treatedScore L = AronowAudit.P047.armIPW (toProject L) true := by
  funext u
  exact (AronowAudit.P047.armIPW_eq_observed (toProject L) true u).symm

theorem treatedEstimator_eq (L : CausalLaw) :
    treatedEstimator L = AronowAudit.P047.treatedEstimator (toProject L) := by
  funext n s
  exact (AronowAudit.P047.treatedEstimator_eq_observed_sum (toProject L) n s).symm

theorem halfWidth_eq : halfWidth = AronowAudit.P047.halfWidth := rfl

theorem confidenceInterval_eq (L : CausalLaw) :
    confidenceInterval L = AronowAudit.P047.confidenceInterval (toProject L) := rfl

theorem treatedHalfWidth_eq : treatedHalfWidth = AronowAudit.P047.treatedHalfWidth := rfl

theorem treatedMeanModel_iff (L : CausalLaw) (ε : ℝ) :
    TreatedMeanModel L ε ↔ AronowAudit.P047.TreatedMeanModel (toProject L) ε := Iff.rfl

/-- Reindexing the population supremum by the two inverse adapters. -/
theorem knownRootRisk_eq (B ε : ℝ) :
    knownRootRisk B ε = AronowAudit.P047.knownRootRisk B ε := by
  funext K
  unfold knownRootRisk AronowAudit.P047.knownRootRisk
  apply congrArg sSup
  apply congrArg (insert (0 : ℝ))
  ext r
  constructor
  · rintro ⟨L, hL, n, hn, hr⟩
    exact ⟨toProject L, hL, n, hn, hr⟩
  · rintro ⟨L, hL, n, hn, hr⟩
    exact ⟨fromProject L, hL, n, hn, hr⟩

theorem uniform01_eq : uniform01 = AronowAudit.P047.uniform01 := rfl

theorem jointIgnorable_iff (L : CausalLaw) :
    JointIgnorable L ↔ AronowAudit.P047.JointIgnorable (toProject L) := Iff.rfl

theorem unknownModel_iff (L : CausalLaw) :
    UnknownModel L ↔ AronowAudit.P047.UnknownModel (toProject L) := Iff.rfl

theorem observedSample_eq : observedSample = AronowAudit.P047.observedSample := rfl

theorem fairBool_eq : fairBool = AronowAudit.P047.fairBool := rfl

theorem baselineLaw_eq : baselineLaw = AronowAudit.P047.baselineLaw := rfl

theorem randRisk_eq {R : Type u} [MeasurableSpace R] (Q : Measure R)
    [IsProbabilityMeasure Q]
    (E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ) (n : ℕ) (η : ℝ) :
    randRisk Q E n η = AronowAudit.P047.Wave1.Impossibility.randRisk Q E n η := by
  unfold randRisk AronowAudit.P047.Wave1.Impossibility.randRisk
  apply congrArg sSup
  apply congrArg (insert (0 : ℝ))
  ext r
  constructor
  · rintro ⟨L, hL, hr⟩
    exact ⟨toProject L, hL, hr⟩
  · rintro ⟨L, hL, hr⟩
    exact ⟨fromProject L, hL, hr⟩

theorem randStrictRisk_eq {R : Type u} [MeasurableSpace R] (Q : Measure R)
    [IsProbabilityMeasure Q]
    (E : (n : ℕ) → ((Fin n → ObservedUnit) × R) → ℝ) (n : ℕ) (η : ℝ) :
    randStrictRisk Q E n η =
      AronowAudit.P047.Wave1.Impossibility.randStrictRisk Q E n η := by
  unfold randStrictRisk AronowAudit.P047.Wave1.Impossibility.randStrictRisk
  apply congrArg sSup
  apply congrArg (insert (0 : ℝ))
  ext r
  constructor
  · rintro ⟨L, hL, hr⟩
    exact ⟨toProject L, hL, hr⟩
  · rintro ⟨L, hL, hr⟩
    exact ⟨fromProject L, hL, hr⟩

theorem randCoverage_eq {R : Type u} [MeasurableSpace R] (Q : Measure R)
    [IsProbabilityMeasure Q]
    (lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal) :
    randCoverage Q lo hi = AronowAudit.P047.Wave1.Impossibility.randCoverage Q lo hi := by
  funext n
  unfold randCoverage AronowAudit.P047.Wave1.Impossibility.randCoverage
  apply congrArg sInf
  apply congrArg (insert (1 : ℝ))
  ext r
  constructor
  · rintro ⟨L, hL, hr⟩
    exact ⟨toProject L, hL, hr⟩
  · rintro ⟨L, hL, hr⟩
    exact ⟨fromProject L, hL, hr⟩

theorem widthProb_eq {R : Type u} [MeasurableSpace R] (Q : Measure R)
    [IsProbabilityMeasure Q]
    (lo hi : (n : ℕ) → ((Fin n → ObservedUnit) × R) → EReal) :
    widthProb Q lo hi = AronowAudit.P047.Wave1.Impossibility.widthProb Q lo hi := rfl

end

end SAP.P047.Bridge
