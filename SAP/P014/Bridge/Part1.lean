import SAP.P014.Defs
import AronowAudit.P014.P014_LocalRandomization
import AronowAudit.P014.P014_Refutations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P014.Bridge
open scoped BigOperators
noncomputable section

/-- The adapter merely bundles the two validity premises into the audit data. -/
def toAudit {α : Type*} (L : FiniteDistribution α) (h : IsDistribution L) :
    AronowAudit.P014.FiniteLaw α := ⟨L.atoms, L.weight, h.1, h.2⟩

def fromAudit {α : Type*} (L : AronowAudit.P014.FiniteLaw α) : FiniteDistribution α :=
  ⟨L.support, L.mass⟩

theorem fromAudit_valid {α : Type*} (L : AronowAudit.P014.FiniteLaw α) :
    IsDistribution (fromAudit L) := ⟨L.positive, L.total⟩

theorem roundtrip {α : Type*} (L : FiniteDistribution α) (h : IsDistribution L) :
    fromAudit (toAudit L h) = L := rfl

theorem expectation_eq {α : Type*} (L : AronowAudit.P014.FiniteLaw α) :
    expectation (fromAudit L) = L.expect := rfl

theorem probability_eq {α : Type*} (L : AronowAudit.P014.FiniteLaw α) :
    probability (fromAudit L) = L.prob := rfl

theorem pushforward_eq {α β : Type*} (L : AronowAudit.P014.FiniteLaw α) (f : α → β) :
    pushforward (fromAudit L) f = fromAudit (L.map f) := rfl

theorem armAssignments_eq {N : ℕ} (L : AronowAudit.P014.FiniteLaw (TreatmentVector N)) :
    armAssignments (fromAudit L) = AronowAudit.P014.armSupport L := rfl

theorem armProbability_eq {N : ℕ} (L : AronowAudit.P014.FiniteLaw (TreatmentVector N)) :
    armProbability (fromAudit L) = AronowAudit.P014.armMass L := rfl

theorem armMoment_eq {N : ℕ} (L : AronowAudit.P014.FiniteLaw (TreatmentVector N)) :
    armMoment (fromAudit L) = AronowAudit.P014.weightedNumerator L := rfl

theorem supportAverage_eq {N : ℕ} (L : AronowAudit.P014.FiniteLaw (TreatmentVector N)) :
    supportAverage (fromAudit L) = AronowAudit.P014.printedMean L := rfl

theorem conditionalAverage_eq {N : ℕ} (L : AronowAudit.P014.FiniteLaw (TreatmentVector N)) :
    conditionalAverage (fromAudit L) = AronowAudit.P014.weightedMean L := rfl

theorem contrast_eq : @windowContrast = @AronowAudit.P014.windowContrast := rfl
theorem assignment_eq : @thresholdAssignment = @AronowAudit.P014.threshold := rfl
theorem inside_eq : insideWindow = AronowAudit.P014.inWindow := rfl
theorem subjects_eq : @windowSubjects = @AronowAudit.P014.windowSet := rfl
theorem cdf_eq : @windowCDF = @AronowAudit.P014.empiricalCDF := rfl
theorem size_eq : @armSize = @AronowAudit.P014.armCount := rfl
theorem total_eq : @observedArmTotal = @AronowAudit.P014.armTotal := rfl
theorem estimator_eq : @differenceOfMeans = @AronowAudit.P014.differenceInMeans := rfl

theorem uniform_eq {N : ℕ} (L : AronowAudit.P014.FiniteLaw (TreatmentVector N)) :
    ConditionallyUniform (fromAudit L) = AronowAudit.P014.ConditionalUniform L := rfl

theorem noninterference_eq : @Noninterfering = @AronowAudit.P014.NoInterference := rfl

theorem printedLocal_eq {Ω : Type*} {N : ℕ} (L : AronowAudit.P014.FiniteLaw Ω) :
    @PrintedLocalConditions Ω N (fromAudit L) = @AronowAudit.P014.PrintedLocal Ω N L := rfl

theorem generalLocal_eq : @CorrectedLocalConditions = @AronowAudit.P014.CorrectedLocal := rfl
theorem event_eq : @eventProbability = @AronowAudit.P014.eventProb := rfl

theorem otherMean_eq {N : ℕ} (L : AronowAudit.P014.FiniteLaw (TreatmentVector N)) :
    otherSubjectsAverage (fromAudit L) = AronowAudit.P014.hhMean L := rfl

theorem direct_eq {N : ℕ} (L : AronowAudit.P014.FiniteLaw (TreatmentVector N)) :
    directEffect (fromAudit L) = AronowAudit.P014.hhDirect L := rfl

theorem six_eq : uniformSix = fromAudit AronowAudit.P014.sixLaw := rfl
theorem localThree_eq : localThree = AronowAudit.P014.threeWindow := rfl
theorem scores1_eq : scores1 = AronowAudit.P014.witnessX := rfl
theorem scores5_eq : scores5 = AronowAudit.P014.defectiveX := rfl
theorem scores9_eq : scores9 = AronowAudit.P014.comparisonX := rfl
theorem allocations_eq : allocations = AronowAudit.P014.witnessZ := rfl
theorem outcomes1_eq : outcomes1 = AronowAudit.P014.spilloverAll := rfl
theorem outcomes5_eq : outcomes5 = AronowAudit.P014.noInterferenceOne := rfl
theorem outcomes9_eq : outcomes9 = AronowAudit.P014.spilloverOne := rfl
theorem witnessLaw_eq : assignmentDistribution = fromAudit AronowAudit.P014.witnessLaw := rfl
theorem extendedLaw_eq : extendedDistribution = fromAudit AronowAudit.P014.extendedLaw := rfl
theorem extendedScores_eq : extendedScores = AronowAudit.P014.extendedX := rfl

/-- The only denominator algebra needed for T2 and T3. -/
theorem fixed_propensity_arms {N : ℕ} (L : FiniteDistribution (TreatmentVector N))
    (hL : IsDistribution L) (S : Finset (Fin N)) (m : ℕ)
    (hm : 0 < m) (hmn : m < S.card)
    (hp : ∀ i ∈ S, armProbability L i true = (m : ℝ) / S.card) :
    (∀ i ∈ S, armProbability L i false = ((S.card : ℝ) - m) / S.card) ∧ PositiveArms L S := by
  have hn : (0 : ℝ) < S.card := by exact_mod_cast lt_trans hm hmn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn' : (m : ℝ) < S.card := by exact_mod_cast hmn
  have hf : ∀ i ∈ S, armProbability L i false = ((S.card : ℝ) - m) / S.card := by
    intro i hi
    have he := AronowAudit.P014.armMasses_add (toAudit L hL) i
    change armProbability L i true + armProbability L i false = 1 at he
    rw [hp i hi] at he
    rw [sub_div, div_self hn.ne']
    linarith
  refine ⟨hf, ?_⟩
  intro i hi a
  cases a
  · rw [hf i hi]; exact div_pos (sub_pos.mpr hmn') hn
  · rw [hp i hi]; exact div_pos hm' hn

theorem interior_arms {N : ℕ} (L : FiniteDistribution (TreatmentVector N))
    (hL : IsDistribution L) (S : Finset (Fin N))
    (hp : ∀ i ∈ S, 0 < armProbability L i true ∧ armProbability L i true < 1) :
    PositiveArms L S := by
  intro i hi a
  cases a
  · have he := AronowAudit.P014.armMasses_add (toAudit L hL) i
    change armProbability L i true + armProbability L i false = 1 at he
    linarith [(hp i hi).2]
  · exact (hp i hi).1

end
end SAP.P014.Bridge
