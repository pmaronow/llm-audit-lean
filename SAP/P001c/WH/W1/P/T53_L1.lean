import SAP.P001c.WH.W1.Leaves
import AronowAudit.P001.P001_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c.WH.W1.P.T53_L1

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology Classical

noncomputable section

def geomParam : ↑unitInterval := ⟨7 / 8, by norm_num, by norm_num⟩

lemma geomParam_ne_zero : geomParam ≠ 0 := by
  intro h
  have hv := congrArg (fun x : ↑unitInterval => (x : ℝ)) h
  norm_num [geomParam] at hv

lemma geomCoeff_eq_mass (k : ℕ) :
    (1 - (geomParam : ℝ)) ^ k * (geomParam : ℝ) = SAP.P001c.powerTailMass k := by
  norm_num [geomParam, SAP.P001c.powerTailMass, pow_succ]
  ring

lemma value_nonneg (k : ℕ) : 0 ≤ SAP.P001c.powerTailValue k := by
  simp [SAP.P001c.powerTailValue]

lemma value_sq (k : ℕ) :
    (SAP.P001c.powerTailValue k) ^ 2 = (2 : ℝ) ^ (2 * k) := by
  dsimp [SAP.P001c.powerTailValue]
  calc
    ((2 : ℝ)^k) ^ 2 = (2 : ℝ)^(k * 2) := by rw [← pow_mul]
    _ = (2 : ℝ)^(2 * k) := by congr 1; omega

lemma atom_mass (k : ℕ) :
    SAP.P001c.probability SAP.P001c.powerTailLaw {j | SAP.P001c.powerTailValue j = (2 : ℝ)^k} =
      SAP.P001c.powerTailMass k := by
  have hset : {j : ℕ | SAP.P001c.powerTailValue j = (2 : ℝ)^k} = {k} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, SAP.P001c.powerTailValue]
    constructor
    · intro h
      exact (pow_right_injective₀ (by norm_num : 0 < (2 : ℝ)) (by norm_num : (2 : ℝ) ≠ 1)) h
    · rintro rfl
      rfl
  change (SAP.P001c.powerTailLaw {j | SAP.P001c.powerTailValue j = (2 : ℝ)^k}).toReal = _
  rw [hset]
  change (geometricMeasure geomParam).real {k} = _
  rw [geometricMeasure_real_singleton geomParam_ne_zero]
  exact geomCoeff_eq_mass k

lemma value_integrable :
    Integrable SAP.P001c.powerTailValue SAP.P001c.powerTailLaw := by
  obtain ⟨_, _, hs1, _, _, _, _, _⟩ :=
    AronowAudit.P001.squares_missing_wlln_hypothesis
  change Integrable SAP.P001c.powerTailValue (geometricMeasure geomParam)
  rw [integrable_geometricMeasure_iff geomParam_ne_zero]
  convert hs1 using 1 with k
  funext k
  rw [geomCoeff_eq_mass k, SAP.P001c.Bridge.powerTailMass_eq]
  simp [SAP.P001c.powerTailValue, abs_of_nonneg (pow_nonneg (by norm_num) k)]
  ring

lemma value_sq_integrable :
    Integrable (fun k => (SAP.P001c.powerTailValue k)^2) SAP.P001c.powerTailLaw := by
  obtain ⟨_, _, _, hs2, _, _, _, _⟩ :=
    AronowAudit.P001.squares_missing_wlln_hypothesis
  change Integrable (fun k => (SAP.P001c.powerTailValue k)^2) (geometricMeasure geomParam)
  rw [integrable_geometricMeasure_iff geomParam_ne_zero]
  convert hs2 using 1 with k
  funext k
  rw [geomCoeff_eq_mass k, SAP.P001c.Bridge.powerTailMass_eq, value_sq]
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _)]
  ring

lemma value_memLp :
    MemLp SAP.P001c.powerTailValue 2 SAP.P001c.powerTailLaw := by
  apply (memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).2
  exact value_sq_integrable

lemma value_expectation :
    SAP.P001c.expectation SAP.P001c.powerTailLaw SAP.P001c.powerTailValue = 7 / 6 := by
  obtain ⟨_, _, _, _, hsum, _, _, _⟩ :=
    AronowAudit.P001.squares_missing_wlln_hypothesis
  change (∫ k, SAP.P001c.powerTailValue k ∂geometricMeasure geomParam) = 7 / 6
  rw [integral_geometricMeasure' geomParam_ne_zero value_integrable]
  calc
    (∑' k : ℕ, ((1 - (geomParam : ℝ)) ^ k * (geomParam : ℝ)) •
        SAP.P001c.powerTailValue k) =
        ∑' k : ℕ, (2 : ℝ)^k * AronowAudit.P001.heavyMomentMass k := by
      congr 1
      funext k
      rw [smul_eq_mul, geomCoeff_eq_mass k, SAP.P001c.Bridge.powerTailMass_eq]
      simp [SAP.P001c.powerTailValue]
      ring
    _ = 7 / 6 := hsum

lemma value_sq_expectation :
    SAP.P001c.expectation SAP.P001c.powerTailLaw
      (fun k => (SAP.P001c.powerTailValue k)^2) = 7 / 4 := by
  obtain ⟨_, _, _, _, _, hsum, _, _⟩ :=
    AronowAudit.P001.squares_missing_wlln_hypothesis
  change (∫ k, (SAP.P001c.powerTailValue k)^2 ∂geometricMeasure geomParam) = 7 / 4
  rw [integral_geometricMeasure' geomParam_ne_zero value_sq_integrable]
  calc
    (∑' k : ℕ, ((1 - (geomParam : ℝ)) ^ k * (geomParam : ℝ)) •
        (SAP.P001c.powerTailValue k)^2) =
        ∑' k : ℕ, (2 : ℝ)^(2*k) * AronowAudit.P001.heavyMomentMass k := by
      congr 1
      funext k
      rw [smul_eq_mul, geomCoeff_eq_mass k, SAP.P001c.Bridge.powerTailMass_eq, value_sq]
      ring
    _ = 7 / 4 := hsum

end
end SAP.P001c.WH.W1.P.T53_L1

open SAP.P001c.WH.W1.P.T53_L1
open MeasureTheory ProbabilityTheory

theorem SAP.P001c.WH.W1.T53_L1_proof : SAP.P001c.WH.W1.T53_L1 := by
  have hmass := atom_mass
  have hmean := value_expectation
  have hsecond := value_sq_expectation
  have hmem := value_memLp
  have hprobLaw : IsProbabilityMeasure SAP.P001c.powerTailLaw := by
    unfold SAP.P001c.powerTailLaw
    infer_instance
  haveI : IsProbabilityMeasure SAP.P001c.powerTailLaw := hprobLaw
  refine ⟨hmass, hmem, ?_, hmean, hsecond, ?_⟩
  · have habs : (fun k => |SAP.P001c.powerTailValue k|) = SAP.P001c.powerTailValue := by
      funext k
      exact abs_of_nonneg (value_nonneg k)
    rw [habs]
    exact hmean
  · rw [variance_eq_sub hmem]
    change SAP.P001c.expectation SAP.P001c.powerTailLaw
        (fun k => (SAP.P001c.powerTailValue k)^2) -
      (SAP.P001c.expectation SAP.P001c.powerTailLaw SAP.P001c.powerTailValue)^2 = 7 / 18
    rw [hsecond, hmean]
    norm_num

