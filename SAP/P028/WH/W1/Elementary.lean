import SAP.P028.WH.W1.Donors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028.WH.W1
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open SAP.P028 SAP.P028.Bridge
noncomputable section
open Classical

theorem printedPairs (x0 x1 : ℝ) :
    printedSystem (1/2) (3/4) (3/4) x0 x1 ↔ x0 = x1 ∧ x1 ∈ Set.Icc 0 1 := by
  unfold printedSystem
  constructor
  · rintro ⟨he,h0,h01,h1,h11,hm,hm1⟩
    exact ⟨by linarith, h1, h11⟩
  · rintro ⟨rfl,h1,h11⟩
    exact ⟨by ring, h1, h11, h1, h11, by linarith, by linarith⟩

theorem mixturePairs (x0 x1 : ℝ) :
    mixtureSystem (1/2) (3/4) (3/4) x0 x1 ↔ x0 = x1 ∧ x1 ∈ Set.Icc (1/2) 1 := by
  change AronowAudit.P028.mixtureSystem _ _ _ _ _ ↔ _
  rw [AronowAudit.P028.corrected_reframing _ _ _ _ _ (by norm_num) (by norm_num)]
  unfold AronowAudit.P028.correctedSystem
  constructor
  · rintro ⟨he,h0,h01,h1,h11,hm,hm1⟩
    exact ⟨by linarith, by linarith, h11⟩
  · rintro ⟨rfl,h1,h11⟩
    exact ⟨by ring, by linarith, h11, by linarith, h11, by linarith, by linarith⟩

theorem coordinate_eq (F : ℝ → ℝ → Prop) (a b : ℝ)
    (hF : ∀ x0 x1, F x0 x1 ↔ x0 = x1 ∧ x1 ∈ Set.Icc a b) (d : Bool) :
    wholeCoordinate F d = Set.Icc a b := by
  ext x
  constructor
  · rintro ⟨x0,x1,h,hx⟩
    rcases (hF _ _).mp h with ⟨he,hi⟩
    have hx' : x1 = x := by cases d <;> simp_all
    exact hx' ▸ hi
  · intro hx
    exact ⟨x,x,(hF _ _).mpr ⟨rfl,hx⟩,by cases d <;> rfl⟩

def halfProbability : Set.Icc (0 : ℝ) 1 := ⟨1/2, by constructor <;> norm_num⟩
def oneProbability : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩

theorem misprintRealization : wholeMisprintRealization := by
  let A := AronowAudit.P028.attainingModel halfProbability (by norm_num [halfProbability]) 1 1 (1/2)
  let M := fromAudit A
  have hb : boundedOutcomes M := AronowAudit.P028.attaining_model_bounded
    halfProbability (by norm_num [halfProbability]) 1 1 (1/2)
    (by norm_num) (by norm_num) (by norm_num)
  have hm := AronowAudit.P028.attaining_model_moments
    halfProbability (by norm_num [halfProbability]) 1 1 (1/2)
  change complierProbability M = (1/2 : ℝ) ∧
    armMean M false = (1/2)*1+(1-1/2)*(1/2) ∧
    armMean M true = (1/2)*1+(1-1/2)*(1/2) ∧
    complierMean M false = 1 ∧ complierMean M true = 1 at hm
  refine ⟨M, rfl, rfl, ?_, rfl, hb, hm.1, ?_, ?_, ?_, ?_, hm.2.2.2⟩
  · funext d ω
    cases d <;> rfl
  · change (AronowAudit.P028.attainingMeasure halfProbability).real {ω | (if ω.1 then 2 else 1 : Fin 3) = 1} = 1/2
    rw [← integral_indicator_one MeasurableSet.of_discrete, AronowAudit.P028.attaining_integral]
    norm_num [halfProbability, Set.indicator]
  · exact AronowAudit.P028.attaining_arm_probability halfProbability
  · linarith [hm.2.1]
  · linarith [hm.2.2.1]

theorem fullComplianceWitness :
    ∃ M : CausalModel (Bool × Bool), boundedOutcomes M ∧ complierProbability M = 1 ∧
      complierMean M false = 0 ∧ complierMean M true = 1 ∧
      (∀ z, M.μ.real (armEvent M z) = 1/2) := by
  let A := AronowAudit.P028.attainingModel oneProbability (by norm_num [oneProbability]) 0 1 0
  refine ⟨fromAudit A, ?_, ?_, ?_, ?_, ?_⟩
  · exact AronowAudit.P028.attaining_model_bounded oneProbability (by norm_num [oneProbability])
      0 1 0 (by norm_num) (by norm_num) (by norm_num)
  · exact (AronowAudit.P028.attaining_model_moments oneProbability (by norm_num [oneProbability]) 0 1 0).1
  · exact (AronowAudit.P028.attaining_model_moments oneProbability (by norm_num [oneProbability]) 0 1 0).2.2.2.1
  · exact (AronowAudit.P028.attaining_model_moments oneProbability (by norm_num [oneProbability]) 0 1 0).2.2.2.2
  · exact AronowAudit.P028.attaining_arm_probability oneProbability

theorem fullCompliance_ae {Ω : Type*} [MeasurableSpace Ω] (M : CausalModel Ω)
    (hp : complierProbability M = 1) : ∀ᵐ ω ∂M.μ, ω ∈ complierEvent M := by
  have hm : MeasurableSet (complierEvent M) := (M.measurableS (measurableSet_singleton 2))
  have hc : M.μ.real (complierEvent M)ᶜ = 0 := by
    rw [probReal_compl_eq_one_sub hm]
    change 1-complierProbability M = 0
    rw [hp]; ring
  exact (ae_iff).mpr ((measureReal_eq_zero_iff).mp hc)

end
end SAP.P028.WH.W1
