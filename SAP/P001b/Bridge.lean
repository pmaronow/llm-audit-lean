import SAP.P001b.Defs
import AronowAudit.P001.P001_Foundations
import AronowAudit.P001.Wave1.TotalProbabilityCountable
import AronowAudit.P001.Wave1.Gap.GLP0012B3
import AronowAudit.P001.Wave1.Gap.GLP0012B5
import AronowAudit.P001.Wave1.IrrationalRange
import AronowAudit.P001.Wave1.Gap.GLP0013B1
import AronowAudit.P001.Wave1.Gap.FidP001

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b.Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical
noncomputable section

/-- The finite-distribution adapter only bundles the supplied atom weights. -/
def asFiniteLaw {n : ℕ} (w : Fin n → ℝ) (hn : ∀ i, 0 ≤ w i)
    (ht : ∑ i, w i = 1) : AronowAudit.P001.FiniteLaw n := ⟨w, hn, ht⟩

theorem probability_eq : @probability = @AronowAudit.P001.prob := rfl
theorem density_eq : Density = AronowAudit.P001.HasPDF := rfl
theorem jointDensity_eq : JointDensity = AronowAudit.P001.HasJointPDF := rfl
theorem distributionFunction_eq : @distributionFunction = @AronowAudit.P001.cdf := rfl

theorem finiteProbability_eq {n : ℕ} (P : AronowAudit.P001.FiniteLaw n)
    (A : Fin n → Prop) [DecidablePred A] :
    finiteProbability P.weight A = AronowAudit.P001.fprob P A := by
  unfold finiteProbability AronowAudit.P001.fprob
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : A i <;> simp only [hi, ite_true, ite_false]

theorem finiteMean_eq {n : ℕ} (P : AronowAudit.P001.FiniteLaw n) (Y : Fin n → ℝ) :
    finiteMean P.weight Y = AronowAudit.P001.fmean P Y := rfl

theorem finiteConditionalMean_eq {n : ℕ} (P : AronowAudit.P001.FiniteLaw n)
    (Y X : Fin n → ℝ) (x : ℝ) :
    finiteConditionalMean P.weight Y X x = AronowAudit.P001.fcond P Y X x := rfl

theorem finiteConditionalIndependence_eq {n : ℕ} {E F G : Type*}
    (P : AronowAudit.P001.FiniteLaw n) (Y : Fin n → E) (Z : Fin n → F) (X : Fin n → G) :
    FiniteConditionalIndependence P.weight Y Z X = AronowAudit.P001.FCondIndep P Y Z X := by
  simp only [FiniteConditionalIndependence, AronowAudit.P001.FCondIndep,
    ← finiteProbability_eq]

theorem voterMass_eq : voterMass = AronowAudit.P001.binaryJoint.weight := rfl
theorem electorateType_eq : electorateType = AronowAudit.P001.electorateU := rfl
theorem displayedGender_eq : displayedGender = AronowAudit.P001.electorateD := rfl
theorem potentialVoteShare_eq : potentialVoteShare = AronowAudit.P001.electorateOutcome := rfl
theorem countedVoteShare_eq : countedVoteShare = AronowAudit.P001.electorateVoteShare := rfl
theorem zeroMass_eq : zeroMass = AronowAudit.P001.zeroAtom.weight := rfl
theorem integerCDF_eq : integerCDF = AronowAudit.P001.intMassCDF := rfl
theorem dieMass_eq : dieMass = AronowAudit.P001.fairDieLaw.weight := rfl
theorem dieValue_eq : dieValue = AronowAudit.P001.fairDieValue := rfl

theorem dyadicLocation_eq : dyadicLocation = AronowAudit.P001.dyadicValue := rfl
theorem dyadicWeight_eq : dyadicWeight = AronowAudit.P001.dyadicMass := rfl
theorem dyadicDistributionFunction_eq : dyadicDistributionFunction = AronowAudit.P001.dyadicCDF := rfl
theorem uniformDistributionFunction_eq : uniformDistributionFunction = AronowAudit.P001.uniformCDF := rfl
theorem closedUniformDensity_eq : closedUniformDensity = AronowAudit.P001.uniformClosedPDF := rfl
theorem openUniformDensity_eq : openUniformDensity = AronowAudit.P001.uniformOpenPDF := rfl
theorem modifiedUniformDensity_eq : modifiedUniformDensity = AronowAudit.P001.uniformModifiedPDF := rfl
theorem negativeRectangleDensity_eq : negativeRectangleDensity = AronowAudit.P001.rectanglePDF := rfl
theorem infiniteSliceDensity_eq : infiniteSliceDensity = AronowAudit.P001.smoothSlicePDF := rfl
theorem printedBivariateNormal_eq : printedBivariateNormal = AronowAudit.P001.bivariateNormalPDF := rfl

/-- Structural induction identifies the two recursive interval encodings. -/
theorem cantorInterval_eq (w : List Bool) : cantorInterval w = AronowAudit.P001.fatInterval w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [cantorInterval, AronowAudit.P001.fatInterval, ih]

theorem cantorStage_eq (n : ℕ) : cantorStage n = AronowAudit.P001.fatStage n := by
  simp only [cantorStage, AronowAudit.P001.fatStage, cantorInterval_eq]

theorem fatCantorSet_eq : fatCantorSet = AronowAudit.P001.fatCantor := by
  simp only [fatCantorSet, AronowAudit.P001.fatCantor, cantorStage_eq]

/-- Rewrite the subtype and its measure together along the equality of Cantor sets. -/
theorem cantor_facts : IsClosed fatCantorSet ∧ volume fatCantorSet = 1/2 ∧
    IsProbabilityMeasure cantorProbability ∧
    Density (cantorProbability.map (fun x : fatCantorSet => x.val)) cantorDensity ∧
    Set.range (fun x : fatCantorSet => x.val) = fatCantorSet ∧
    ∀ a b : ℝ, a < b → ¬ Set.Icc a b ⊆ fatCantorSet := by
  let P : Set ℝ → Prop := fun C =>
    IsClosed C ∧ volume C = 1/2 ∧
    IsProbabilityMeasure ((2 : ℝ≥0∞) • volume.comap (fun x : C => x.val)) ∧
    Density (((2 : ℝ≥0∞) • volume.comap (fun x : C => x.val)).map
      (fun x : C => x.val)) (fun x => if x ∈ C then 2 else 0) ∧
    Set.range (fun x : C => x.val) = C ∧
    ∀ a b : ℝ, a < b → ¬ Set.Icc a b ⊆ C
  have hp : P AronowAudit.P001.fatCantor :=
    AronowAudit.P001.Wave1.fat_cantor_continuous_range_counterexample_proof
  exact (congrArg P fatCantorSet_eq).mpr hp

end
end SAP.P001b.Bridge
