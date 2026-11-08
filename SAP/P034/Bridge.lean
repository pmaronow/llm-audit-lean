import SAP.P034.Defs
import AronowAudit.P034.P034_Attrition
import AronowAudit.P034.P034_Contrasts
import AronowAudit.P034.P034_Rounding

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P034.Bridge

open MeasureTheory ProbabilityTheory

/-- Copy the four data fields into the existing project's model. -/
def toAudit {Ω K : Type*} {k : ℕ} (M : SAP.P034.SurveyModel Ω K k) :
    AronowAudit.P034.SurveyModel Ω K k where
  T := M.T
  Y := M.Y
  R := M.R
  X := M.X

theorem worldAModel_eq : toAudit SAP.P034.worldAModel = AronowAudit.P034.worldAModel := rfl

theorem worldBModel_eq : toAudit SAP.P034.worldBModel = AronowAudit.P034.worldBModel := rfl

/-- The finite facts agree after reducing the concrete model's fields. -/
theorem worldAFacts_iff :
    SAP.P034.WorldANumericalFacts ↔ AronowAudit.P034.WorldANumericalFacts := Iff.rfl

theorem sampleFacts_iff :
    SAP.P034.SampleNumericalFacts ↔ AronowAudit.P034.SampleNumericalFacts := Iff.rfl

theorem worldBFacts_iff : SAP.P034.WorldBFacts ↔ AronowAudit.P034.WorldBFacts := Iff.rfl

theorem testProbability_eq :
    SAP.P034.chiSquareOnePValue (SAP.P034.samplePearson : ℝ) =
      AronowAudit.P034.chiSquareOnePValue (AronowAudit.P034.samplePearson : ℝ) := rfl

theorem potentialBundle_eq {Ω : Type*} {k : ℕ} (M : SAP.P034.SurveyModel Ω ℝ k) :
    SAP.P034.potentialBundle M = AronowAudit.P034.potentialBundle (toAudit M) := rfl

theorem outcomeCovariateBundle_eq {Ω : Type*} {k : ℕ}
    (M : SAP.P034.SurveyModel Ω ℝ k) :
    SAP.P034.outcomeCovariateBundle M =
      AronowAudit.P034.outcomeCovariateBundle (toAudit M) := rfl

theorem identification_iff {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (M : SAP.P034.SurveyModel Ω ℝ k) :
    SAP.P034.CompleteCaseIdentification μ M ↔
      AronowAudit.P034.CompleteCaseIdentification μ (toAudit M) := Iff.rfl

theorem failure_iff :
    SAP.P034.EqualCompletionFailure ↔ AronowAudit.P034.EqualCompletionFailure := Iff.rfl

theorem fittedOutcome_eq : @SAP.P034.fittedOutcome = @AronowAudit.P034.fittedOutcome := rfl

theorem factorialCell_eq : SAP.P034.factorialCell = AronowAudit.P034.factorialCell := rfl

theorem oa3Counts_eq : SAP.P034.oa3Counts = AronowAudit.P034.oa3Counts := rfl

theorem oa3Totals_eq : SAP.P034.oa3Totals = AronowAudit.P034.oa3Totals := rfl

theorem oa3Tenths_eq : SAP.P034.oa3Tenths = AronowAudit.P034.oa3Tenths := rfl

theorem oa3Percentage_eq : SAP.P034.oa3Percentage = AronowAudit.P034.oa3Percentage := rfl

theorem roundsToTenth_eq : SAP.P034.roundsToTenth = AronowAudit.P034.roundsToTenth := rfl

/-- Scalar extension of an exported nonsingular rational system and its
exported solution, using Mathlib's determinant and multiplication maps. -/
theorem normal_equations_cast {n : ℕ} (G : Matrix (Fin n) (Fin n) ℚ)
    (h b : Fin n → ℚ) (hdet : G.det ≠ 0) (hsol : G.mulVec b = h)
    (β : Fin n → ℝ) :
    (G.map (fun q => (q : ℝ))).mulVec β = (fun i => (h i : ℝ)) ↔
      β = (fun i => (b i : ℝ)) := by
  have hdetR : (G.map (fun q => (q : ℝ))).det ≠ 0 := by
    rw [← Rat.cast_det]
    exact_mod_cast hdet
  have hunit : IsUnit (G.map (fun q => (q : ℝ))) :=
    (G.map (fun q => (q : ℝ))).isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr hdetR)
  have hsolR : (G.map (fun q => (q : ℝ))).mulVec (fun i => (b i : ℝ)) =
      (fun i => (h i : ℝ)) := by
    funext i
    simpa only [Function.comp_def, Rat.coe_castHom, hsol] using
      ((Rat.castHom ℝ).map_mulVec G b i).symm
  exact ⟨fun hβ => (Matrix.mulVec_injective_iff_isUnit.mpr hunit)
    (hβ.trans hsolR.symm), fun hβ => hβ ▸ hsolR⟩

end SAP.P034.Bridge
