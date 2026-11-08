import SAP.P023.Defs
import SAP.P023.Bridge
import SAP.P023.WH.W1.Proofs.T3
import SAP.P023.WH.W1.Proofs.T4
import SAP.P023.WH.W1.Proofs.T5
import SAP.P023.WH.W1.Proofs.T8
import SAP.P023.WH.W1.Proofs.T11
import SAP.P023.WH.W2.Proofs.T11

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P023 SAP.P023.Bridge
open MeasureTheory Filter
open scoped BigOperators Topology

theorem SAP.P023.T1 : T1Statement := by
  have hw : close (1/200 : ℝ) linearX = {2, 3} := by
    ext i; fin_cases i <;> norm_num [close, linearX]
  refine ⟨linearWitness, hw, ?_, ?_, ?_⟩
  · norm_num [rd, hw, linearD, linearY]
  · intro y y' hag
    unfold rd
    congr 2 <;> apply Finset.sum_congr rfl <;> intro i hi <;> rw [hag i hi]
  · intro y y' β β' hag hβ hβ'
    exact coarsenedLocalization (1/200) (by norm_num) linearX linearD y y'
      linearWitness.1 (by norm_num [hw, linearD]) (by norm_num [hw, linearD])
      hag β β' hβ hβ'

theorem SAP.P023.T2 : T2Statement := by
  have hw : close (1/5 : ℝ) degree7X = {7, 8} := by
    ext i; fin_cases i <;> norm_num [close, degree7X]
  exact ⟨degreeSevenWitness, hw, by norm_num [rd, hw, degree7D, degree7Y]⟩

theorem SAP.P023.T3 : SAP.P023.T3WholeStatement := SAP.P023.WH.W1.T3_whole

theorem SAP.P023.T4 : SAP.P023.T4WholeStatement := SAP.P023.WH.W1.T4_whole

theorem SAP.P023.T5 : SAP.P023.T5WholeStatement := SAP.P023.WH.W1.T5_whole

theorem SAP.P023.T6 : T6Statement := by
  exact ⟨uniformLaw.1, uniformLaw.2, continuityWitness, noLipschitzContinuityCounterexample⟩

theorem SAP.P023.T7 : T7Statement := by
  exact ⟨populationBias, uniformConstants, finitePolynomialWeights, finiteConditionalBias⟩

theorem SAP.P023.T8 : SAP.P023.T8WholeStatement := SAP.P023.WH.W1.T8_whole

theorem SAP.P023.T9 : T9Statement := by
  exact pairIndexedAppendix

theorem SAP.P023.T10 : T10Statement := by
  exact ⟨coarsenedLocalization, polynomialLocalizationRefutation⟩

theorem SAP.P023.T11 : SAP.P023.T11WholeStatement_W2 := SAP.P023.WH.W2.T11_whole

theorem SAP.P023.T12 : T12Statement := by
  exact propositionTwoRefutation

