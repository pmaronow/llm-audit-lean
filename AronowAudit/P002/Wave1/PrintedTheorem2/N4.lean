import AronowAudit.P002.Wave1.PrintedTheorem2Blueprint
import AronowAudit.P031.P031_Variance

namespace AronowAudit.P002.Wave1.PrintedTheorem2
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Transport the proved P031 finite-sampling identity, including complementation. -/
theorem n4_proof : N4 := by
  intro n P q h1 h0
  have hmn : P.n1 ≤ n := by omega
  have hk : n - P.n1 ≤ n := Nat.sub_le _ _
  have hmn' : P.n1 ≤ Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using hmn
  have hk' : n - P.n1 ≤ Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using hk
  have hmean : AronowAudit.P031.groupMean Finset.univ q = mean q := by
    simp only [AronowAudit.P031.groupMean, mean, Finset.card_univ, Fintype.card_fin]
  have hvar : AronowAudit.P031.popVariance q = (∑ i, (q i - mean q) ^ 2) / n := by
    simp only [AronowAudit.P031.popVariance, hmean, Fintype.card_fin]
  have hexpect (f : Finset (Fin n) → ℝ) :
      expectation P f = AronowAudit.P031.expectation P.n1 f := rfl
  constructor
  · calc
      expectation P (fun S => (groupMean S q - mean q) ^ 2) =
          AronowAudit.P031.expectation P.n1
            (fun S => (AronowAudit.P031.groupMean S q -
              AronowAudit.P031.groupMean Finset.univ q) ^ 2) := by
        simp only [hexpect, groupMean, AronowAudit.P031.groupMean, mean,
          Finset.card_univ, Fintype.card_fin]
      _ = _ := by
        simpa only [Fintype.card_fin, hvar] using
          AronowAudit.P031.sample_mean_squared_error P.n1 h1 hmn' q
  · calc
      expectation P (fun S => (groupMean Sᶜ q - mean q) ^ 2) =
          AronowAudit.P031.expectation P.n1
            (fun S => (AronowAudit.P031.groupMean Sᶜ q -
              AronowAudit.P031.groupMean Finset.univ q) ^ 2) := by
        simp only [hexpect, groupMean, AronowAudit.P031.groupMean, mean,
          Finset.card_univ, Fintype.card_fin]
      _ = AronowAudit.P031.expectation (n - P.n1)
          (fun S => (AronowAudit.P031.groupMean S q -
            AronowAudit.P031.groupMean Finset.univ q) ^ 2) := by
        simpa only [Fintype.card_fin] using
          AronowAudit.P031.expectation_compl P.n1 hmn'
            (fun S => (AronowAudit.P031.groupMean S q -
              AronowAudit.P031.groupMean Finset.univ q) ^ 2)
      _ = (((n : ℝ) - ((n - P.n1 : ℕ) : ℝ)) /
          (((n - P.n1 : ℕ) : ℝ) * ((n : ℝ) - 1))) *
            ((∑ i, (q i - mean q) ^ 2) / n) := by
        simpa only [Fintype.card_fin, hvar] using
          AronowAudit.P031.sample_mean_squared_error (n - P.n1) h0 hk' q
      _ = _ := by
        rw [Nat.cast_sub hmn]
        ring

end
end AronowAudit.P002.Wave1.PrintedTheorem2
