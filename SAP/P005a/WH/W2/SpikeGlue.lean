import SAP.P005a.Defs.WholeW2
import SAP.P005a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2
noncomputable section
open Finset Filter SAP.P005a.Bridge
open scoped BigOperators Matrix Topology
set_option maxHeartbeats 800000

/-- Positive normalized arm variance follows from the already proved raw variance. -/
theorem spikeVariance_pos (n : ℕ) (hn : 6 ≤ n) (A : Finset (Fin n))
    (hcard : 2 ≤ A.card) : 0 < firstVariance (spikePopulation n) A := by
  have hq : 0 < spikeQ n :=
    AronowAudit.P005.Wave1.InteractedExpansion.spikeQ_pos_of_S1
      AronowAudit.P005.Wave1.InteractedExpansion.n1_proof n (by omega)
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  have hx : (fun i => (spikePopulation n).x i 0) =
      (fun i => (Real.sqrt (spikeQ n))⁻¹ * spikeZ n i) := by
    funext i
    dsimp only [spikePopulation]
    ring
  unfold firstVariance
  rw [hx]
  change 0 < AronowAudit.P005.sampleCov A _ _
  rw [AronowAudit.P005.sampleCov_scale_both]
  change 0 < (Real.sqrt (spikeQ n))⁻¹^2 *
    AronowAudit.P005.sampleCov A (fun i => spikeA n i-1/(n : ℝ))
      (fun i => spikeA n i-1/(n : ℝ))
  rw [AronowAudit.P005.covariance_location_invariant A hA]
  exact mul_pos (sq_pos_of_ne_zero (inv_ne_zero (Real.sqrt_pos.mpr hq).ne'))
    (AronowAudit.P005.Wave1.InteractedExpansion.n5_proof n hn A hcard)

/-- The generic affine-OLS theorem gives the raw fitted-line interpretation. -/
theorem spikeFit_eq (n : ℕ) (hn : 6 ≤ n) (A : Finset (Fin n)) (hcard : 2 ≤ A.card) :
    mean A (spikeV n) - dot (xMean (spikePopulation n) A)
      (armBetaHat (spikePopulation n) A (spikeV n)) = spikeFit n A := by
  have hq : 0 < spikeQ n :=
    AronowAudit.P005.Wave1.InteractedExpansion.spikeQ_pos_of_S1
      AronowAudit.P005.Wave1.InteractedExpansion.n1_proof n (by omega)
  have hh := (AronowAudit.P005.Wave1.InteractedExpansion.n4_proof n
    (toPopulation (spikePopulation n)) (spikeA n) (1/(n : ℝ)) (Real.sqrt (spikeQ n))
    (Real.sqrt_pos.mpr hq).ne' (fun _ _ => rfl) A (spikeV n)
    (AronowAudit.P005.Wave1.InteractedExpansion.n5_proof n hn A hcard).ne').2
  have hd : dot (xMean (spikePopulation n) A)
      (armBetaHat (spikePopulation n) A (spikeV n)) =
      (mean A (spikeA n)-1/(n : ℝ))*scalarSlope A (spikeA n) (spikeV n) := hh
  rw [hd]
  unfold spikeFit
  ring

/-- An ordinary-only arm lies exactly on v=n²a. -/
theorem spikeLowFit (n : ℕ) (hn : 6 ≤ n) (A : Finset (Fin n)) (hcard : 2 ≤ A.card)
    (hz : ∀ i ∈ A, i.val ≠ 0) :
    (∀ i ∈ A, spikeV n i = (n : ℝ)^2*spikeA n i) ∧ spikeFit n A = n := by
  constructor
  · intro i hi
    dsimp only [spikeA]
    rw [if_neg (hz i hi)]
    field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast (show n ≠ 0 by omega)]
  · exact AronowAudit.P005.Wave1.InteractedExpansion.n7_proof
      AronowAudit.P005.Wave1.InteractedExpansion.n5_proof n hn A hz hcard

end
end SAP.P005a.WH.W2
