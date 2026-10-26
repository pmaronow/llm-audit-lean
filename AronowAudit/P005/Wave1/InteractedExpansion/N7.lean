import AronowAudit.P005.Wave1.InteractedExpansionBlueprint

set_option autoImplicit false
namespace AronowAudit.P005.Wave1.InteractedExpansion
open AronowAudit.P005 Finset Filter
open scoped BigOperators Topology
noncomputable section

theorem n7_proof : N7 := by
  intro h5 n hn A hzero hcard
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hv : sampleCov A (spikeA n) (spikeA n) ≠ 0 := ne_of_gt (h5 n hn A hcard)
  have heq (i : Fin n) (hi : i ∈ A) : spikeV n i = (n : ℝ)^2 * spikeA n i := by
    rw [spikeA, if_neg (hzero i hi)]
    field_simp [hn0]
  have hmean : mean A (spikeV n) = (n : ℝ)^2 * mean A (spikeA n) := by
    rw [← mean_mul]
    unfold mean
    congr 1
    exact Finset.sum_congr rfl heq
  have hprod : mean A (fun i => spikeA n i * spikeV n i) =
      (n : ℝ)^2 * mean A (fun i => spikeA n i * spikeA n i) := by
    rw [← mean_mul]
    unfold mean
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [heq i hi]
    ring
  have hcov : sampleCov A (spikeA n) (spikeV n) =
      (n : ℝ)^2 * sampleCov A (spikeA n) (spikeA n) := by
    simp only [sampleCov, hprod, hmean]
    ring
  unfold armFit
  rw [hmean, hcov]
  field_simp [hv, hn0]
  <;> ring

end
end AronowAudit.P005.Wave1.InteractedExpansion
