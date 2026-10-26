import AronowAudit.P005.Wave1.InteractedExpansionBlueprint

set_option autoImplicit false
namespace AronowAudit.P005.Wave1.InteractedExpansion
open AronowAudit.P005 Finset Filter
open scoped BigOperators Topology
noncomputable section

/-- Positivity is isolated so the other nodes need only S1. -/
theorem spikeQ_pos_of_S1 (h1 : S1) (n : ℕ) (hn : 3 ≤ n) : 0 < spikeQ n := by
  rw [(h1 n hn).2.2.2.2]
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  positivity

theorem n2_proof : N2 := by
  intro h1 n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnon : (univ : Finset (Fin n)).Nonempty := by
    exact Finset.card_pos.mp (by simpa using (show 0 < n by omega))
  have ha : mean univ (spikeA n) = 1 / (n : ℝ) := by
    simp only [mean, (h1 n hn).2.2.2.1, Finset.card_univ, Fintype.card_fin]
  have hz : popMean (spikeZ n) = 0 := by
    change mean univ (fun i => spikeA n i - 1 / (n : ℝ)) = 0
    rw [mean_sub, ha, mean_const univ hnon, sub_self]
  have hq : 0 < spikeQ n := spikeQ_pos_of_S1 h1 n hn
  have hs : Real.sqrt (spikeQ n) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have hscale : (Real.sqrt (spikeQ n))⁻¹ ^ 2 *
      popMean (fun i => spikeZ n i ^ 2) = 1 := by
    change (Real.sqrt (spikeQ n))⁻¹ ^ 2 * spikeQ n = 1
    rw [inv_pow, Real.sq_sqrt hq.le, inv_mul_cancel₀ (ne_of_gt hq)]
  have hp : spikePopulation n = scalarPopulation (spikeZ n) (spikeV n) (spikeV n)
      (Real.sqrt (spikeQ n))⁻¹ := by
    unfold spikePopulation scalarPopulation
    congr 1
    funext i k
    ring
  rw [hp]
  exact standardized_scalar _ _ _ _ hz hscale

end
end AronowAudit.P005.Wave1.InteractedExpansion
