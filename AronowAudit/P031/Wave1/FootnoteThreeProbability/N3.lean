import AronowAudit.P031.Wave1.FootnoteThreeProbabilityBlueprint

namespace AronowAudit.P031.Wave1.FootnoteThreeProbability
noncomputable section
open scoped BigOperators Matrix Topology
open Filter

/-- Combine the pointwise error bound and the two finite sampling MSE bounds. -/
theorem n3_proof : N3 := by
  classical
  intro hPoint hAbs N M v B hM hMN hB hv
  let f : ℝ := ((N : ℝ) - M) / ((M : ℝ) * ((N : ℝ) - 1))
  have hmR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hnR : (2 : ℝ) ≤ N := by exact_mod_cast (hM.trans hMN)
  have hmnR : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hf : 0 ≤ f := by
    dsimp only [f]
    exact div_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have hRaw := bounded_raw_sample_moment_errors M hM
    (by simpa only [Fintype.card_fin] using hMN) v B hB hv
  simp only [Fintype.card_fin] at hRaw
  have hsqrt1 : Real.sqrt (f * B ^ 2) = B * Real.sqrt f := by
    rw [Real.sqrt_mul hf, Real.sqrt_sq hB]
    ring
  have hsqrt2 : Real.sqrt (f * B ^ 4) = B ^ 2 * Real.sqrt f := by
    rw [show B ^ 4 = (B ^ 2) ^ 2 by ring, Real.sqrt_mul hf, Real.sqrt_sq (sq_nonneg B)]
    ring
  have hμ : expectation M (fun s => |groupMean s v - groupMean Finset.univ v|) ≤
      B * Real.sqrt f := by
    calc
      _ ≤ Real.sqrt (expectation M (fun s => (groupMean s v - groupMean Finset.univ v) ^ 2)) :=
        hAbs N M _ hMN
      _ ≤ Real.sqrt (f * B ^ 2) := Real.sqrt_le_sqrt hRaw.1
      _ = _ := hsqrt1
  have hν : expectation M (fun s => |groupMean s (fun i => v i ^ 2) -
      groupMean Finset.univ (fun i => v i ^ 2)|) ≤ B ^ 2 * Real.sqrt f := by
    calc
      _ ≤ Real.sqrt (expectation M (fun s => (groupMean s (fun i => v i ^ 2) -
          groupMean Finset.univ (fun i => v i ^ 2)) ^ 2)) := hAbs N M _ hMN
      _ ≤ Real.sqrt (f * B ^ 4) := Real.sqrt_le_sqrt hRaw.2
      _ = _ := hsqrt2
  have hpointE := expectation_mono M (fun s hs =>
    hPoint N M v B s hM (Finset.mem_powersetCard.mp hs).2 hB hv)
  rw [expectation_add, expectation_add, expectation_mul, expectation_mul,
    expectation_const M (by simpa only [Fintype.card_fin] using hMN)] at hpointE
  change expectation M (fun s : Finset (Fin N) => |sampleVariance s v - popVariance v|) ≤
    6 * B ^ 2 * Real.sqrt f + B ^ 2 / ((M : ℝ) - 1)
  calc
    _ ≤ 2 * expectation M (fun s => |groupMean s (fun i => v i ^ 2) -
          groupMean Finset.univ (fun i => v i ^ 2)|) +
        (4 * B) * expectation M (fun s => |groupMean s v - groupMean Finset.univ v|) +
        B ^ 2 / ((M : ℝ) - 1) := hpointE
    _ ≤ 2 * (B ^ 2 * Real.sqrt f) + (4 * B) * (B * Real.sqrt f) +
        B ^ 2 / ((M : ℝ) - 1) := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hν (show (0 : ℝ) ≤ 2 by norm_num))
        (mul_le_mul_of_nonneg_left hμ (show 0 ≤ 4 * B by positivity))) le_rfl
    _ = _ := by ring

end
end AronowAudit.P031.Wave1.FootnoteThreeProbability
