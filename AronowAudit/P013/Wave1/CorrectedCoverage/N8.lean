import AronowAudit.P013.Wave1.CorrectedCoverageBlueprint

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.CorrectedCoverage

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- An eventual positive floor for `N V_N` converts (L) to relative lower tails. -/
theorem n8_proof : N8 := by
  intro S hc6 hL η hη _hη1
  obtain ⟨c, hc, ht⟩ := hc6
  have hfloor : ∀ᶠ n : ℕ in atTop,
      c / 2 < ((n : ℝ) + 1) * seqTrueVariance S n :=
    ht.eventually (lt_mem_nhds (by linarith : c / 2 < c))
  have hδ : 0 < η * c / 2 := by positivity
  have htail := hL (η * c / 2) hδ
  have hupper : ∀ᶠ n : ℕ in atTop,
      probability (seqLaw S n)
          (fun z => seqVarianceEstimate S n z < (1 - η) * seqTrueVariance S n) ≤
        probability (seqLaw S n)
          (fun z => ((n : ℝ) + 1) * seqVarianceEstimate S n z <
            ((n : ℝ) + 1) * seqTrueVariance S n - η * c / 2) := by
    filter_upwards [hfloor] with n hn
    apply probability_mono
    intro z hz
    have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hscaled := mul_lt_mul_of_pos_left hz hN
    have hηfloor := mul_lt_mul_of_pos_left hn hη
    nlinarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) htail
    (Eventually.of_forall (fun n => probability_nonneg _ _)) hupper

end

end AronowAudit.P013.Wave1.CorrectedCoverage
