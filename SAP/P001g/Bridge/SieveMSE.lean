import SAP.P001g.Defs
import AronowAudit.P001.Wave1.SieveRate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g.Bridge

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001.Wave1
open AronowAudit.P001.Wave1.SieveRate
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-- Transport the standard Gaussian second moment through the existing
witness's one-observation marginal law. -/
theorem sieve_outcome_memLp : MemLp (sieveY 0) 2 sieveMu := by
  have hZ : Measurable (fun ω => (sieveX 0 ω, sieveY 0 ω)) := n1_proof.2.1.1 0
  have hY : Measurable (sieveY 0) := measurable_snd.comp hZ
  have hYlaw : sieveMu.map (sieveY 0) = gaussianReal 0 1 := by
    change sieveMu.map (Prod.snd ∘ (fun ω => (sieveX 0 ω, sieveY 0 ω))) = _
    rw [← Measure.map_map measurable_snd hZ, n1_proof.2.2.1]
    simp only [sieveNu, Measure.map_snd_prod, measure_univ, one_smul]
  have hG : MemLp (id : ℝ → ℝ) 2 (sieveMu.map (sieveY 0)) := by
    rw [hYlaw]
    simpa using (memLp_id_gaussianReal (μ := 0) (v := 1) (2 : ℝ≥0))
  simpa only [Function.comp_def, id_eq] using hG.comp_of_map hY.aemeasurable

/-- Reassemble the source's sieve counterexample using its existing bad-event
bound and event inclusion, now also supplying the finite-second-moment guard.
The subsequence/limit contradiction is the same scalar transport as in the
source assembly; no counterexample estimates are reproved. -/
theorem t119 : SAP.P001g.T119Statement := by
  intro H
  letI : IsProbabilityMeasure sieveMu := n1_proof.1
  obtain ⟨hpdf, hYi, hcef⟩ := n2_proof n1_proof
  obtain ⟨fit, hfit⟩ := n4_proof PolynomialBlp.n3_proof sieveX sieveY sieveJ
  have hCP := @H (ℕ → ℝ × ℝ) _ sieveMu inferInstance sieveX sieveY
    n1_proof.2.1 hYi sieve_outcome_memLp 0 1 one_pos sieveF hpdf
    sieveF_pos sieveM contDiff_const hcef sieveJ n3_proof.1 n3_proof.2.1 fit hfit
  have hT := (hCP 1 one_pos).comp (tendsto_pow_atTop (n := 4) (by norm_num))
  have hev := hT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 72))
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp hev
  have hlt := ht₀ (max t₀ 25) (le_max_left _ _)
  have hbad := n19_proof n1_proof n18_proof n16_proof n17_proof
    (n15_proof n5_proof n7_proof n8_proof n9_proof n10_proof n11_proof
      n12_proof n13_proof n14_proof) (max t₀ 25) (le_max_right _ _)
  have hsub := badSet_subset n1_proof n3_proof n5_proof n6_proof n20_proof
    fit hfit (max t₀ 25) (le_trans (by norm_num) (le_max_right _ _))
  have hmono := ENNReal.toReal_mono (measure_ne_top sieveMu _) (measure_mono hsub)
  simp only [Function.comp, SAP.P001g.prob] at hlt
  linarith

end
end SAP.P001g.Bridge
