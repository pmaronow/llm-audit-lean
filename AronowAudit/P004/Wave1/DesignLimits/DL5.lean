import AronowAudit.P004.Wave1.DesignLimits.DL1
import AronowAudit.P004.Wave1.DesignLimits.NF

namespace AronowAudit.P004.Wave1.DesignLimits

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Additive Slutsky, using finite-event inclusions and continuity of the normal CDF. -/
theorem dl5_proof : DL5 := by
  classical
  intro p hp T U hT hU x
  -- These bounds hold separately for every fixed positive delta and every N.
  have hsandwich : ∀ δ : ℝ, 0 < δ → ∀ N,
      prob (p N) (fun z => T N z ≤ x - δ) -
          prob (p N) (fun z => δ < |U N z|) ≤
        prob (p N) (fun z => T N z + U N z ≤ x) ∧
      prob (p N) (fun z => T N z + U N z ≤ x) ≤
        prob (p N) (fun z => T N z ≤ x + δ) +
          prob (p N) (fun z => δ < |U N z|) := by
    intro δ _hδ N
    have hlower := prob_le_add_of_imp_finite (p N) (hp N)
      (fun z => T N z ≤ x - δ)
      (fun z => T N z + U N z ≤ x)
      (fun z => δ < |U N z|) (by
        intro z hz
        by_cases hb : δ < |U N z|
        · exact Or.inr hb
        · left
          have hUle : U N z ≤ δ :=
            le_trans (le_abs_self (U N z)) (le_of_not_gt hb)
          linarith)
    have hupper := prob_le_add_of_imp_finite (p N) (hp N)
      (fun z => T N z + U N z ≤ x)
      (fun z => T N z ≤ x + δ)
      (fun z => δ < |U N z|) (by
        intro z hz
        by_cases hb : δ < |U N z|
        · exact Or.inr hb
        · left
          have hnegUle : -U N z ≤ δ :=
            le_trans (neg_le_abs (U N z)) (le_of_not_gt hb)
          linarith)
    exact ⟨by linarith, hupper⟩
  -- Choose a fixed shift small enough for any requested CDF tolerance.
  have hclose : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      |normalCDF (x - δ) - normalCDF x| < η ∧
      |normalCDF (x + δ) - normalCDF x| < η := by
    intro η hη
    have hcont : ContinuousAt normalCDF x := nf_proof.1.continuousAt
    obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp hcont η hη
    have hminus : dist (x - r / 2) x < r := by
      rw [Real.dist_eq]
      have heq : x - r / 2 - x = -(r / 2) := by ring
      rw [heq, abs_neg, abs_of_pos (half_pos hr)]
      linarith
    have hplus : dist (x + r / 2) x < r := by
      rw [Real.dist_eq]
      have heq : x + r / 2 - x = r / 2 := by ring
      rw [heq, abs_of_pos (half_pos hr)]
      linarith
    refine ⟨r / 2, half_pos hr, ?_, ?_⟩
    · simpa only [Real.dist_eq] using hball hminus
    · simpa only [Real.dist_eq] using hball hplus
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨δ, hδ, hminus, _⟩ := hclose ((normalCDF x - a) / 2) (by linarith)
    have hgap : a < normalCDF (x - δ) := by
      have hleft := (abs_lt.mp hminus).1
      linarith
    have hlim : Tendsto (fun N => prob (p N) (fun z => T N z ≤ x - δ) -
        prob (p N) (fun z => δ < |U N z|)) atTop
        (nhds (normalCDF (x - δ))) := by
      simpa only [sub_zero] using (hT (x - δ)).sub (hU δ hδ)
    have hevent : ∀ᶠ N in atTop, a <
        prob (p N) (fun z => T N z ≤ x - δ) -
          prob (p N) (fun z => δ < |U N z|) :=
      hlim.eventually (eventually_gt_nhds hgap)
    filter_upwards [hevent] with N hN
    exact lt_of_lt_of_le hN (hsandwich δ hδ N).1
  · intro b hb
    obtain ⟨δ, hδ, _, hplus⟩ := hclose ((b - normalCDF x) / 2) (by linarith)
    have hgap : normalCDF (x + δ) < b := by
      have hright := (abs_lt.mp hplus).2
      linarith
    have hlim : Tendsto (fun N => prob (p N) (fun z => T N z ≤ x + δ) +
        prob (p N) (fun z => δ < |U N z|)) atTop
        (nhds (normalCDF (x + δ))) := by
      simpa only [add_zero] using (hT (x + δ)).add (hU δ hδ)
    have hevent : ∀ᶠ N in atTop,
        prob (p N) (fun z => T N z ≤ x + δ) +
          prob (p N) (fun z => δ < |U N z|) < b :=
      hlim.eventually (eventually_lt_nhds hgap)
    filter_upwards [hevent] with N hN
    exact lt_of_le_of_lt (hsandwich δ hδ N).2 hN

end
end AronowAudit.P004.Wave1.DesignLimits
