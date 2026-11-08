import AronowAudit.P017.Wave1.PropositionOneBlueprint
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false

namespace AronowAudit.P017.Wave1.PropositionOne

open AronowAudit.P017 MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

theorem n3_proof : N3 := by
  intro h1 h2
  have hμ : populationMean ipwPopulation ipwEffect = 1 / 2 := h1.2.2
  have hclosed : IsClosed (effectSupport ipwPopulation ipwEffect) :=
    Measure.isClosed_support
  have hIcc : Icc (0 : ℝ) 1 ⊆ effectSupport ipwPopulation ipwEffect := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact closure_minimal h2 hclosed
  have h0 : (0 : ℝ) ∈ effectSupport ipwPopulation ipwEffect := hIcc (by norm_num)
  have h1s : (1 : ℝ) ∈ effectSupport ipwPopulation ipwEffect := hIcc (by norm_num)
  have hinf : supportInf (effectSupport ipwPopulation ipwEffect) ≤ (0 : EReal) := by
    exact sInf_le ⟨0, h0, by simp⟩
  have hsup : (1 : EReal) ≤ supportSup (effectSupport ipwPopulation ipwEffect) := by
    exact le_sSup ⟨1, h1s, by simp⟩
  have hu : ((1 / 2 : ℝ) : EReal) ≤
      supportSup (effectSupport ipwPopulation ipwEffect) - ((1 / 2 : ℝ) : EReal) := by
    calc
      _ = (1 : EReal) - ((1 / 2 : ℝ) : EReal) := by
        rw [← EReal.coe_one, ← EReal.coe_sub]; norm_num
      _ ≤ _ := EReal.sub_le_sub hsup le_rfl
  have hl : ((1 / 2 : ℝ) : EReal) ≤
      ((1 / 2 : ℝ) : EReal) - supportInf (effectSupport ipwPopulation ipwEffect) := by
    calc
      _ = ((1 / 2 : ℝ) : EReal) - (0 : EReal) := by simp
      _ ≤ _ := EReal.sub_le_sub le_rfl hinf
  have hr := EReal.toENNReal_le_toENNReal (le_min hu hl)
  change (1 / 2 : ℝ≥0∞) ≤ effectRadius ipwPopulation ipwEffect
  simpa only [effectRadius, hμ, EReal.real_coe_toENNReal, ENNReal.ofReal_div_of_pos
    (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using hr

end

end AronowAudit.P017.Wave1.PropositionOne
