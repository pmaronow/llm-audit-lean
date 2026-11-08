import SAP.P046.WH.W1.Leaves
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

namespace SAP.P046.WH.W1.P.T5_L3

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

theorem error_bridge (M : Study) (f g : ℝ → ℝ)
    (hf : MemLp (fun o => f (W o)) 2 M.law)
    (hg : MemLp (fun o => g (W o)) 2 M.law) :
    l2Sq M (fun w => f w - g w) =
        ENNReal.toReal (wholeL2Sq M (fun w => f w - g w)) ∧
      wholeL2Sq M (fun w => f w - g w) < ⊤ := by
  have hsub : MemLp (fun o => f (W o) - g (W o)) 2 M.law := hf.sub hg
  have hsquare : Integrable (fun o => (f (W o) - g (W o)) ^ 2) M.law :=
    hsub.integrable_sq
  have hnonneg : 0 ≤ᵐ[M.law] fun o => (f (W o) - g (W o)) ^ 2 :=
    ae_of_all _ fun o => sq_nonneg _
  have hbridge := integral_eq_lintegral_of_nonneg_ae hnonneg hsquare.aestronglyMeasurable
  have hfinite : (∫⁻ o, ENNReal.ofReal ((f (W o) - g (W o)) ^ 2) ∂M.law) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal hnonneg).mp hsquare.hasFiniteIntegral
  constructor
  · simpa [l2Sq, wholeL2Sq] using hbridge
  · simpa [wholeL2Sq] using hfinite

end

end SAP.P046.WH.W1.P.T5_L3

theorem SAP.P046.WH.W1.T5_L3_proof : SAP.P046.WH.W1.T5_L3 := by
  classical
  intro M hM F g hg hF j hWhole
  letI := hM.probability
  intro eps heps
  have hsets (n : ℕ) :
      {a : Sample n | eps < l2Sq M (fun w => (F n).g j a w - g w)} =ᵐ[sampleLaw M n]
      {a | ENNReal.ofReal eps <
        wholeL2Sq M (fun w => (F n).g j a w - g w)} := by
    filter_upwards [hF n j] with a ha
    have hb := SAP.P046.WH.W1.P.T5_L3.error_bridge M
      (fun w => (F n).g j a w) g ha hg
    have hcmp :
        (ENNReal.ofReal eps < wholeL2Sq M (fun w => (F n).g j a w - g w)) ↔
          eps < l2Sq M (fun w => (F n).g j a w - g w) := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt heps) (ne_of_lt hb.2)]
      rw [← hb.1]
    change (eps < l2Sq M (fun w => (F n).g j a w - g w)) =
      (ENNReal.ofReal eps < wholeL2Sq M (fun w => (F n).g j a w - g w))
    exact propext hcmp.symm
  have hseq :
      (fun n => (sampleLaw M n
        {a | eps < l2Sq M (fun w => (F n).g j a w - g w)}).toReal) =
      (fun n => (sampleLaw M n
        {a | ENNReal.ofReal eps <
          wholeL2Sq M (fun w => (F n).g j a w - g w)}).toReal) := by
    funext n
    exact congrArg ENNReal.toReal ((hsets n).measure_eq)
  rw [hseq]
  exact hWhole eps heps
