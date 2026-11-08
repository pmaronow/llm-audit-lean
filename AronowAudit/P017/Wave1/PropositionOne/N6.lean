import AronowAudit.P017.Wave1.PropositionOneBlueprint
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.InfinitePi

set_option autoImplicit false

namespace AronowAudit.P017.Wave1.PropositionOne

open AronowAudit.P017 MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

theorem n6_proof : N6 := by
  intro h1 h5
  let P := iidSamples ipwPopulation
  let X : ℕ → (ℕ → ℝ × (ℝ × ℝ)) → ℝ := fun i s => ipwSummand (s i)
  have hm : Measurable ipwSummand := h5.1
  have hpop (i : ℕ) : IdentDistrib (X i) ipwSummand P ipwPopulation := by
    have heval : IdentDistrib (fun s : ℕ → ℝ × (ℝ × ℝ) => s i) id
        P ipwPopulation :=
      ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, by
        rw [show P = Measure.infinitePi (fun _ : ℕ => ipwPopulation) from rfl,
          (measurePreserving_eval_infinitePi (fun _ : ℕ => ipwPopulation) i).map_eq,
          Measure.map_id]⟩
    exact heval.comp hm
  have hindep : iIndepFun X P := iIndepFun_infinitePi (fun _ => hm)
  have hid (i : ℕ) : IdentDistrib (X i) (X 0) P P :=
    (hpop i).trans (hpop 0).symm
  have hx : MemLp (X 0) 2 P := (hpop 0).memLp_iff.mpr h5.2.1
  have hv : variance (X 0) P = (53 / 12 : ℝ) :=
    (hpop 0).variance_eq.trans h5.2.2.2
  have hmean : (∫ s, X 0 s ∂P) = populationMean ipwPopulation ipwEffect := by
    rw [(hpop 0).integral_eq, h5.2.2.1, h1.2.2]
  let v : ℝ≥0 := (53 / 12 : ℝ).toNNReal
  have hvpos : 0 < v := Real.toNNReal_pos.mpr (by norm_num)
  have hy : HasLaw id (gaussianReal 0 (variance (X 0) P).toNNReal)
      (gaussianReal 0 v) := by
    rw [hv]
    exact ⟨measurable_id.aemeasurable, Measure.map_id⟩
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hy hx hindep hid
  change ∃ v : ℝ≥0, 0 < v ∧ TendstoInDistribution
    (fun n s => sqrtN n * (sampleMean ipwSummand n s - populationMean ipwPopulation ipwEffect))
    atTop (fun z : ℝ => z) (fun _ => iidSamples ipwPopulation) (gaussianReal 0 v)
  refine ⟨v, hvpos, ?_⟩
  refine hclt.congr (fun n => ae_of_all _ fun s => ?_) (ae_of_all _ fun _ => rfl)
  rw [hmean]
  change (Real.sqrt (n : ℝ))⁻¹ *
      ((∑ i ∈ Finset.range n, ipwSummand (s i)) -
        (n : ℝ) * populationMean ipwPopulation ipwEffect) =
    Real.sqrt (n : ℝ) *
      ((∑ i ∈ Finset.range n, ipwSummand (s i)) / (n : ℝ) -
        populationMean ipwPopulation ipwEffect)
  by_cases hn : n = 0
  · simp [hn]
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
    field_simp
    rw [hsq]

end

end AronowAudit.P017.Wave1.PropositionOne
