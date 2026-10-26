import AronowAudit.P001.Wave1.SieveRateBlueprint

/-! The infinite product witness and its one-observation marginals. -/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n1_proof : N1 := by
  classical
  have hprob : IsProbabilityMeasure sieveMu := by
    unfold sieveMu
    infer_instance
  have hpair (i : ℕ) :
      (fun ω : ℕ → ℝ × ℝ => (sieveX i ω, sieveY i ω)) = (fun ω => ω i) := by
    rfl
  have hm (i : ℕ) :
      Measurable (fun ω : ℕ → ℝ × ℝ => (sieveX i ω, sieveY i ω)) := by
    rw [hpair i]
    exact measurable_pi_apply i
  have hlaw (i : ℕ) :
      sieveMu.map (fun ω => (sieveX i ω, sieveY i ω)) = sieveNu := by
    rw [hpair i]
    exact Measure.infinitePi_map_eval (fun _ : ℕ => sieveNu) i
  have hindep : iIndepFun (fun i ω => (sieveX i ω, sieveY i ω)) sieveMu := by
    exact
      (iIndepFun_infinitePi (P := fun _ : ℕ => sieveNu)
        (X := fun _ : ℕ => (id : ℝ × ℝ → ℝ × ℝ)) (fun _ => measurable_id))
  have hiid : IID sieveMu (fun i ω => (sieveX i ω, sieveY i ω)) := by
    refine ⟨hm, hindep, ?_⟩
    intro i
    exact ⟨(hm i).aemeasurable, (hm 0).aemeasurable,
      (hlaw i).trans (hlaw 0).symm⟩
  have hXlaw : sieveMu.map (sieveX 0) = uniformLaw 0 1 := by
    change sieveMu.map (Prod.fst ∘ (fun ω => (sieveX 0 ω, sieveY 0 ω))) = _
    rw [← Measure.map_map measurable_fst (hm 0), hlaw 0]
    simp only [sieveNu, Measure.map_fst_prod, measure_univ, one_smul]
  exact ⟨hprob, hiid, hlaw 0, hXlaw⟩

end

end AronowAudit.P001.Wave1.SieveRate
