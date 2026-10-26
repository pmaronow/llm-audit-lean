import AronowAudit.P004.Wave1.PairedWitnessBlueprint

namespace AronowAudit.P004.Wave1.PairedWitness

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators Classical

theorem pw1_proof : PW1 := by
  change LogisticConditions pairO pairTheta pairThetaSet pairThetaHat
  unfold LogisticConditions
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isCompact_singleton
  · exact Set.mem_singleton _
  · refine ⟨1, ?_⟩
    intro N i j
    norm_num [pairO]
  · refine ⟨1, by norm_num, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    intro v
    have hNr : (N : ℝ) ≠ 0 := by
      exact_mod_cast (show N ≠ 0 by omega)
    have hdot : ∀ i : Fin N, dot (pairO N i) v = v 0 := by
      intro i
      simp [dot, pairO, Fin.sum_univ_one]
    simp only [hdot, Fin.sum_univ_one, one_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have havg : (N : ℝ) * (v 0) ^ 2 / (N : ℝ) = (v 0) ^ 2 := by
      field_simp [hNr] <;> ring
    rw [havg]
  · intro N z
    refine ⟨Set.mem_singleton _, ?_⟩
    intro θ hθ
    have heq : θ = pairTheta := Set.mem_singleton_iff.mp hθ
    subst θ
    exact le_rfl

end
end AronowAudit.P004.Wave1.PairedWitness
