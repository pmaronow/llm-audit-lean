import AronowAudit.P022.Wave1.RandomizationVariance.N4

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.RandomizationVariance
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators
noncomputable section

theorem n2_proof : N2 := by
  intro d y1 y0 π
  have hm : NeZero d.m := ⟨by have := d.treatment_min; omega⟩
  have hk : NeZero d.k := ⟨by have := d.control_min; omega⟩
  rw [Finset.sum_add_distrib, sum_treat_mul, sum_ctrl_mul]
  change finiteMean (observedTreatment d y1 π) - finiteMean (observedControl d y0 π) -
      (finiteMean y1 - finiteMean y0) = _
  have h1 : (∑ i : Fin d.m, (y1 (π ⟨i.val, by have := d.sample_le; omega⟩) - finiteMean y1)) /
      (d.m : ℝ) = finiteMean (observedTreatment d y1 π) - finiteMean y1 := by
    have hh : finiteMean (fun i => observedTreatment d y1 π i - finiteMean y1) =
        finiteMean (observedTreatment d y1 π) - finiteMean y1 := by
      unfold finiteMean
      rw [Finset.expect_sub_distrib, Finset.expect_const Finset.univ_nonempty]
    simpa only [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin, observedTreatment] using hh
  have h0 : (∑ i : Fin d.k, (y0 (π ⟨d.m + i.val, by have := d.sample_le; omega⟩) - finiteMean y0)) /
      (d.k : ℝ) = finiteMean (observedControl d y0 π) - finiteMean y0 := by
    have hh : finiteMean (fun i => observedControl d y0 π i - finiteMean y0) =
        finiteMean (observedControl d y0 π) - finiteMean y0 := by
      unfold finiteMean
      rw [Finset.expect_sub_distrib, Finset.expect_const Finset.univ_nonempty]
    simpa only [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin, observedControl] using hh
  rw [neg_div, h1, h0]
  ring

end
end AronowAudit.P022.Wave1.RandomizationVariance
