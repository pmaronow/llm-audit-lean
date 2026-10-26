import AronowAudit.P047.Wave1.ImpossibilityBlueprint
import Mathlib.Order.LiminfLimsup

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

theorem n17_proof : N17.{u} := by
  classical
  intro R _ Q _ E _hE hrisk
  have hbounded (n : ℕ) (η : ℝ) : BddAbove
      (insert (0 : ℝ) {r | ∃ L : CausalLaw, UnknownModel L ∧
        r = ((sampleLaw L.measure).prod Q).real
          {z | η < |E n (observedSample n z.1, z.2) - ate L|}}) := by
    refine ⟨1, ?_⟩
    rintro r (rfl | ⟨L, _hL, rfl⟩)
    · norm_num
    · exact measureReal_le_one
  have hnonneg (n : ℕ) : 0 ≤ randStrictRisk Q E n (1 / 24) :=
    le_csSup (hbounded n (1 / 24)) (Set.mem_insert _ _)
  have hcomparison (n : ℕ) :
      randRisk Q E n (1 / 12) ≤ randStrictRisk Q E n (1 / 24) := by
    unfold randRisk
    apply csSup_le (Set.insert_nonempty _ _)
    rintro r (rfl | ⟨L, hL, rfl⟩)
    · exact hnonneg n
    · have hinclusion :
          {z : _ × R | (1 / 12 : ℝ) ≤ |E n (observedSample n z.1, z.2) - ate L|} ⊆
          {z : _ × R | (1 / 24 : ℝ) < |E n (observedSample n z.1, z.2) - ate L|} := by
        intro z hz
        change (1 / 12 : ℝ) ≤ _ at hz
        change (1 / 24 : ℝ) < _
        linarith
      refine (measureReal_mono hinclusion).trans ?_
      exact le_csSup (hbounded n (1 / 24)) (Set.mem_insert_of_mem _ ⟨L, hL, rfl⟩)
  have hupper (n : ℕ) : randStrictRisk Q E n (1 / 24) ≤ 1 := by
    apply csSup_le (Set.insert_nonempty _ _)
    rintro r (rfl | ⟨L, _hL, rfl⟩)
    · norm_num
    · exact measureReal_le_one
  have heventually : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) ≤ randStrictRisk Q E n (1 / 24) := by
    exact Filter.eventually_atTop.mpr ⟨1, fun n hn =>
      (hrisk n hn).trans (hcomparison n)⟩
  have hlim : (1 / 2 : ℝ) ≤
      Filter.limsup (fun n => randStrictRisk Q E n (1 / 24)) atTop :=
    Filter.le_limsup_of_frequently_le heventually.frequently
      (Filter.isBoundedUnder_of ⟨1, hupper⟩)
  exact ⟨1 / 24, by norm_num, lt_of_lt_of_le (by norm_num) hlim⟩

end

end AronowAudit.P047.Wave1.Impossibility
