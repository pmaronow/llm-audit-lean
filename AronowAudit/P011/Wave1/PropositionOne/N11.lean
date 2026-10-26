import AronowAudit.P011.Wave1.PropositionOneBlueprint

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PropositionOne

open AronowAudit.P011 MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

theorem n11_proof : N11 := by
  classical
  intro F T a b hab ha hb
  have hcover (k : ℕ) :
      Set.univ ⊆ {y | |T k y - a| > 1} ∪ {y | |T k y - b| > 1} := by
    intro y _
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at h
    have htriangle : |a - b| ≤ |T k y - a| + |T k y - b| := by
      calc
        |a - b| = |(T k y - b) + -(T k y - a)| := by
          congr 1
          ring
        _ ≤ |T k y - b| + |-(T k y - a)| := abs_add_le _ _
        _ = |T k y - a| + |T k y - b| := by rw [abs_neg, add_comm]
    linarith
  have hmass (k : ℕ) :
      1 ≤ probability (F.model k) {y | |T k y - a| > 1} +
        probability (F.model k) {y | |T k y - b| > 1} := by
    letI : IsProbabilityMeasure (F.model k).law := (F.model k).probability
    calc
      1 = (F.model k).law.real Set.univ := probReal_univ.symm
      _ ≤ (F.model k).law.real
          ({y | |T k y - a| > 1} ∪ {y | |T k y - b| > 1}) :=
        measureReal_mono (hcover k)
      _ ≤ _ := measureReal_union_le _ _
  have hlim := (ha 1 (by norm_num)).add (hb 1 (by norm_num))
  have hfalse : (1 : ℝ) ≤ 0 := by
    simpa only [zero_add] using ge_of_tendsto hlim (Eventually.of_forall hmass)
  norm_num at hfalse

end

end AronowAudit.P011.Wave1.PropositionOne
