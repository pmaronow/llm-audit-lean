import AronowAudit.P011.Wave1.CorollaryOneBlueprint
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.CorollaryOne

open AronowAudit.P011 AronowAudit.P011.Wave1.PropositionOne MeasureTheory ProbabilityTheory
  Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- The underestimate event has probability tending to one at epsilon one. -/
theorem n3_proof : N3 := by
  intro F T V c a hidentity hT hgap
  classical
  let bad (k : ℕ) : Set (Fin (F.size k) → ℝ) := {y | |T k y - a| > 1}
  let under (k : ℕ) : Set (Fin (F.size k) → ℝ) :=
    {y | (F.size k : ℝ) * (var (F.model k) (betaHat (F.model k)) - V k y) > 1}
  have hbad : Tendsto (fun k => probability (F.model k) (bad k)) atTop (𝓝 0) :=
    hT 1 (by norm_num)
  have hcover (k : ℕ) : bad k ∪ under k = Set.univ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      by_cases hy : |T k y - a| > 1
      · exact Or.inl hy
      · apply Or.inr
        have hupper : T k y - a ≤ 1 := (abs_le.mp (le_of_not_gt hy)).2
        change 1 < (F.size k : ℝ) *
          (var (F.model k) (betaHat (F.model k)) - V k y)
        rw [hidentity k y]
        linarith
  have hlower (k : ℕ) :
      1 - probability (F.model k) (bad k) ≤ probability (F.model k) (under k) := by
    letI : IsProbabilityMeasure (F.model k).law := (F.model k).probability
    -- A union bound works for arbitrary sets; N3 assumes no measurability of T or V.
    have h := measureReal_union_le (μ := (F.model k).law) (bad k) (under k)
    rw [hcover k, probReal_univ] at h
    change 1 ≤ probability (F.model k) (bad k) +
      probability (F.model k) (under k) at h
    linarith
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hleft : Tendsto (fun k => 1 - probability (F.model k) (bad k)) atTop (𝓝 1) := by
    simpa only [sub_zero] using hone.sub hbad
  have hunder : Tendsto (fun k => probability (F.model k) (under k)) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hleft hone hlower ?_
    intro k
    letI : IsProbabilityMeasure (F.model k).law := (F.model k).probability
    exact measureReal_le_one
  intro hcons
  have hzero : Tendsto (fun k => probability (F.model k) (under k)) atTop (𝓝 0) :=
    hcons 1 (by norm_num)
  have hcontr : (1 : ℝ) = 0 := tendsto_nhds_unique hunder hzero
  norm_num at hcontr

end

end AronowAudit.P011.Wave1.CorollaryOne
