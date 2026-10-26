import AronowAudit.P011.Wave1.CorollaryThreeBlueprint
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.CorollaryThree

open AronowAudit.P011 AronowAudit.P011.Wave1.PropositionOne AronowAudit.P011.Wave1.CorollaryOne
  MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- Nonnegativity is contained in a fixed positive deviation from the negative limit. -/
theorem n1_proof : N1 := by
  intro F T a ha hT
  have heps : 0 < -a / 2 := by linarith
  have htail := hT (-a / 2) heps
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => measureReal_nonneg) ?_
  intro k
  letI : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro y hy
  change 0 ≤ T k y at hy
  change -a / 2 < |T k y - a|
  have habs : T k y - a ≤ |T k y - a| := le_abs_self _
  linarith

end

end AronowAudit.P011.Wave1.CorollaryThree
