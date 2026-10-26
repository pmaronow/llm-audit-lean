import AronowAudit.P044.P044_NetworkSpillovers

namespace AronowAudit.P044.Wave1

open Finset
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- P044-T13: the generator baseline law differs from the absolute standard
normal law at every unit of every finite loopless graph. -/
theorem baseline_description_refuted_for_every_graph
    (N : ℕ) (A : AronowAudit.P044.Adjacency N)
    (_hdiag : ∀ i, A i i = false) (i : Fin N) :
    AronowAudit.P044.baselineLaw (AronowAudit.P044.degreeScale A i : ℝ) ≠
      AronowAudit.P044.halfNormalLaw := by
  exact (AronowAudit.P044.baseline_not_halfNormal
    (AronowAudit.P044.degreeScale A i : ℝ) (by positivity)).2.2

end

end AronowAudit.P044.Wave1
