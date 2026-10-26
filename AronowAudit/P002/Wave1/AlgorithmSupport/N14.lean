import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Split the step condition at the zero index; successor indices are exactly
the indices of the tail. The index shifts reduce definitionally. -/
theorem n14_proof : N14 := by
  intro X R p rest
  change
    (∀ i : Fin (rest.length + 1),
      R ((p :: rest).get i) ((p :: rest)[i.val + 1]?)) ↔
      (R p rest.head? ∧
        ∀ i : Fin rest.length, R (rest.get i) (rest[i.val + 1]?))
  rw [Fin.forall_fin_succ]
  constructor
  · rintro ⟨hzero, hsucc⟩
    constructor
    · change R p (rest[0]?) at hzero
      simpa only [List.head?_eq_getElem?] using hzero
    · intro i
      have hi := hsucc i
      change R (rest.get i) (rest[i.val + 1]?) at hi
      exact hi
  · rintro ⟨hzero, hsucc⟩
    constructor
    · change R p (rest[0]?)
      simpa only [List.head?_eq_getElem?] using hzero
    · intro i
      change R (rest.get i) (rest[i.val + 1]?)
      exact hsucc i

end
end AronowAudit.P002.Wave1.AlgorithmSupport
