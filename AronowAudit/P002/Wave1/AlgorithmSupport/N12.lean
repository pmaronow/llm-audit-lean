import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint

/-! # Algorithm 2: the closed pieces cover the real line -/

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- The terminal piece reaches infinity and each successor starts at its
predecessor's right endpoint; induction therefore covers everything to the right
of the first left endpoint. -/
theorem n12_proof : N12 := by
  intro hcons M g α J pieces hRun
  obtain ⟨_hJ, _hJne, hpiecesne, hinit, hsteps⟩ := hRun
  have htail : ∀ (rest : List (RecordedPiece M)) (p : RecordedPiece M),
      (∀ i : Fin (p :: rest).length,
        Algorithm2Step g α J ((p :: rest).get i) ((p :: rest)[i.val + 1]?)) →
      ∀ β : ℝ, p.left ≤ (β : EReal) →
        ∃ q ∈ p :: rest, β ∈ closedInterval q.left q.right := by
    intro rest
    induction rest with
    | nil =>
        intro p hsteps' β hβ
        obtain ⟨hpstep, _⟩ :=
          (hcons (Algorithm2Step g α J) p []).mp hsteps'
        have htop : p.right = ⊤ := hpstep.2
        refine ⟨p, by simp, hβ, ?_⟩
        rw [htop]
        exact le_top
    | cons q rest ih =>
        intro p hsteps' β hβ
        obtain ⟨hpstep, hrest⟩ :=
          (hcons (Algorithm2Step g α J) p (q :: rest)).mp hsteps'
        have hmeet : q.left = p.right := hpstep.2.2.1
        by_cases hright : (β : EReal) ≤ p.right
        · exact ⟨p, by simp, hβ, hright⟩
        · have hqβ : q.left ≤ (β : EReal) := by
            rw [hmeet]
            exact le_of_lt (lt_of_not_ge hright)
          obtain ⟨r, hr, hβr⟩ := ih q hrest β hqβ
          exact ⟨r, List.mem_cons_of_mem p hr, hβr⟩
  cases pieces with
  | nil => exact (hpiecesne rfl).elim
  | cons p rest =>
      intro β
      have hbot : p.left = ⊥ := (hinit p rfl).1
      apply htail rest p hsteps β
      rw [hbot]
      exact bot_le

end
end AronowAudit.P002.Wave1.AlgorithmSupport
