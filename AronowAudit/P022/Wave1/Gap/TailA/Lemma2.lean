import AronowAudit.P022.Wave1.Lib.TailA.AtomEndpoints

namespace AronowAudit.P022.Wave1.TailA

set_option autoImplicit false

/-- Corrected Lemma 2 with the explicit universal partition. -/
theorem lemma2_corrected_final : (∀ (S : ExperimentSequence)
      (H : JointLaw)
      (θ ρ : ℝ)
      (h : Conditions123 S H θ ρ)
      (hleft : AtomLeftConvergence S H),
      Lemma2Conclusions S H θ ρ) := by
  intro S H θ ρ h hleft
  obtain ⟨hpos, hanti, huniform, htail⟩ :=
    lemma2_corrected_explicit_final S H θ ρ h hleft
  refine ⟨huniform, correctedPartitionInteger, correctedPartitionInteger,
    ?_, ?_, ?_, ?_⟩
  · intro η hη
    exact ⟨hpos η hη, hpos η hη⟩
  · intro a b ha hab
    exact ⟨hanti a b ha hab, hanti a b ha hab⟩
  · intro η hη
    exact (htail η hη).1
  · intro η hη
    exact (htail η hη).2

end AronowAudit.P022.Wave1.TailA
