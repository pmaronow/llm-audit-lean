import AronowAudit.P022.Wave1.Lib.TailA.AtomEndpoints

namespace AronowAudit.P022.Wave1.TailA

set_option autoImplicit false

/-- Corrected Lemma 2 with the exact held type and the explicit universal partition. -/
theorem lemma2_corrected_final : type_of% @AronowAudit.P022.lemma2_corrected := by
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

example : type_of% @AronowAudit.P022.lemma2_corrected := AronowAudit.P022.Wave1.TailA.lemma2_corrected_final

end AronowAudit.P022.Wave1.TailA
