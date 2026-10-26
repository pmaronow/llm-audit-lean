import AronowAudit.P041.P041_Risks

noncomputable section
namespace AronowAudit.P041

/-- Refutation of the printed directional percentage claims. -/
theorem printed_directional_percentages_refuted :
    ¬ (roundsWhole (relativeIncrease (75/150) (52/150)) 36 ∧
    roundsWhole (relativeIncrease (92/150) (69/150)) 29 ∧
    roundsWhole (relativeIncrease (62/100) (32/100)) 64) := by
  norm_num [relativeIncrease, roundsWhole]

end AronowAudit.P041

