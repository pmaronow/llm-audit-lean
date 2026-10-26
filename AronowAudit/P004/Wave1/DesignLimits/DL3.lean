import AronowAudit.P004.Wave1.DesignLimits.DL1

namespace AronowAudit.P004.Wave1.DesignLimits

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Domination on a good event with vanishing exceptional probability. -/
theorem dl3_proof : DL3 := by
  classical
  intro p hp U W Good hbad hdom hW ε hε
  have hupper : Tendsto (fun N => prob (p N) (fun z => ¬ Good N z) +
      prob (p N) (fun z => ε < |W N z|)) atTop (nhds 0) := by
    simpa only [zero_add] using hbad.add (hW ε hε)
  have hbound : ∀ᶠ N in atTop, prob (p N) (fun z => ε < |U N z|) ≤
      prob (p N) (fun z => ¬ Good N z) + prob (p N) (fun z => ε < |W N z|) := by
    filter_upwards [hdom] with N hN
    apply prob_le_add_of_imp_finite (p N) (hp N)
    intro z hz
    by_cases hg : Good N z
    · exact Or.inr (lt_of_lt_of_le hz (hN z hg))
    · exact Or.inl hg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall (fun N => prob_nonneg_finite (p N) (hp N) _)) hbound

end
end AronowAudit.P004.Wave1.DesignLimits
