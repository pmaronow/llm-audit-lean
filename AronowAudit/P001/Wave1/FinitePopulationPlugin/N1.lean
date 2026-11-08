import AronowAudit.P001.Wave1.FinitePopulationPluginBlueprint

/-! Node N1 (= Target) of the P001-T50 blueprint (trivial; written by the blueprint
architect): every clause is a proved frozen theorem or one line of algebra. -/

namespace AronowAudit.P001.Wave1.FinitePopulationPlugin

open AronowAudit.P001 MeasureTheory

theorem n1_proof : N1 := by
  intro Ω _ μ _ Z hZ
  obtain ⟨hpop, h3, h4, h10, hm, hv⟩ := finite_population_example_moments
  have hvar := variance_functional_minus_sign μ Z hZ
  exact ⟨hpop, ⟨h3, h4, h10, hm, hv⟩, hvar, by rw [hvar]; ring,
    fun x n hn => empirical_variance_identity x n hn⟩

end AronowAudit.P001.Wave1.FinitePopulationPlugin
