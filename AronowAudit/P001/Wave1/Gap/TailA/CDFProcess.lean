import AronowAudit.P001.Wave1.Lib.TailA.CDFDonsker

/-! The exact held empirical-CDF process row, with the constructed law identified. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AronowAudit.P001.Wave1.TailA

/-- The supplied tangent-supported CDF bridge is the Donsker limit law. -/
theorem iid_empirical_cdf_bridge_limit_final :
    type_of% @AronowAudit.P001.iid_empirical_cdf_bridge_limit := by
  intro Ω mΩ mK bK μ pμ X hiid νB pν hbridge
  obtain ⟨ν, hp, ht, hb, hw⟩ := cdf_donsker_supported μ X hiid
  have hF := CondP001cd_cdf_law μ (X 0) (hiid.1 0)
  have heq : ν = νB := cdf_bridge_unique (μ.map (X 0)) ν νB
    (hF ▸ hb) (hF ▸ hbridge)
  exact heq ▸ hw

example : type_of% @AronowAudit.P001.iid_empirical_cdf_bridge_limit := AronowAudit.P001.Wave1.TailA.iid_empirical_cdf_bridge_limit_final

end AronowAudit.P001.Wave1.TailA
