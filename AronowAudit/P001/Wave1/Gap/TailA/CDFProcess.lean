import AronowAudit.P001.Wave1.Lib.TailA.CDFDonsker

/-! The empirical-CDF process limit with its law identified. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AronowAudit.P001.Wave1.TailA

/-- The supplied tangent-supported CDF bridge is the Donsker limit law. -/
theorem iid_empirical_cdf_bridge_limit_final :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      [MeasurableSpace KolmogorovSpace]
      [BorelSpace KolmogorovSpace]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℝ)
      (hiid : IID μ X)
      (νB : Measure KolmogorovSpace)
      [IsProbabilityMeasure νB]
      (hbridge : IsCDFBridge (cdf μ (X 0)) νB),
      OuterWeakLimit μ (fun n ω => Real.sqrt n •
    (empiricalCDFElement X n ω-kolmogorovEmbed (cdf μ (X 0)))) νB) := by
  intro Ω mΩ mK bK μ pμ X hiid νB pν hbridge
  obtain ⟨ν, hp, ht, hb, hw⟩ := cdf_donsker_supported μ X hiid
  have hF := CondP001cd_cdf_law μ (X 0) (hiid.1 0)
  have heq : ν = νB := cdf_bridge_unique (μ.map (X 0)) ν νB
    (hF ▸ hb) (hF ▸ hbridge)
  exact heq ▸ hw

end AronowAudit.P001.Wave1.TailA
