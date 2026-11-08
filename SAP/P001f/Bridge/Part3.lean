import SAP.P001f.Bridge.Part1
import AronowAudit.P001.Wave1.SampleMean
import AronowAudit.P001.Wave1.PolynomialBlp
import AronowAudit.P001.Wave1.MarDiscrete
import AronowAudit.P001.Wave1.MarVector
import AronowAudit.P001.Wave1.McarMean
import AronowAudit.P001.Wave1.MarBalance
import AronowAudit.P001.Wave1.MissingDr
import AronowAudit.P001.Wave1.AteSharpBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001f.Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
universe u v

theorem transportT106 : T106Statement.{u} := by
  intro Ω _ μ _
  constructor
  · intro X Y hX hY a b c
    exact AronowAudit.P001.expectation_linearity μ X Y hX hY a b c
  · intro X hX a c
    obtain ⟨halt, hshift, hscale⟩ := AronowAudit.P001.variance_affine_rules μ X hX a c
    have hs := AronowAudit.P001.standard_deviation_rules μ X hX a c
    refine ⟨halt, hshift, hscale, hs.1, hs.2, ?_⟩
    intro hv ε hε
    exact AronowAudit.P001.chebyshev_standard_deviations μ X hX hv ε hε

theorem transportT107 : T107Statement.{u, v} := by
  exact @AronowAudit.P001.iterated_expectation

theorem transportT108 : T108Statement.{u} := by
  exact @AronowAudit.P001.Wave1.sample_mean_paper_contract

theorem transportT109 : T109Statement.{u} := by
  exact ⟨AronowAudit.P001.weierstrass_approximation,
    @AronowAudit.P001.Wave1.polynomial_blp_paper_support_approximation⟩

theorem transportT110 : T110Statement := by
  classical
  constructor
  · intro n hn Y
    obtain ⟨ha, hmax⟩ := AronowAudit.P001.bernoulli_ml_unique_sample_fraction hn Y
    refine ⟨ha, ?_, hmax⟩
    simp only [Finset.sum_boole]
  · exact AronowAudit.P001.three_coin_flips_maximum

theorem transportT111 : T111Statement.{u, v} := by
  exact ⟨@AronowAudit.P001.Wave1.mcar_paper_support_mean,
    @AronowAudit.P001.Wave1.mar_discrete_paper_support_identification,
    @AronowAudit.P001.Wave1.mar_vector_paper_support_cef,
    AronowAudit.P001.missing_mcar_mar_sample_estimates⟩

theorem transportT112 : T112Statement.{u} := by
  intro Ω _ K μ _ X hX Y R hY hR hb hR0 hR1 p hp hCI ε hε hpos
  obtain ⟨hbalance, hmar, hself, hbound⟩ :=
    AronowAudit.P001.Wave1.mar_propensity_paper_support_balance
      μ X hX Y R hY hR hb hR0 hR1 p hp hCI ε hε hpos
  exact ⟨hbalance, hmar, hself, ε, hε, hbound⟩

theorem transportT113 : T113Statement.{u} := by
  exact @AronowAudit.P001.Wave1.missing_double_robustness_paper_support

theorem transportT114 : T114Statement.{u} := by
  exact ⟨@AronowAudit.P001.Wave1.ate_sharp_paper_bounds_same_observable_law,
    AronowAudit.P001.binary_causal_sample_bound_estimates⟩

end
end SAP.P001f.Bridge
