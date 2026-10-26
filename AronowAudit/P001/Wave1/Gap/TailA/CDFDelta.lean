import AronowAudit.P001.Wave1.Gap.TailA.CDFProcess
import AronowAudit.P001.Wave1.Lib.TailA.CDFLinearImage
import AronowAudit.P001.Wave1.Lib.TailA.OuterHadamardDelta

/-! Empirical-CDF delta limits with the derivative-image law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AronowAudit.P001.Wave1.TailA

/-- The full process limit and nondegenerate scalar functional limit. -/
theorem empirical_cdf_delta_nondegenerate_final :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      [MeasurableSpace KolmogorovSpace]
      [BorelSpace KolmogorovSpace]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℝ)
      (hiid : IID μ X)
      (T : KolmogorovSpace → ℝ)
      (L : KolmogorovSpace →L[ℝ] ℝ)
      (hd : HadamardAt cdfDomain (CDFTangent (cdf μ (X 0))) T (kolmogorovEmbed (cdf μ (X 0))) L)
      (νB : Measure KolmogorovSpace)
      [IsProbabilityMeasure νB]
      (hbridge : IsCDFBridge (cdf μ (X 0)) νB)
      (hstat : ∀ n, Measurable (fun ω => T (empiricalCDFElement X n ω)))
      (hL2 : MemLp (fun h => L h) 2 νB)
      (hv : 0 < var νB (fun h => L h)),
      OuterWeakLimit μ (fun n ω => Real.sqrt n •
    (empiricalCDFElement X n ω-kolmogorovEmbed (cdf μ (X 0)))) νB ∧
  CD μ (fun n ω => Real.sqrt n*(T (empiricalCDFElement X n ω)-
    T (kolmogorovEmbed (cdf μ (X 0)))))
    (gaussianReal 0 ⟨var νB (fun h => L h), le_of_lt hv⟩)) := by
  intro Ω mΩ mK bK μ pμ X hiid T L hd νB pν hbridge hstat hL2 hv
  have hprocess := iid_empirical_cdf_bridge_limit_final μ X hiid νB hbridge
  have hF := CondP001cd_cdf_law μ (X 0) (hiid.1 0)
  have htot : TotallyBounded (Set.range (cdf μ (X 0))) := by
    rw [hF]
    exact cdf_value_totallyBounded (μ.map (X 0))
  have hθ : kolmogorovEmbed (cdf μ (X 0)) ∈ cdfDomain := by
    rw [hF]
    exact CondP001cd_cdf_domain (μ.map (X 0))
  have hD : ∀ᶠ n in atTop, ∀ ω, empiricalCDFElement X n ω ∈ cdfDomain := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    intro ω
    let instEmpirical : IsProbabilityMeasure (empirical X n ω) :=
      CondP001cd_empirical_probability X hn ω
    exact CondP001cd_cdf_domain (empirical X n ω)
  have htight := cdf_bridge_tight (μ.map (X 0)) νB (hF ▸ hbridge)
  have hdelta := outer_hadamard_delta_real μ cdfDomain (CDFTangent (cdf μ (X 0)))
    (kolmogorovEmbed (cdf μ (X 0))) hθ (cdf_tangent_closed _)
    (cdf_tangent_separable _ htot) T L hd (empiricalCDFElement X) hD
    (fun n => Real.sqrt n) (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    νB hbridge.1 htight hprocess hstat
  have hgauss := cdf_bridge_linear_gaussian (μ.map (X 0)) νB (hF ▸ hbridge) L hL2
  have hvnn : (var νB (fun h => L h)).toNNReal =
      ⟨var νB (fun h => L h), hv.le⟩ := by
    exact Real.toNNReal_of_nonneg hv.le
  rw [hvnn] at hgauss
  exact ⟨hprocess, hgauss ▸ hdelta.2⟩

/-- The full nondegenerate functional delta correction. -/
theorem functional_delta_nondegenerate_correction_final :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      [MeasurableSpace KolmogorovSpace]
      [BorelSpace KolmogorovSpace]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℝ)
      (hiid : IID μ X)
      (T : KolmogorovSpace → ℝ)
      (L : KolmogorovSpace →L[ℝ] ℝ)
      (hd : HadamardAt cdfDomain (CDFTangent (cdf μ (X 0))) T (kolmogorovEmbed (cdf μ (X 0))) L)
      (νB : Measure KolmogorovSpace)
      [IsProbabilityMeasure νB]
      (hbridge : IsCDFBridge (cdf μ (X 0)) νB)
      (hstat : ∀ n, Measurable (fun ω => T (empiricalCDFElement X n ω)))
      (hL2 : MemLp (fun h => L h) 2 νB)
      (hv : 0 < var νB (fun h => L h)),
      OuterWeakLimit μ (fun n ω => Real.sqrt n •
    (empiricalCDFElement X n ω-kolmogorovEmbed (cdf μ (X 0)))) νB ∧
  CD μ (fun n ω => Real.sqrt n*(T (empiricalCDFElement X n ω)-
    T (kolmogorovEmbed (cdf μ (X 0)))))
    (gaussianReal 0 ⟨var νB (fun h => L h), le_of_lt hv⟩)) :=
  @empirical_cdf_delta_nondegenerate_final

/-- The full process limit and nondegenerate scalar functional limit
in the Kolmogorov embedding. -/
theorem kolmogorov_embedding_preserves_cdf_final :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      [MeasurableSpace KolmogorovSpace]
      [BorelSpace KolmogorovSpace]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℝ)
      (hiid : IID μ X)
      (T : KolmogorovSpace → ℝ)
      (L : KolmogorovSpace →L[ℝ] ℝ)
      (hd : HadamardAt cdfDomain (CDFTangent (cdf μ (X 0))) T (kolmogorovEmbed (cdf μ (X 0))) L)
      (νB : Measure KolmogorovSpace)
      [IsProbabilityMeasure νB]
      (hbridge : IsCDFBridge (cdf μ (X 0)) νB)
      (hstat : ∀ n, Measurable (fun ω => T (empiricalCDFElement X n ω)))
      (hL2 : MemLp (fun h => L h) 2 νB)
      (hv : 0 < var νB (fun h => L h)),
      OuterWeakLimit μ (fun n ω => Real.sqrt n •
    (empiricalCDFElement X n ω-kolmogorovEmbed (cdf μ (X 0)))) νB ∧
  CD μ (fun n ω => Real.sqrt n*(T (empiricalCDFElement X n ω)-
    T (kolmogorovEmbed (cdf μ (X 0)))))
    (gaussianReal 0 ⟨var νB (fun h => L h), le_of_lt hv⟩)) :=
  @empirical_cdf_delta_nondegenerate_final

end AronowAudit.P001.Wave1.TailA
