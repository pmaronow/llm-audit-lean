import SAP.P001f.Bridge.Part1
import SAP.P001f.Bridge.T102PDFSupport
import AronowAudit.P001.Wave1.Gap.DecideA
import AronowAudit.P001.Wave1.Checks.FidP001Contracts
import AronowAudit.P001.Wave1.MixtureMaximum
import AronowAudit.P001.P001_PrintedRefutations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001f.Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
universe u v

theorem transportT96 : T96Statement := by
  refine ⟨AronowAudit.P001.causal_ipw_logit_ml_counterexample, ?_, ?_,
    AronowAudit.P001.causal_ipw_not_poststratified, ?_⟩
  · intro j
    fin_cases j <;> norm_num [causalTreatedCounts, causalSizes]
  · norm_num
  · norm_num

theorem transportT97 : T97Statement.{v} := by
  intro E _ _ n hn nt nc q ht hc hq
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := AronowAudit.P001.causal_ipw_saturation_necessary nt nc q ht hc hq
  constructor
  · intro hall
    apply h.mp
    intro st sc
    exact (div_left_inj' hn0).mp (hall st sc)
  · intro hs st sc
    exact congrArg (fun x : ℝ => x / (n : ℝ)) (h.mpr hs st sc)

theorem transportT98 : T98Statement.{u, v} := by
  intro Ω E _ _ μ _ X D hiid p hp hb hpos
  have hX : Measurable (X 0) := measurable_fst.comp (hiid.1 0)
  have hD : Measurable (D 0) := measurable_snd.comp (hiid.1 0)
  have hpos0 : ∃ ε : ℝ, 0 < ε ∧ ∀ ω, ε < p (X 0 ω) ∧ p (X 0 ω) < 1 - ε := by
    obtain ⟨ε, hε, hh⟩ := hpos
    exact ⟨ε, hε, hh 0⟩
  exact ⟨AronowAudit.P001.treatment_weights_denominators_correction μ (X 0) hX
    (D 0) hD (hb 0) p hp hpos0,
    AronowAudit.P001.treatment_weight_sample_means μ X D hiid p hp hb hpos⟩

theorem transportT99 : T99Statement := by
  classical
  obtain ⟨hci, hp, hlo, hhi, hatt, hw, hne⟩ :=
    AronowAudit.P001.att_counterexample_with_ignorability
  have hci' := (finiteConditionalIndependence_iff AronowAudit.P001.attWitness
    (fun _ => ((0 : ℝ), (1 : ℝ))) (![0, 1] : Fin 2 → ℝ) (fun _ => (0 : ℝ))).mpr hci
  refine ⟨?_, ?_, ?_, ?_, hci', hp, ⟨hlo, hhi⟩, ?_, hw, hatt, hne, ?_⟩
  · intro i
    fin_cases i <;> norm_num [attWeights]
  · norm_num [attWeights, Fin.sum_univ_succ]
  · norm_num [finiteProbability, attWeights, Fin.sum_univ_succ]
  · norm_num [finiteProbability, attWeights, Fin.sum_univ_succ]
  · norm_num
  · have hn := AronowAudit.P001.att_normalization_counterexample
    calc
      _ = (1 / 4 : ℝ) / (1 / 4) := by
        congr 1
        · exact hn.1
        · norm_num [finiteMean, attWeights, Fin.sum_univ_succ]
      _ = 1 := hn.2.2.2
      _ = _ := hn.2.1.symm

theorem transportT100 : T100Statement.{u, v} := by
  intro Ω E _ _ μ _ X hX Y0 Y1 D h0 h1 hD hiτ hb hpD p hp hCI
  obtain ⟨hden, hw, hn⟩ :=
    AronowAudit.P001.Wave1.att_normalized_propensity_mean_integrable_effect
      μ X hX Y0 Y1 D h0 h1 hD hiτ hb hpD p hp hCI
  let P := (μ {ω | D ω = 1}).toReal
  let W := ∫ ω, p (X ω) * (Y1 ω - Y0 ω) ∂μ
  let A := eventMean μ D (fun ω => Y1 ω - Y0 ω) 1
  have hden' : (∫ ω, p (X ω) ∂μ) = P := hden
  have hn' : A = W / P := by
    rw [← hden']
    exact hn
  have hWA : W = P * A := by
    have hh := (eq_div_iff hpD.1.ne').mp hn'
    nlinarith
  refine ⟨hden, hpD.1, hw, hWA, hn, ?_⟩
  change W = A ↔ P = 1 ∨ A = 0
  constructor
  · intro he
    have hz : (P - 1) * A = 0 := by nlinarith [hWA]
    simpa only [mul_eq_zero, sub_eq_zero] using hz
  · rintro (he | he)
    · simpa only [he, one_mul] using hWA
    · calc
        W = P * A := hWA
        _ = A := by rw [he, mul_zero]

theorem transportT101 : T101Statement.{u} := by
  intro Ω A B
  exact ⟨rfl, AronowAudit.P001.relative_complement A B⟩

theorem pdaWellDefined_iff : PDAWellDefined.{u} ↔
    AronowAudit.P001.Wave1.FidP001Contracts.printedContract_P001_T102.{u} := Iff.rfl

theorem transportT102 : T102Statement.{u} := by
  constructor
  · exact T102_pdf_support_identification_refuted
  · intro Ω K X mhat n _ ω k _
    exact AronowAudit.P001.printed_pda_plugin_formula X mhat n ω k

theorem transportT103 : T103Statement := by
  exact AronowAudit.P001.Wave1.printed_unrestricted_mixture_maximum_refuted

theorem overlapEquivalence_iff : OverlapUniformPositivityEquivalence ↔
    AronowAudit.P001.PrintedConfidence.PrintedOverlapUniformPositivityConverse := Iff.rfl

theorem transportT104 : T104Statement := by
  exact AronowAudit.P001.PrintedConfidence.printed_overlap_uniform_positivity_converse_refuted

end
end SAP.P001f.Bridge
