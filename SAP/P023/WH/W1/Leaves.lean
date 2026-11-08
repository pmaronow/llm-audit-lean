import SAP.P023.Defs.WholeW1
import SAP.P023.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P023.WH.W1
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open SAP.P023.Bridge
open AronowAudit.P023.Wave1

/-! All remaining steps are donor applications or short arguments, proved here.
There are no unproved mathematical leaves in this group. -/

/-- Transport a finite real-risk comparison to every measurable predictor.
An integrable loss uses the Bochner/nonnegative integral identity; a
nonintegrable nonnegative measurable loss has infinite extended risk. -/
theorem extend_risk_bound (ν : Measure (ℝ × ℝ)) (R B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ f : ℝ → ℝ, Measurable f →
      Integrable (fun z => (z.2-f z.1)^2) ν → R-predictionRisk ν f ≤ B)
    (f : ℝ → ℝ) (hf : Measurable f) :
    ENNReal.ofReal R ≤ extendedPredictionRisk ν f + ENNReal.ofReal B := by
  have hn : 0 ≤ᵐ[ν] (fun z : ℝ × ℝ => (z.2-f z.1)^2) :=
    Eventually.of_forall (fun z => sq_nonneg _)
  by_cases hi : Integrable (fun z : ℝ × ℝ => (z.2-f z.1)^2) ν
  · have he : ENNReal.ofReal (predictionRisk ν f) = extendedPredictionRisk ν f :=
      ofReal_integral_eq_lintegral_ofReal hi hn
    have hR : R ≤ predictionRisk ν f+B := by linarith [hb f hf hi]
    calc
      _ ≤ ENNReal.ofReal (predictionRisk ν f+B) := ENNReal.ofReal_le_ofReal hR
      _ = _ := by
        have hp : 0 ≤ predictionRisk ν f := integral_nonneg (fun z => sq_nonneg _)
        rw [ENNReal.ofReal_add hp hB, he]
  · have htop : extendedPredictionRisk ν f = ∞ := by
      by_contra hfin
      apply hi
      exact (lintegral_ofReal_ne_top_iff_integrable
        ((measurable_snd.sub (hf.comp measurable_fst)).pow_const 2).aestronglyMeasurable hn).mp hfin
    simp [htop]

/-- The independent two-point noise gives an irreducible risk of one hundredth,
also against measurable predictors of infinite risk. -/
theorem witness_risk_lower (μ : Measure ℝ) (hp : ProbabilityLaw μ)
    (h : ℝ → ℝ) (hm : Measurable h) (f : ℝ → ℝ) (hf : Measurable f) :
    ENNReal.ofReal (1/100) ≤ extendedPredictionRisk (witnessLaw μ h) f := by
  let ν := witnessLaw μ h
  have hn : 0 ≤ᵐ[ν] (fun z : ℝ × ℝ => (z.2-f z.1)^2) :=
    Eventually.of_forall (fun _ => sq_nonneg _)
  by_cases hi : Integrable (fun z : ℝ × ℝ => (z.2-f z.1)^2) ν
  · have he : ENNReal.ofReal (predictionRisk ν f) = extendedPredictionRisk ν f :=
      ofReal_integral_eq_lintegral_ofReal hi hn
    rw [← he]
    exact ENNReal.ofReal_le_ofReal (GP023B1b_risk_lower μ hp hm hf hi)
  · have htop : extendedPredictionRisk ν f = ∞ := by
      by_contra hfin
      exact hi ((lintegral_ofReal_ne_top_iff_integrable
        ((measurable_snd.sub (hf.comp measurable_fst)).pow_const 2).aestronglyMeasurable hn).mp hfin)
    change ENNReal.ofReal (1/100) ≤ extendedPredictionRisk ν f
    simp [htop]

theorem uniform_projections : WholeUniformProjections := by
  intro J _
  have hpd : MomentPositiveDefinite uniformMargins J := uniform_full_rank J
  have h := GLP023B4c_T8_cpb_residual_moments uniformMargins uniformLaw.1 uniformLaw.2 J hpd
  exact ⟨hpd, h.1, h.2.1⟩

/-- The root counts and perturbation keep the donor's unrestricted polynomial
claims; only the comparisons of defined close-window means receive count guards. -/
theorem T3_assembly : T3WholeStatement := by
  refine ⟨printedBinEquivalence, coarsenedWeights, coarsenedLocalization,
    finitePolynomialWeights, ?_, conditionalMoments, uniformIllustration,
    uniform_projections, ?_⟩
  · intro ι _ _ J hJ k hk x d hdata hfull hboth
    obtain ⟨hn, hp, hpert⟩ := AronowAudit.P023.corrected_finite_nonlocality
      J hJ k hk x d hdata hfull hboth
    refine ⟨hn, hp, ?_⟩
    intro hmany
    obtain ⟨i, y, y', hout, hone, hag, hpoly, hrd, hc⟩ := hpert hmany
    exact ⟨i, y, y', hout, hone, hag, hpoly,
      fun hn1 hn0 => ⟨hrd, fun β β' hβ hβ' => hc β β' hβ hβ' hn1 hn0⟩⟩
  · intro Ω _ P A B β
    refine ⟨?_, AronowAudit.P023.shared_target_asymptotic_equivalence P A B β⟩
    intro N ε _
    simpa only [sub_self, sub_zero] using
      AronowAudit.P023.difference_probability_bound P (A N) (B N) β β ε

theorem sigmoid_family : WholeSigmoidFamily := by
  intro a η ha hη hη1
  let ν := witnessLaw uniformMargins (sigmoid a η)
  have hc : Continuous (sigmoid a η) := GP023B1b_continuous a η
  have hp : ProbabilityLaw ν := GP023B1b_witness_probability _ uniformLaw.1 hc.measurable
  let : IsProbabilityMeasure uniformMargins := ⟨uniformLaw.1⟩
  have hmargin : marginLaw ν = uniformMargins := GP023B1b_witness_margin _ hc.measurable
  have hsq : Integrable (fun z : ℝ × ℝ => z.2^2) ν := by
    have ht : Integrable (fun z : ℝ × ℝ =>
        (z.2-predict (polynomialDesign 1 (fun x : ℝ => x) party) (fun _ => 0) z.1)^2) ν :=
      GP023B1b_regression_risk_integrable a η ha.le 1 (fun _ => 0)
    simpa [predict] using ht
  have hmean : ConditionalMean ν (fun x => 1/2+sigmoid a η x) :=
    (sigmoidPopulation.1 a η ha hη hη1).2.2.2.2.1
  refine ⟨hp, hmargin, hsq, continuous_const.add hc, ?_, ?_, ?_, ?_⟩
  · simp [sigmoid]
  · intro J c
    exact GP023B1b_regression_risk_integrable a η ha.le J c
  · intro J _
    exact GLP023B4c_T8_cpb_fwl uniformMargins uniformLaw.1 uniformLaw.2 J
      (uniform_full_rank J) _ (GLP023B4c_T8_cpb_continuous (continuous_const.add hc))
  · intro Ω _ P sample hiid J hJ
    have hs : MarginSupport (marginLaw ν) := by rw [hmargin]; exact uniformLaw.2
    have hpd : ∀ K, 1 ≤ K → MomentPositiveDefinite (marginLaw ν) K := by
      intro K _; rw [hmargin]; exact uniform_full_rank K
    have ht := GLP023B4c_T8_fixed_limit P ν sample hiid hp hs hsq
      (fun x => 1/2+sigmoid a η x) hmean hpd J hJ
    change ConvergesInProbability P (fun N => samplePolynomial sample N J)
      (populationCoefficient (marginLaw ν) J (fun x => 1/2+sigmoid a η x)) at ht
    rwa [hmargin] at ht

theorem sigmoid_all_risks : WholeSigmoidAllRisks := by
  intro a η ha hη hη1 J hJ
  dsimp only
  intro f hf
  have hfit := (sigmoidFit a η ha ⟨hη, hη1⟩).2.2.2.1 J hJ
  exact ⟨witness_risk_lower uniformMargins uniformLaw.1 _
    (GP023B1b_continuous a η).measurable f hf,
    extend_risk_bound _ _ _ (by positivity) hfit.2.2.1 f hf⟩

theorem T4_assembly : T4WholeStatement := by
  refine ⟨sigmoidPopulation, sigmoidFit, ?_, sigmoid_family, uniformSymmetry,
    uniform_projections, uniformIllustration.2.2.1, uniformIllustration.2.2.2.1,
    sigmoid_all_risks, ?_, ?_, ?_⟩
  · exact @sigmoid_sample_separation_proof
  · intro J hJ
    have h := (sigmoidFit (1/20) (1/10000) (by norm_num) (by norm_num)).2.2.2.1 J hJ
    norm_num at h ⊢
    exact h.2.2.2
  · intro a
    simpa using ((((continuous_const : Continuous (fun _ : ℝ => a^2)).mul continuous_id).div_const (3 : ℝ)).tendsto 0).mono_left
      (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from nhdsWithin_le_nhds)
  · intro a J
    refine ⟨(fun j => if j.val = 0 then 1/2-a else if j.val = 1 then 2*a else 0), ?_⟩
    intro x
    simp [predict, polynomialDesign, Fin.sum_univ_succ]
    ring

theorem clustered_all_risks : WholeClusteredAllRisks := by
  intro d hd hd1
  dsimp only
  intro f hf
  let ν := witnessLaw (clusteredMargins d) (clusterSmooth d)
  obtain ⟨_, _, _, hconst, hb, hfit⟩ := clusteredFit d ⟨hd, hd1⟩
  have hi : Integrable (fun z : ℝ × ℝ => (z.2-(1/2:ℝ))^2) ν := by
    by_contra hn
    have hz : predictionRisk ν (fun _ => 1/2) = 0 := integral_undef hn
    have hnonneg : 0 ≤ expectation (clusteredMargins d) (fun x => clusterSmooth d x^2) :=
      integral_nonneg (fun _ => sq_nonneg _)
    change predictionRisk ν (fun _ => 1/2) = _ at hconst
    linarith
  have he : ENNReal.ofReal (predictionRisk ν (fun _ => 1/2)) =
      extendedPredictionRisk ν (fun _ => 1/2) :=
    ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _))
  obtain ⟨hp, _, _, _, _, _, hc, _⟩ := clusteredPopulation.1 d hd hd1
  refine ⟨witness_risk_lower _ hp _ hc.measurable f hf, ?_, ?_⟩
  · rw [← he]
    exact extend_risk_bound ν _ _ (sq_nonneg _) hb f hf
  · intro J hJ
    exact extend_risk_bound ν _ _ (sq_nonneg _) (hfit J hJ).2 f hf

theorem clustered_loss_integrable : WholeClusteredLossIntegrable := by
  intro d hd hd1 J c
  obtain ⟨hp, hs, _, _, _, _, hc, _, _, _, _, hb, _⟩ := clusteredPopulation.1 d hd hd1
  let : IsProbabilityMeasure (clusteredMargins d) := ⟨hp⟩
  let X := polynomialDesign J (fun x : ℝ => x) party
  have hpred : Measurable (predict X c) := GP023B1b_predict_measurable J c
  have hmeas : Measurable (fun z : ℝ × ℝ => (z.2-predict X c z.1)^2) :=
    (measurable_snd.sub (hpred.comp measurable_fst)).pow_const 2
  apply (GP023B1b_integrable_witness_iff (clusteredMargins d) hc.measurable hmeas).mpr
  have hbranch (u : ℝ) : Integrable
      (fun x => (1/2+clusterSmooth d x+u-predict X c x)^2) (clusteredMargins d) := by
    let C := |(1/2:ℝ)|+d/2+|u|+∑ j, |c j|
    apply GP023B1b_supported_integrable _ hp hs
      (((measurable_const.add hc.measurable).add measurable_const).sub hpred |>.pow_const 2)
      (C^2)
    intro x hx
    have he : |1/2+clusterSmooth d x+u-predict X c x| ≤ C := by
      calc
        _ ≤ |1/2+clusterSmooth d x+u|+|predict X c x| := abs_sub _ _
        _ ≤ (|(1/2:ℝ)|+|clusterSmooth d x|+|u|)+∑ j, |c j| :=
          add_le_add ((abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)) (GP023B1b_predict_bound J c x hx)
        _ ≤ C := by dsimp [C]; linarith [hb x]
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) he 2
  exact ⟨hbranch (-1/10), hbranch (1/10)⟩

theorem clustered_zero_approximation :
    ∀ d : ℝ, 0 < d → d ≤ 1/2 → ∀ J : ℕ,
      (0 : Polynomial ℝ).natDegree ≤ J ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        |clusterSmooth d x - (0 : Polynomial ℝ).eval x| ≤ d/2 := by
  intro d hd hd1 J
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hb, _⟩ := clusteredPopulation.1 d hd hd1
  exact ⟨by simp, fun x _ => by simpa using hb x⟩

theorem T5_assembly : T5WholeStatement := by
  refine ⟨clusteredPopulation, clusteredFit, clustered_all_risks,
    clustered_loss_integrable, clustered_zero_approximation, ?_, ?_, ?_⟩
  · intro d hd hd1
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩ :=
      clusteredPopulation.1 d hd hd1
    have hd4 : d^4 ≤ (1/2:ℝ)^4 := by gcongr
    have hbase : 0 < 1-d^4 := by norm_num at hd4; linarith
    have hden : 0 < (1-d^4)*(d/2)^2/6+d^4/12 := by positivity
    refine ⟨hden, ?_⟩
    rw [hb]
    have hden' : 0 < 1-d^4+2*d^2 := by positivity
    apply (div_eq_div_iff (ne_of_gt hden') (ne_of_gt hden)).mpr
    ring
  · intro J
    obtain ⟨hp, hb⟩ := clustered_zero_approximation (1/1000) (by norm_num) (by norm_num) J
    refine ⟨hp, ?_⟩
    convert hb using 1
    norm_num
  · simpa using ((continuous_id.div_const (2 : ℝ)).tendsto 0).mono_left
      (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from nhdsWithin_le_nhds)

theorem T8_assembly : T8WholeStatement := by
  intro Ω _ P ν sample α β h c δ L σ2 hr hiid k hkpos hk0 hnk
  have ht := corrected_proposition2_proof P ν sample α β h c δ L σ2 hr hiid k hkpos hk0 hnk
  refine ⟨?_, ht.2⟩
  intro J hJ
  have hpd : MomentPositiveDefinite (marginLaw ν) J := (ht.1 J hJ).1
  have hp : ProbabilityLaw (marginLaw ν) := GLP023B4c_marginal_probability ν hr.1
  have hs : MarginSupport (marginLaw ν) := hr.2.1
  have hproj := GLP023B4c_T8_cpb_residual_moments (marginLaw ν) hp hs J hpd
  exact ⟨hpd, (GLP023B4c_rayleigh _ hp hs J hpd).1,
    hproj.1, hproj.2.1, (ht.1 J hJ).2⟩

theorem T11_assembly : T11WholeStatement := by
  have hdata : TwoParty wholeEndpointMargins wholeEndpointParties := by
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals intro i; fin_cases i <;> norm_num [wholeEndpointMargins, wholeEndpointParties]
  have hnot : ¬ Condition1 (1/2) wholeEndpointMargins := by
    rintro ⟨⟨i, hi⟩, _⟩
    fin_cases i <;> norm_num [wholeEndpointMargins] at hi
  have hclose : close (1/2) wholeEndpointMargins = Finset.univ := by
    ext i; fin_cases i <;> norm_num [close, wholeEndpointMargins]
  refine ⟨propositionOne, ?_, hdata, hnot, hclose, ?_, ?_, ?_⟩
  · intro ι _ k hk x d y hdata hn1 hn0 c hc
    have hb : CoarsenedOLS k x d y (c ⟨1, by omega⟩) :=
      (printedBinEquivalence k hk x d y hdata _).mpr ⟨c, hc, rfl⟩
    exact (coarsenedWeights k hk x d y hdata hn1 hn0 _ hb).2.1
  · rw [hclose]; norm_num [wholeEndpointParties, Fin.sum_univ_succ]
  · rw [hclose]; norm_num [wholeEndpointParties, Fin.sum_univ_succ]
  · norm_num [rd, hclose, wholeEndpointParties, wholeEndpointOutcomes, Fin.sum_univ_succ]

end
end SAP.P023.WH.W1
