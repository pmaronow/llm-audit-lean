import SAP.P011a.WH.W2.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W2

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-- T9: concentration of a bounded, deterministically shifted sparse quadratic form on
arbitrary rows. Replay `msr_quadratic_concentration` without its unused nesting premise.
Use `msr_normalized_expectation`, `msr_normalized_variance`, `msr_Q_memLp2` and
`OracleCompletion.rowCP_of_variance`; take d=ceil(c2)+1 and let n_k tend to infinity.
About 70 lines; no model-fitting or selection argument belongs in this leaf. -/
def T9_L1 : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), RowScaling F c1 c2 c3 c4 →
  ∀ (a : ∀ k, Fin (F.size k) → ℝ) (B : ℝ), 0 ≤ B →
  (∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |weighted (F.model k) y i-a k i| ≤ B) →
  InProbability F
    (fun k y => quadratic (oracleMatrix (F.model k).G) (weighted (F.model k) y-a k)/(F.size k : ℝ))
    (fun k => scaledTrue F k + quadratic (oracleMatrix (F.model k).G)
      (fun i => expectation (F.model k) (fun y => weighted (F.model k) y i)-a k i)/(F.size k : ℝ))

/-- T10: a single Borel representative works for every fixed mean pattern and the mixture.
The common support is the finite set {a+b,a-b,-a+b,-a-b}^n. Define the representative as
a finite sum of singleton indicators with the prescribed values of T, and zero elsewhere.
Push the support statement through each finite uniform source law. No positivity, injectivity
of the source map, or measurability of T is needed. Estimated 60–100 lines. -/
def T10_L1 : Prop :=
  ∀ (a b : ℝ) (n : ℕ) (T : (Fin n → ℝ) → ℝ),
  ∃ Tm : (Fin n → ℝ) → ℝ, Measurable Tm ∧
    (∀ s : ℕ → Bool, Tm =ᵐ[(fixedMeanModel a b s n).law] T) ∧
    Tm =ᵐ[(mixtureModel a b n).law] T

/-- T1: certify the decimal reading "about 0.805" by this rational interval.
Bridge `Phi` to P033's `normalCDF` using `cdf_eq_real`, and identify the two
quantiles by unfolding their infima and normalizing the threshold to 39/40. Use `pseudo_counter_quantile_bounds`,
`Real.sq_sqrt`, monotonicity and `pseudo_counter_cdf_certificate` (degree 32 suffices).
Every numerical comparison is rational arithmetic. Estimated 80–140 lines. -/
def T1_L1 : Prop :=
  8045/10000 < 2*Phi (normalQuantile (1/20)*Real.sqrt (7/16))-1 ∧
    2*Phi (normalQuantile (1/20)*Real.sqrt (7/16))-1 < 8055/10000

/-- T2: certify the printed decimal prefix by consecutive rational endpoints.
Use the same quantile bridge as T1. Bracket z_0.975*sqrt(19/29) between
1.586448186371 and 1.586448186372 using the quantile bounds and squared rational
comparisons. Apply P033's CDF certificates and strict monotonicity. Estimated 80–140 lines. -/
def T2_L1 : Prop :=
  8873623230/10000000000 < 2*Phi (normalQuantile (1/20)*Real.sqrt (19/29))-1 ∧
    2*Phi (normalQuantile (1/20)*Real.sqrt (19/29))-1 < 8873623231/10000000000

/-- T3(i): oracle concentration, with the mean quadratic retained and no observed nesting.
Replay `OracleCompletion.revised_oracle_convergence_completed` after deleting the unused
nesting component. Finite expectation/variance bounds concentrate Q/n; betaHat-beta tends
to zero and `sample_centering_bound` controls replacing beta by betaHat.
Only size growth, not monotonicity, enters. Estimated 100–140 lines. -/
def T3_L1 : Prop := OracleConvergenceWhole

/-- T3(iii): sample-variance concentration with both marginal variance and mean spread.
Replay `SampleCompletion.revised_sample_variance_completed` after deleting the unused
nesting component. Use `U_variance_bound`, `U_mean`, `U_memLp_two` and the exact sample
centering identity. The scaled-variance limit and n_k tending to infinity make the square
of betaHat-beta negligible. Estimated 60–100 lines. -/
def T3_L2 : Prop := SampleVarianceConvergenceWhole

private theorem misspec_of_shifted (hshifted : T9_L1) : ResidualMisspecificationWhole := by
  intro F c1 c2 c3 c4 h p D γstar γhat hmeas hz herr
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  let a : ∀ k, Fin (F.size k) → ℝ := fun k i => (F.model k).theta i*(D k *ᵥ γstar) i
  have hshift (k : ℕ) (y : Fin (F.size k) → ℝ) :
      weighted (F.model k) y-a k = trueResidual (F.model k) (D k) γstar y := by
    funext i
    dsimp [a, weighted, trueResidual]
    ring
  obtain ⟨B₀,hB₀⟩ := hz
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hzB (k : ℕ) : ∀ᵐ y ∂(F.model k).law,
      ∀ i, |trueResidual (F.model k) (D k) γstar y i| ≤ B :=
    (hB₀ k).mono fun y hy i => (hy i).trans (le_max_left _ _)
  have hb (k : ℕ) : ∀ᵐ y ∂(F.model k).law,
      ∀ i, |weighted (F.model k) y i-a k i| ≤ B := by
    filter_upwards [hzB k] with y hy
    have he := congrFun (hshift k y)
    intro i
    change |(weighted (F.model k) y-a k) i| ≤ B
    rw [he i]
    exact hy i
  have hQ := hshifted F c1 c2 c3 c4 h a B hB hb
  let b : ℕ → ℝ := fun k => quadratic (oracleMatrix (F.model k).G)
    (fun i => expectation (F.model k) (fun y => weighted (F.model k) y i)-a k i)/(F.size k : ℝ)
  have hQ' : ∀ ε > (0 : ℝ), Tendsto (fun k => (F.model k).law.real
      {y | |quadratic (oracleMatrix (F.model k).G)
        (trueResidual (F.model k) (D k) γstar y)/(F.size k : ℝ) -
          (scaledTrue F k+b k)| > ε}) atTop (𝓝 0) := by
    simpa only [InProbability, probability, hshift, b] using hQ
  have hE := AronowAudit.P011.Wave1.msr_prediction_transfer (Bridge.family F)
    c2 h.2.1.le h.2.2.2.2.2.2.1
    (fun k y => fittedResidual (F.model k) (D k) (γhat k) y)
    (fun k y => trueResidual (F.model k) (D k) γstar y) B hB hzB herr
  have hfit := AronowAudit.P011.OracleCompletion.row_moving_add_error
    (fun k => (F.model k).law)
    (fun k y => quadratic (oracleMatrix (F.model k).G)
      (trueResidual (F.model k) (D k) γstar y)/(F.size k : ℝ))
    (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
      (fittedResidual (F.model k) (D k) (γhat k) y))
    (fun k => scaledTrue F k+b k) hQ' hE
  intro ε hε
  have hh := hfit ε hε
  change Tendsto (fun k => probability (F.model k) {y |
    |((F.size k : ℝ)*VResidual (F.model k).G
      (fittedResidual (F.model k) (D k) (γhat k) y)-scaledTrue F k)-b k| > ε}) atTop (𝓝 0)
  have he (k : ℕ) (y : Fin (F.size k) → ℝ) :
      ((F.size k : ℝ)*VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (γhat k) y)-scaledTrue F k)-b k =
      (F.size k : ℝ)*VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (γhat k) y)-(scaledTrue F k+b k) := by ring
  simpa only [probability, he] using hh

theorem T9_assembly (h1 : T9_L1) : T9WholeStatement := by
  have hmiss := misspec_of_shifted h1
  have hpred := residual_prediction_of_misspec hmiss
  exact ⟨residual_root_of_prediction hpred, hpred, hmiss, Bridge.ResidualFailure_proved,
    Bridge.ResidualPerturbation_proved, residual_failure_finite⟩

private theorem positive_probability (F : Family)
    (X : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (c : ℝ) (hc : 0 < c)
    (hX : ∀ k, Measurable (X k)) (hlim : InProbability F X (fun _ => c)) :
    Tendsto (fun k => probability (F.model k) {y | 0 < X k y}) atTop (𝓝 1) := by
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  have hb : Tendsto (fun k => probability (F.model k) {y | X k y ≤ 0}) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun k => ?_) (hlim (c/2) (by linarith))
    apply measureReal_mono (μ := (F.model k).law) ?_ (measure_ne_top _ _)
    intro y hy
    change c/2 < |X k y-c|
    have hle := neg_le_abs (X k y-c)
    change X k y ≤ 0 at hy
    linarith
  have he (k : ℕ) : probability (F.model k) {y | 0 < X k y} =
      1-probability (F.model k) {y | X k y ≤ 0} := by
    have hs : MeasurableSet {y | X k y ≤ 0} := measurableSet_le (hX k) measurable_const
    have hh := measureReal_compl (μ := (F.model k).law) hs
    have hset : {y | 0 < X k y} = {y | X k y ≤ 0}ᶜ := by ext y; simp
    simpa only [probability,hset,probReal_univ] using hh
  simp_rw [he]
  simpa using tendsto_const_nhds.sub hb

theorem T1_assembly (h1 : T1_L1) : T1WholeStatement := by
  refine ⟨⟨Bridge.CycleCounterexample_proved, AronowAudit.P011.cycle_covariance_algebra,
    AronowAudit.P011.cycle_negative_realization.2.1⟩, h1, ?_, ?_⟩
  · intro a k i
    have hh : covariance ((cycleFamily a).model k) i i =
        ((2 : ℝ) • (1 : Matrix (Fin ((cycleFamily a).size k))
          (Fin ((cycleFamily a).size k)) ℝ) + adjacency ((cycleFamily a).model k).G) i i :=
      AronowAudit.P011.Wave1.cycleCE_covariance a (k+1) i i
    simpa [Matrix.one_apply,adjacency,((cycleFamily a).model k).G.property.2] using hh
  · have hlim := positive_probability (cycleFamily (3/2)) (scaledOracle (cycleFamily (3/2)))
      (7/4) (by norm_num) (fun k => by
        unfold scaledOracle V1 quadratic centered average weighted adjacency
        fun_prop) Bridge.CycleCounterexample_proved.2.2.2.2.1
    have he (k : ℕ) (y : Fin ((cycleFamily (3/2)).size k) → ℝ) :
        0 < scaledOracle (cycleFamily (3/2)) k y ↔
        0 < V1 ((cycleFamily (3/2)).model k).G (weighted ((cycleFamily (3/2)).model k) y) := by
      unfold scaledOracle
      exact mul_pos_iff_of_pos_left (by exact_mod_cast (cycleFamily (3/2)).positive k)
    simpa only [he] using hlim

theorem T2_assembly (h1 : T2_L1) : T2WholeStatement := by
  exact ⟨⟨Bridge.PathCounterexample_proved, Bridge.PathMoments_proved, Bridge.PathOLS_proved⟩,
    path_finite_whole, h1⟩

theorem T3_assembly (h1 : T3_L1) (h2 : T3_L2) : T3WholeStatement := by
  refine ⟨h1, whole_expectation, h2, whole_mean_conditions h1,
    Bridge.CliqueCharacterization_proved, ?_⟩
  intro F c1 c2 c3 c4 h k
  let : IsProbabilityMeasure (Bridge.model (F.model k)).law := (F.model k).probability
  refine ⟨?_, whole_bias F c1 c2 c3 c4 h k⟩
  exact AronowAudit.P011.delta_sum_zero (F.positive k) (Bridge.model (F.model k))
    (fun i => (AronowAudit.P011.ProbabilityCompletion.weighted_memLp
      (Bridge.model (F.model k)) c1 (h.2.2.2.2.2.1 k) i).integrable (by norm_num))

private theorem inProbability_congr_ae (F : Family)
    (T U : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (a : ℕ → ℝ)
    (he : ∀ k, T k =ᵐ[(F.model k).law] U k) :
    InProbability F T a ↔ InProbability F U a := by
  have hp (k : ℕ) (ε : ℝ) : probability (F.model k) {y | |T k y-a k| > ε} =
      probability (F.model k) {y | |U k y-a k| > ε} := by
    apply measureReal_congr
    filter_upwards [he k] with y hy
    simp only [hy]
  simp only [InProbability, hp]

private theorem arbitrary_impossibility (hrep : T10_L1) : ArbitraryStatisticImpossibility := by
  intro a b ha hb
  have h := Bridge.UniversalImpossibility_proved a b ha hb
  have hc := h.2.2.2.1
  have htail := h.2.2.2.2
  have rep (T : ∀ k, (Fin (k+1) → ℝ) → ℝ) :
      ∃ U : ∀ k, (Fin (k+1) → ℝ) → ℝ,
        (∀ k, Measurable (U k)) ∧
        (∀ s k, U k =ᵐ[(fixedMeanModel a b s (k+1)).law] T k) ∧
        (∀ k, U k =ᵐ[(mixtureModel a b (k+1)).law] T k) := by
    choose U hU using fun k => hrep a b (k+1) (T k)
    exact ⟨U, fun k => (hU k).1, fun s k => (hU k).2.1 s, fun k => (hU k).2.2⟩
  constructor
  · rintro ⟨T,hfixed,hmix⟩
    obtain ⟨U,hU,hUf,hUm⟩ := rep T
    apply hc
    refine ⟨U,hU,?_,?_⟩
    · intro s
      exact (inProbability_congr_ae (fixedMeanFamily a b s) U T _ (hUf s)).mpr (hfixed s)
    · exact (inProbability_congr_ae (mixtureFamily a b) U T _ hUm).mpr hmix
  · intro T ht hall
    obtain ⟨U,hU,hUf,hUm⟩ := rep T
    apply htail U hU
    · intro ε hε
      have hp (k : ℕ) : probability (mixtureModel a b (k+1)) {y | a^2+b^2-U k y > ε} =
          probability (mixtureModel a b (k+1)) {y | a^2+b^2-T k y > ε} := by
        apply measureReal_congr
        filter_upwards [hUm k] with y hy
        simp only [hy]
      simpa only [hp] using ht ε hε
    · intro s
      exact (inProbability_congr_ae (fixedMeanFamily a b s) U T _ (hUf s)).mpr (hall s)

private theorem no_universal_rule (himpossible : ArbitraryStatisticImpossibility) :
    ¬ ∃ V : ObservedVarianceRule, UniversalRuleConsistency V := by
  rintro ⟨V,hV⟩
  have hcontra (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : False := by
    let T : ∀ k, (Fin (k+1) → ℝ) → ℝ := fun k y =>
      ((k+1 : ℕ) : ℝ)*V (k+1) y (fun _ => 0) (fun _ => 1) (emptyGraph (k+1))
    apply (himpossible a b ha hb).1
    refine ⟨T, ?_, ?_⟩
    · intro s
      have hsc := rowScaling_of_scaling ((Bridge.UniversalImpossibility_proved a b ha hb).1 s)
      have hlim := hV (fixedMeanFamily a b s) (2*a+b) 1 (b^2) 2 hsc
      change InProbability (fixedMeanFamily a b s) T
        (scaledTrue (fixedMeanFamily a b s)) at hlim
      have hm : scaledTrue (fixedMeanFamily a b s) = fun _ => b^2 := by
        funext k
        exact (Bridge.MixtureMoments_proved a b s (k+1) (by omega)).2.2.1
      rw [hm] at hlim
      exact hlim
    · have hsc := rowScaling_of_scaling (Bridge.UniversalImpossibility_proved a b ha hb).2.1
      have hlim := hV (mixtureFamily a b) (a+b) 1 (a^2+b^2) 2 hsc
      change InProbability (mixtureFamily a b) T
        (scaledTrue (mixtureFamily a b)) at hlim
      have hm : scaledTrue (mixtureFamily a b) = fun _ => a^2+b^2 := by
        funext k
        exact (Bridge.MixtureMoments_proved a b (fun _ => true) (k+1) (by omega)).2.2.2.2.2
      rw [hm] at hlim
      exact hlim
  exact hcontra 1 1 (by norm_num) (by norm_num)

private theorem zero_unscaled :
    ∀ (F : Family) (c1 c2 c3 c4 : ℝ), RowScaling F c1 c2 c3 c4 →
      InProbability F (fun _ _ => 0) (fun k => var (F.model k) (betaHat (F.model k))) := by
  intro F c1 c2 c3 c4 h
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  have hn : Tendsto (fun k => (F.size k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.grows
  have hv := h.2.2.2.2.2.2.2.1.div_atTop hn
  have he (k : ℕ) : scaledTrue F k/(F.size k : ℝ) =
      var (F.model k) (betaHat (F.model k)) := by
    unfold scaledTrue
    exact mul_div_cancel_left₀ _ (by exact_mod_cast (F.positive k).ne')
  have hv' : Tendsto (fun k => var (F.model k) (betaHat (F.model k))) atTop (𝓝 0) := by
    simpa only [he] using hv
  have hz := AronowAudit.P011.CoverageCompletion.rowCP_det (fun k => (F.model k).law)
    (fun k => -var (F.model k) (betaHat (F.model k))) 0 (by simpa only [neg_zero] using hv'.neg)
  intro ε hε
  simpa only [AronowAudit.P011.CoverageCompletion.RowCP, probability, zero_sub, sub_zero]
    using hz ε hε

private theorem unbiased_design :
    ∀ n : ℕ, 0 < n →
    let m := fixedMeanModel 1 1 (fun _ => true) n
    m.law = uniformLaw (fun u : Fin n → Bool => fun i =>
      2*(if u i then (1 : ℝ) else 0)) ∧
    var m (betaHat m) = 1/(n : ℝ) ∧
    expectation m (fun y => betaHat m y/(n : ℝ)) = var m (betaHat m) := by
  intro n hn
  let m := fixedMeanModel 1 1 (fun _ => true) n
  have h := Bridge.MixtureMoments_proved 1 1 (fun _ => true) n hn
  have hvar : (n : ℝ)*var m (betaHat m) = 1 := by simpa using h.2.2.1
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hb : beta m = 1 := by simpa [average, sign, hn0] using h.2.1
  refine ⟨?_, (eq_div_iff hn0).mpr (by simpa [mul_comm] using hvar), ?_⟩
  · change uniformLaw _ = uniformLaw _
    congr 1
    funext u i
    cases u i <;> norm_num [sign]
  · change (∫ y, betaHat m y/(n : ℝ) ∂m.law) = _
    rw [integral_div]
    change beta m/(n : ℝ) = _
    rw [hb]
    exact ((eq_div_iff hn0).mpr (by simpa [mul_comm] using hvar)).symm

theorem T10_assembly (h1 : T10_L1) : T10WholeStatement := by
  have h := arbitrary_impossibility h1
  exact ⟨Bridge.UniversalImpossibility_proved, Bridge.MixtureMoments_proved, h,
    no_universal_rule h, zero_unscaled, unbiased_design⟩

end
end SAP.P011a.WH.W2
