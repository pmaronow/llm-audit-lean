import SAP.P006a.WH.W1.Tools

set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
universe u v
namespace SAP.P006a.WH.W1
noncomputable section
/-- The mean of any integrable covariate mark among treated units is A/q. Prove by pulling m(X_i) out of the Bernoulli conditional expectation, integrating, and transporting through the covariate IdentDistrib. The indicator integral of T_i=true is its bit integral, hence q; q>0 licenses the event mean. Use the oracle adapter to call T2_treatment_stats without any estimator assumption. About 80 lines. -/
def T2_L1 : Prop :=
  ∀ {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n), OutcomeStanding E → ∀ π : C → ℝ, Admissible π →
    ∀ m : C → ℝ, Measurable m → Integrable m E.PX → ∀ i : Fin n,
    0 < E.q π →
    eventMean (E.law π) {ω | E.T π i ω = true} (fun ω => m (E.X i ω)) = E.A m π/E.q π
/-- Convert the already proved interval frontiers and attained threshold optimum into an explicit scalar maximum over q. Cover [0,1] by the prefix intervals; T2_prefix_cover in GP006B1 gives a proof pattern (it is private, so reproduce the short finite-order argument). At each q, the supplied frontier gives an attained fiber maximum and therefore its real supremum. Use nonnegativity of h_n on [0,1] to compare arbitrary policies to their fiber maxima. The supplied global threshold optimum attains the scalar maximum; use bestValue_eq on both optimizers. No compactness proof is needed here. Approximately 150-220 lines. -/
def T2_L2 : Prop :=
  ∀ {K : ℕ} (_hK : 0 < K) (n : ℕ), 0 < n → ∀ p m : Fin K → ℝ,
    (∀ i, 0 < p i) → (∑ i, p i) = 1 → Antitone m →
    (∀ j q, prefixMass p j ≤ q → q ≤ prefixMass p j+p j →
      thresholdRule p j q ∈ finitePolicies ∧
      finiteMass p (thresholdRule p j q) = q ∧
      finiteA p m (thresholdRule p j q) = prefixA p m j+m j*(q-prefixMass p j) ∧
      ∀ π ∈ finitePolicies, finiteMass p π = q →
        finiteA p m π ≤ prefixA p m j+m j*(q-prefixMass p j)) →
    (∃ j q, prefixMass p j ≤ q ∧ q ≤ prefixMass p j+p j ∧
      IsBest finitePolicies (fun π => emptyFactor n (finiteMass p π)*finiteA p m π)
        (thresholdRule p j q)) → ScalarFrontierFacts n p m
/-- Conditional Bernoulli treatment from an independent uniform seed, including policies attaining 0 and 1. Prove conditional-expectation uniqueness on sets fst^{-1}(B), using integral_prod and the uniform-cutoff integral. The probability law intervalLaw is volume restricted to [0,1]; P047's uniform01 uses (0,1], equal up to the null singleton {0}. Either transport uniform01_integral_ite or integrate the interval indicator directly. Boundedness supplies every integrability step. This is the only new stochastic calculation for the two-agent completion. Approximately 100-180 lines. -/
def T12_L1 : Prop :=
  ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∀ π : ℝ → ℝ, Admissible π →
    (ν.prod intervalLaw)[(fun ω : ℝ × ℝ => bit (decide (ω.2 ≤ π ω.1))) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[ν.prod intervalLaw]
      (fun ω => π ω.1)
lemma average_facts (h1 : T2_L1.{u,v}) {Ω : Type u} {C : Type v} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (hD : OutcomeStanding E) {π : C → ℝ}
    (hp : Admissible π) (m : C → ℝ) (hm : Measurable m) (hi : Integrable m E.PX)
    (r : Ω → ℝ) (hz : ∀ ω, ¬ 0 < treatedCount (fun i => E.T π i ω) → r ω = 0)
    (hmean : (∫ ω, r ω ∂E.law π) = E.averageObjective m π) :
    AveragePolicyFacts E m π r := by
  have : IsProbabilityMeasure E.PX := hD.px_probability
  have : IsProbabilityMeasure (Bridge.experiment E).PX := hD.px_probability
  have : IsProbabilityMeasure (E.law π) := hD.law_probability π hp
  have hS := Bridge.standing (oracle_standing E hD)
  have hbase := AronowAudit.P006.Wave1.T2_actual_averages
    (Bridge.experiment (oracleBaseline E)) hS hp (oracle_vector E hD π hp)
  have he : (E.law π {ω | treatedCount (fun i => E.T π i ω) = 0}).toReal =
      (1-E.q π)^n := hbase.1
  have hstats := AronowAudit.P006.Wave1.T2_treatment_stats
    (Bridge.experiment (oracleBaseline E)) hS hp
  have hq1 : E.q π ≤ 1 := hstats.2.1
  refine ⟨he, AronowAudit.P006.Wave1.T2_nonempty_mass (E.law π) (E.T π)
    (fun i => (hD.measurable_units π hp i).2.2.2) (E.q π) he, hmean,
    AronowAudit.P006.Wave1.T2_objective_formula (Bridge.experiment E) hp m, ?_⟩
  intro hq
  refine ⟨fun i => h1 E hD π hp m hm hi i hq, ?_⟩
  exact AronowAudit.P006.Wave1.T2_event_mean (E.law π) E.hn (E.T π)
    (fun i => (hD.measurable_units π hp i).2.2.2) (E.q π) (E.A m π) hq hq1 he r hz hmean
/-- Assembly of all corrected finite-sample average-reward clauses. -/
theorem T2_assembly (h1 : T2_L1.{u,v}) (h2 : T2_L2) : T2WholeStatement.{u,v} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Ω C _ _ n E hD
    have hato : ∀ π, Admissible π → AveragePolicyFacts E E.μ1 π (atoSample E π) := by
      intro π hp
      have h := AronowAudit.P006.Wave1.T2_actual_averages
        (Bridge.experiment (oracleBaseline E)) (Bridge.standing (oracle_standing E hD)) hp
        (oracle_vector E hD π hp)
      apply average_facts h1 E hD hp E.μ1 hD.means_measurable.2 hD.means_integrable.2
      · intro ω hz
        simp only [atoSample, wATO, ite_eq_right hz]
      · exact h.2.1
    refine ⟨hato, ?_, ?_, ?_, ?_⟩
    · intro π
      exact AronowAudit.P006.Wave1.T2_best_congr {π | Admissible π}
        E.expectedATO (E.averageObjective E.μ1) (fun p hp => (hato p hp).2.2.1) π
    · intro P hP hL hU
      have hatt : ∀ π ∈ P, AveragePolicyFacts E E.τ π (attSample E π) := by
        intro π hp
        apply average_facts h1 E hD (hP π hp) E.τ
          (hD.means_measurable.2.sub hD.means_measurable.1)
          (hD.means_integrable.2.sub hD.means_integrable.1)
        · intro ω hz
          simp only [attSample, wATT, wATO, ite_eq_right hz]
        · exact actual_average_local E hD P hL hU (hP π hp) hp
      exact ⟨hatt, fun π => AronowAudit.P006.Wave1.T2_best_congr P E.expectedATT
        (E.averageObjective E.τ) (fun p hp => (hatt p hp).2.2.1) π⟩
    · exact ⟨fun π hp i => (oracle_standing E hD).integrable_units π hp i |>.2.2,
        oracle_vector E hD⟩
    · exact fun P hP hL hU hI => independent_vector_local E hD P hP hL hU hI
  · intro K hK n hn p m hp hsum hm
    have h := AronowAudit.P006.Wave1.T2_finite_threshold_proof hK n hn p m hp hsum hm
    exact ⟨h.1, h.2.1, h2 hK n hn p m hp hsum hm h.1 h.2.1, h.2.2⟩
  · obtain ⟨_, _, _, _, hb, hu, _, _, _, _⟩ := AronowAudit.P006.T1_average_counterexample
    refine ⟨⟨by norm_num [binaryPolicies, binaryFeasible], hb⟩, hu, ?_, ?_⟩ <;>
      norm_num [binaryRule, effectE001]
  · intro n q hq
    apply (eq_div_iff (ne_of_gt hq)).2
    simpa only [emptyFactor, AronowAudit.P006.emptyFactor, mul_comm] using
      AronowAudit.P006.Wave1.T2_geometric n q
  · exact AronowAudit.P006.T2_one_unit_factor
theorem T3_assembly : T3WholeStatement := by
  constructor
  · intro Ω C _ _ n E hD P hP hz hL hU
    have hv (π : C → ℝ) (hp : π ∈ P) : E.V π = E.A E.τ π := by
      have h := AronowAudit.P006.Wave1.RepairT6T7_actual_welfare (Bridge.experiment E)
        (Bridge.policyDesign (outcome_policy E hD (hP π hp))) (hP π hp)
      simpa only [Experiment.meanWelfare, Experiment.A, mul_comm] using
        (show E.V π = E.meanWelfare π from h)
    have hf (π : C → ℝ) (hp : π ∈ P) :
        E.expectedATT π = emptyFactor n (E.q π)*E.V π ∧ 1 ≤ emptyFactor n (E.q π) := by
      have hstats := AronowAudit.P006.Wave1.T2_treatment_stats
        (Bridge.experiment (oracleBaseline E)) (Bridge.standing (oracle_standing E hD)) (hP π hp)
      exact ⟨(actual_average_local E hD P hL hU (hP π hp) hp).trans
        (congrArg (emptyFactor n (E.q π)*·) (hv π hp).symm),
        AronowAudit.P006.emptyFactor_ge_one n E.hn (E.q π) ⟨hstats.1, hstats.2.1⟩⟩
    have hvz : E.V (fun _ => 0) = 0 := by rw [hv _ hz]; simp [Experiment.A]
    have hrz : E.expectedATT (fun _ => 0) = 0 := by rw [(hf _ hz).1, hvz, mul_zero]
    have ht : Integrable E.τ E.PX := hD.means_integrable.2.sub hD.means_integrable.1
    have hbound : BddAbove (E.V '' P) := by
      refine ⟨∫ x, |E.τ x| ∂E.PX, ?_⟩
      rintro v ⟨π, hp, rfl⟩
      rw [hv π hp]
      have hi := AronowAudit.P006.Wave1.T7_policy_mul ht (hP π hp)
      change (∫ x, E.τ x * π x ∂E.PX) ≤ _
      rw [show (fun x => E.τ x * π x) = (fun x => π x * E.τ x) by funext x; ring]
      apply integral_mono hi ht.abs
      intro x
      calc
        π x*E.τ x ≤ |π x*E.τ x| := le_abs_self _
        _ = |π x| * |E.τ x| := abs_mul _ _
        _ ≤ 1 * |E.τ x| := mul_le_mul_of_nonneg_right
          (by rw [abs_of_nonneg ((hP π hp).2 x).1]; exact ((hP π hp).2 x).2) (abs_nonneg _)
        _ = |E.τ x| := one_mul _
    refine ⟨fun π hp => ⟨hv π hp, hf π hp⟩, hrz, hvz,
      ⟨⟨_, ⟨_, hz, rfl⟩⟩, hbound⟩, ?_⟩
    intro b hb
    have hr : 0 ≤ E.expectedATT b := hrz ▸ hb.2 _ hz
    have hp := (hf b hb.1).2
    have hbv : 0 ≤ E.V b := by
      by_contra hn
      have hneg := mul_neg_of_pos_of_neg (by linarith : 0 < emptyFactor n (E.q b))
        (lt_of_not_ge hn)
      rw [← (hf b hb.1).1] at hneg
      linarith
    refine ⟨hr, hbv, by dsimp [regret]; linarith, ?_⟩
    intro s hs
    have he : bestValue P E.V = E.V s := AronowAudit.P006.bestValue_eq hs
    exact ⟨he, by rw [regret, he]⟩
  · obtain ⟨_, _, _, _, hb, hu, _, hs, hg, _⟩ := AronowAudit.P006.T1_average_counterexample
    have hr : regret binaryPolicies (binaryWelfare (1/2) effectE001) (17/18,1) = 1/40 := by
      have he : bestValue binaryPolicies (binaryWelfare (1/2) effectE001) =
          binaryWelfare (1/2) effectE001 (1,1) := AronowAudit.P006.bestValue_eq hs
      rw [regret, he]
      exact hg
    have hpr : printedRegretE001 = 9/20 := by
      norm_num [printedRegretE001, Fintype.sum_bool, effectE001, Bool.forall_bool]
    have he : rewardE001ATT = rewardE001 := funext Bridge.averageWitness
    refine ⟨Bridge.averageWitness, ?_, ?_, hr, hpr, by rw [hr, hpr]; norm_num⟩
    · rw [he]
      exact ⟨by norm_num [binaryPolicies, binaryFeasible], hb⟩
    · rw [he]
      exact hu
/-- Extended positive-part monotonicity and its ordinary integrable specialization. -/
theorem T14_assembly : T14WholeStatement := by
  refine ⟨AronowAudit.P006.positivePart_eq_max, ?_, ?_⟩
  · intro C _ P0 τj τk h
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    have hpos (t : ℝ) : positivePart t = max t 0 := AronowAudit.P006.positivePart_eq_max t
    rw [hpos, hpos]
    exact max_le_max (h x) (le_refl (0 : ℝ))
  · intro C _ P0 τj τk h hj hk
    exact AronowAudit.P006.T14_corrected_rank_inequality P0 τj τk h hj hk
lemma uniform_oracle_standing (h1 : T12_L1) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) :
    Standing (uniformOracle ν) := by
  have : IsProbabilityMeasure ν := hν
  have : IsProbabilityMeasure intervalLaw :=
    isProbabilityMeasure_iff.mpr AronowAudit.P006.T12_density_direction_counterexample.1
  have : IsProbabilityMeasure (uniformOracle ν).PX := hν
  letI (π : ℝ → ℝ) : IsProbabilityMeasure ((uniformOracle ν).law π) :=
    (show IsProbabilityMeasure (ν.prod intervalLaw) from inferInstance)
  have hT (π : ℝ → ℝ) (hp : Admissible π) :
      Measurable (fun ω : ℝ × ℝ => decide (ω.2 ≤ π ω.1)) := by
    apply measurable_to_bool
    convert measurableSet_le measurable_snd (hp.1.comp measurable_fst) using 1
    ext ω
    simp
  have hG : MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ) inferInstance ≤
      (inferInstance : MeasurableSpace (ℝ × ℝ)) := measurable_fst.comap_le
  refine {
    px_probability := hν
    means_measurable := ⟨measurable_const, measurable_const⟩
    means_integrable := ⟨integrable_const 0, integrable_const 1⟩
    law_probability := fun _ _ => inferInstance
    measurable_units := fun π hp _ => ⟨measurable_fst, measurable_const, measurable_const, hT π hp⟩
    integrable_units := fun _ _ _ => ⟨integrable_const 0, integrable_const 1, integrable_const 0⟩
    covariate_law := ?_
    potential_law_fixed := ?_
    iid_independent := fun _ _ => iIndepFun.of_subsingleton
    iid_identical := ?_
    conditional_means := ?_
    bernoulli := fun π hp _ => h1 ν hν π hp
    ignorability := ?_ }
  · intro π hp i
    refine ⟨measurable_fst.aemeasurable, measurable_id.aemeasurable, ?_⟩
    change Measure.map Prod.fst (ν.prod intervalLaw) = Measure.map id ν
    simp only [Measure.map_fst_prod, measure_univ, one_smul, Measure.map_id]
  · intro π π' hp hp' i
    exact IdentDistrib.refl (measurable_fst.prodMk
      (measurable_const.prodMk measurable_const)).aemeasurable
  · intro π hp i j
    have he : i = j := Subsingleton.elim _ _
    subst j
    exact IdentDistrib.refl (measurable_fst.prodMk
      (measurable_const.prodMk (measurable_const.prodMk (hT π hp)))).aemeasurable
  · intro π hp i
    change (ν.prod intervalLaw)[(fun _ => (0 : ℝ)) | MeasurableSpace.comap Prod.fst inferInstance]
        =ᵐ[ν.prod intervalLaw] (fun _ => 0) ∧
      (ν.prod intervalLaw)[(fun _ => (1 : ℝ)) | MeasurableSpace.comap Prod.fst inferInstance]
        =ᵐ[ν.prod intervalLaw] (fun _ => 1)
    simp only [condExp_const hG, Filter.EventuallyEq.rfl, and_self]
  · intro π hp i B _hB
    change (ν.prod intervalLaw)[(fun ω : ℝ × ℝ => bit (decide (ω.2 ≤ π ω.1)) *
      B.indicator (fun _ => (1 : ℝ)) (0,1)) | MeasurableSpace.comap Prod.fst inferInstance]
      =ᵐ[ν.prod intervalLaw] (fun ω => π ω.1 *
        (ν.prod intervalLaw)[(fun _ => B.indicator (fun _ => (1 : ℝ)) (0,1)) |
          MeasurableSpace.comap Prod.fst inferInstance] ω)
    by_cases hb : ((0 : ℝ), (1 : ℝ)) ∈ B
    · simpa only [Set.indicator_of_mem hb, mul_one, condExp_const hG] using h1 ν hν π hp
    · simp only [Set.indicator_of_notMem hb, mul_zero, condExp_const hG, Filter.EventuallyEq.rfl]
/-- The measure obstruction together with both complete oracle agent experiments. -/
theorem T12_assembly (h1 : T12_L1) : T12WholeStatement := by
  have h := AronowAudit.P006.T12_density_direction_counterexample
  have hM : T12Statement := by
    refine ⟨h, ?_⟩
    intro s
    simp only [referenceWithAtom, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact le_add_of_nonneg_right zero_le
  have hν : IsProbabilityMeasure referenceWithAtom := isProbabilityMeasure_iff.mpr h.2.1
  have hLeb : IsProbabilityMeasure intervalLaw := isProbabilityMeasure_iff.mpr h.1
  have hvec (ν : Measure ℝ) : VectorUnbiased (uniformOracle ν) {π | Admissible π} := by
    intro π hp i
    change ((uniformOracle ν).law π)[(0 : (ℝ × ℝ) → ℝ) |
      (uniformOracle ν).vectorSigma π] =ᵐ[(uniformOracle ν).law π] (0 : (ℝ × ℝ) → ℝ)
    rw [condExp_zero]
  refine ⟨hM, uniform_oracle_standing h1 _ hν, uniform_oracle_standing h1 _ hLeb,
    rfl, rfl, Measure.AbsolutelyContinuous.rfl, h.2.2.2.2.1, ?_, hvec _, hvec _, ?_⟩
  · intro x
    constructor <;> norm_num [uniformOracle, Experiment.τ]
  · have : IsProbabilityMeasure referenceWithAtom := hν
    have : IsProbabilityMeasure intervalLaw := hLeb
    exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id
lemma info_integral (f : Bool × Bool → ℝ) :
    (∫ ω, f ω ∂infoLaw) = (f (true,true)+f (true,false)+f (false,true)+f (false,false))/4 := by
  have : IsProbabilityMeasure infoLaw := by unfold infoLaw; infer_instance
  rw [infoLaw, integral_prod f Integrable.of_finite]
  simp only [integral_bernoulliMeasure, smul_eq_mul]
  norm_num
  ring
/-- Exact bounded four-atom refutation of the included general single-unit Lemma 2. -/
theorem T8_assembly : T8WholeStatement := by
  have : IsProbabilityMeasure infoLaw := by unfold infoLaw; infer_instance
  have hfirst : (∫ ω, infoEstimator ω (infoCovariate 0 ω) ∂infoLaw) = 1 := by
    rw [info_integral]
    norm_num [infoEstimator, infoCovariate]
  have hsecond : (∫ ω, infoEstimator ω (infoCovariate 1 ω) ∂infoLaw) = 0 := by
    rw [info_integral]
    norm_num [infoEstimator, infoCovariate]
  have hactual : (∫ ω, wTT (infoEstimator ω) (fun i => infoCovariate i ω)
      (fun _ => true) (fun _ => 0) ∂infoLaw) = -1 := by
    rw [info_integral]
    norm_num [wTT, wWeightedTT, infoEstimator, infoCovariate, bit, Fin.sum_univ_two]
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfirst, hsecond, hactual, ?_⟩
  · exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  · refine ⟨measurable_fst.aemeasurable, measurable_snd.aemeasurable, ?_⟩
    simp only [infoLaw, Measure.map_fst_prod, Measure.map_snd_prod, measure_univ, one_smul]
  · exact ⟨measurable_const, fun _ => ⟨by norm_num, le_rfl⟩⟩
  · intro i
    have hG := (measurable_of_finite (infoCovariate i)).comap_le
    refine ⟨?_, ?_, condIndepFun_const_left true _, condIndepFun_const_left true _⟩
    · rw [condExp_const hG]
    · change infoLaw[(0 : (Bool × Bool) → ℝ) | _] =ᵐ[infoLaw] (0 : (Bool × Bool) → ℝ)
      rw [condExp_zero]
  · intro c
    refine ⟨Integrable.of_finite, ?_⟩
    rw [info_integral]
    rcases c with ⟨x, u⟩
    cases x <;> norm_num [infoEstimator]
  · intro ω c
    unfold infoEstimator
    split <;> norm_num
  · intro i
    exact ⟨Integrable.of_finite, by simp only [one_mul, Filter.EventuallyEq.rfl]⟩
  · intro i
    rw [hactual, integral_zero, info_integral]
    fin_cases i <;> norm_num [infoEstimator, infoCovariate]
end
end SAP.P006a.WH.W1
