import SAP.P020.Defs.WholeW1
import SAP.P020.Bridge
import AronowAudit.P020.P020_Design
import AronowAudit.P020.P020_Logistic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
namespace SAP.P020.WH.W1
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory SAP.P020 Bridge
noncomputable section
/-- The complete missing expectation chain (29), also specialized to control for (30). Prove observed/potential equality on the supported arm, expand the adjusted sum, use the supported arm cardinality to pull the common fitted coefficient out of sums, then finite expectation linearity. Finish with expected_arm_sum, expected_arm_mean_size and designCovariance_product. About 100-150 lines; no independence of the fitted coefficient is available or needed. -/
def T5_L1 : Prop := ∀ (P : ClusterPopulation) (khat : Finset (Fin P.M) → ℝ) (a : Bool),
    W1RajExpectationChain P khat a
/-- Differentiate the two arm quadratics and Appendix C's expanded common objective. Use differenced_variance, differenced_covariance and covariance symmetry to identify the actual functions, then HasDerivAt for constants, identity, squares, sums and products. Obtain the first-derivative function by funext and HasDerivAt.deriv before differentiating it again. No size-variance guard is needed. About 80-150 lines. -/
def T14_L1 : Prop := ∀ P : ClusterPopulation, W1VarianceDerivatives P
/-- Under the sole meaningful-ratio guard, prove every first-order equation, stationary-point characterization, reciprocal-weight coefficient formula and unique minimum of the common moment objective. Expand optimalCoefficient and armOptimalCoefficient, use mc+mt=M with positive arm counts, and field_simp/ring for the first-order chain. The derivative formulas follow directly by polynomial differentiation as in L1. For the unique minimum, multiply optimal_raj_variance by the positive scaling v and use raj_design_variance_moment. About 150-250 lines. -/
def T14_L2 : Prop := ∀ P : ClusterPopulation, W1SizeVariance P ≠ 0 → W1OptimalAlgebra P
/-- Prove each consecutive equivalence in Appendix C's efficiency calculation. Derive positive size variance from clusterVariance_nonneg and the nonzero guard. Use optimal_raj_variance or raj_design_variance_gap for the first equivalence, positive division for the second, unfold the arm coefficients for the third, and mc+mt=M with field_simp for the reciprocal-weight normalization. Finish with coefficient_improvement_intervals. No sign hypothesis on k or its optimum. About 100-180 lines. -/
def T14_L3 : Prop := ∀ P : ClusterPopulation, W1SizeVariance P ≠ 0 → W1EfficiencyChain P
/-- The copied population really has hM clusters, hmt treated clusters, hmc control clusters and hN individuals, and the same ATE. On Fin h × Fin M expand filtered product sums with Finset.sum_product and assignment_arm_counts; cancel positive h for the ATE. The product-set pooled estimator equals copiedDifferenceInMeans, and both its denominators are positive by arm_size_pos and nonempty Fin h. This is finite bookkeeping, about 120-220 lines. -/
def T17_L1 : Prop := ∀ (P : ClusterPopulation) (h : ℕ), 0 < h →
    ∀ s : CopyAssignments P h, W1CopyPopulationFacts P h s
/-- A full uniform finite law, in the existing finite-sum representation. -/
def fullLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω := uniformLaw Finset.univ ⟨Classical.choice inferInstance, Finset.mem_univ _⟩
/-- Bridge real event probabilities under the uniform measure to the project's finite error probability, for every statistic and threshold (including empty and full events). Use uniformOn_univ, count_apply_finset on the filtered univ, and cardinality-as-sum. Fintype.card_pos supplies a finite nonzero denominator; all subsets are measurable because the space is finite and has measurable singletons. About 40-80 lines. -/
def T17_L2 : Prop := ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (T : Ω → ℝ) (d ε : ℝ),
    (uniformOn Set.univ : Measure Ω).real {ω | ε < |T ω - d|} = errorProbability (fullLaw Ω) T d ε
/-- Construct the iid uniform path law and identify every finite prefix law. The path space and its measure are already defined, with discrete coordinates. Use iIndepFun_infinitePi and infinitePi_map_eval. For prefixes use Measure.infinitePi_map_restrict with the range/Fin equivalence, or the exact AsymptoticStatistics.pi_const_eq_infinitePi_map donor from AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw, then uniformOn_pi. Includes the empty prefix; it is a one-point probability space. About 60-120 lines. -/
def T17_L3 : Prop := ∀ P : ClusterPopulation, W1CopyMarginals P
/-- All three introductory strict-growth conditions in both constructions. For copies, sum_range_succ (or Fin.sum_univ_succ) makes the increment an arm count of the new valid assignment; arm_size_pos makes it positive. Total size increases by populationSize_pos. For within-cluster replication, replicated_size and replicated_arm_size give multiplication by r+1 of a positive constant. Apply strictMono_nat_of_lt_succ. These are pathwise statements, so they hold under the product law and under the one-draw coupling. About 60-100 lines. -/
def T17_L4 : Prop := ∀ P : ClusterPopulation, W1ReplicationGrowth P
/-- The analytic refutation, the scalar illustration and the design obstruction are already donor mathematics or short finite-sum arguments. -/
theorem T3_assembly : T3WholeStatement := by
  have hsize (P : ClusterPopulation) : P.M ≤ populationSize P := by
    calc
      P.M = ∑ _j : Fin P.M, 1 := by simp
      _ ≤ populationSize P := Finset.sum_le_sum (fun j _ => P.n_pos j)
  have htwo (P : ClusterPopulation) : 2 ≤ populationSize P := by
    have := hsize P
    have := P.mt_pos
    have := P.mt_lt
    omega
  refine ⟨?_, AronowAudit.P020.logistic_concrete_counterexample,
    fun P => ⟨hsize P, htwo P⟩, ?_⟩
  · exact ⟨AronowAudit.P020.logistic_strictMono,
      AronowAudit.P020.printed_contrast_bound, AronowAudit.P020.printed_model_unit_negative,
      AronowAudit.P020.printed_model_average_negative,
      AronowAudit.P020.printed_model_average_ne_reported⟩
  · rintro ⟨P, hP⟩
    have := htwo P
    omega
/-- The leaf supplies the missing intermediate calculation; existing results supply both final total expectations, corrected ATE expectation and bias. -/
theorem T5_assembly (h1 : T5_L1) : T5WholeStatement := by
  refine ⟨⟨?_, ?_⟩, h1⟩
  · intro P khat
    exact AronowAudit.P020.estimated_coefficient_bias (toPopulation P) khat
  · intro P khat
    have h : expectation (clusterLaw P) (fun s => desRaj P (khat s) s) = averageTreatmentEffect P + (P.M : ℝ) / populationSize P * (designCovariance (clusterLaw P) khat (armMeanSize P false) - designCovariance (clusterLaw P) khat (armMeanSize P true)) :=
      (AronowAudit.P020.estimated_coefficient_bias (toPopulation P) khat).2.2
    unfold designBias
    rw [h]
    ring
/-- No new lemma is needed: fixed-label expectations are expectations of constants, and the six unbiasedness identities are existing donor theorems. -/
theorem T13_assembly : T13WholeStatement := by
  have hc (P : ClusterPopulation) (c : ℝ) :
      expectation (clusterLaw P) (fun _ => c) = c :=
    AronowAudit.P020.expectation_const (toLaw (clusterLaw P)) c
  have hn : populationSize subscriptPopulation = 3 := by
    norm_num [populationSize, subscriptPopulation, Fin.sum_univ_succ]
  have hex : expectation (clusterLaw subscriptPopulation)
      (fun _ => (1 : ℝ) * ((subscriptPopulation.n 0 : ℝ) -
        (populationSize subscriptPopulation : ℝ) / subscriptPopulation.M)) = -(1 : ℝ)/2 := by
    rw [hc, hn]
    norm_num [subscriptPopulation]
  refine ⟨⟨?_, ?_⟩, ?_, ⟨hn, hex⟩, ?_, ?_⟩
  · intro P k
    exact AronowAudit.P020.des_raj_unbiased (toPopulation P) k
  · intro P A X ks ka
    exact AronowAudit.P020.des_raj_covariates_unbiased (toPopulation P) X ks ka
  · intro P k j
    simp only [hc, mul_eq_zero, sub_eq_zero]
    exact ⟨True.intro, True.intro, True.intro⟩
  · intro h
    have hz := h subscriptPopulation 1 0
    linarith
  · intro P k a
    have he : expectation (clusterLaw P)
        (fun s => k * (armMeanSize P a s - (populationSize P : ℝ)/P.M)) =
        k * expectation (clusterLaw P) (fun s => armMeanSize P a s - (populationSize P : ℝ)/P.M) :=
      AronowAudit.P020.expectation_const_mul (toLaw (clusterLaw P)) _ k
    refine ⟨he, ?_⟩
    rw [he]
    have hs : expectation (clusterLaw P) (fun s => armMeanSize P a s - (populationSize P : ℝ)/P.M) = 0 := by
      change AronowAudit.P020.expectation (toLaw (clusterLaw P)) _ = 0
      rw [AronowAudit.P020.expectation_sub, AronowAudit.P020.expectation_const]
      have hm : expectation (clusterLaw P) (armMeanSize P a) = (populationSize P : ℝ)/P.M :=
        AronowAudit.P020.expected_arm_mean_size (toPopulation P) a
      exact sub_eq_zero.mpr hm
    rw [hs, mul_zero]
/-- Mean and variance expansions need only the existing finite-moment donors. -/
theorem arm_expansion (P : ClusterPopulation) (a : Bool) : W1ArmExpansion P a := by
  intro k
  have hM : 0 < P.M := lt_trans P.mt_pos P.mt_lt
  have hm : clusterMean (rajPotential P a k) = clusterMean (if a then P.y1 else P.y0) :=
    AronowAudit.P020.differenced_mean hM _ _ k
  have hs : clusterMean (fun j => (P.n j : ℝ)) = (populationSize P : ℝ)/P.M :=
    AronowAudit.P020.mean_size (toPopulation P)
  have hv : W1ArmVariance P a k = clusterVariance (if a then P.y1 else P.y0) +
      k^2*W1SizeVariance P - 2*k*clusterCovariance (if a then P.y1 else P.y0) (W1Sizes P) :=
    AronowAudit.P020.differenced_variance hM _ _ k
  have hcov : clusterCovariance (if a then P.y1 else P.y0) (W1Sizes P) = W1SizeCovariance P a :=
    AronowAudit.P020.clusterCovariance_comm _ _
  refine ⟨hm, ?_, by rwa [hcov] at hv⟩
  dsimp only [W1ArmVariance, clusterVariance]
  rw [hm]
  simp only [rajPotential, differenced, hs]
  rfl
/-- The substituted quadratic is unconditional; all scaling denominators are positive from the standing design assumptions. -/
theorem objective_expansion (P : ClusterPopulation) : W1ObjectiveExpansion P := by
  intro k
  have hM : (P.M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans P.mt_pos P.mt_lt))
  have hN : (populationSize P : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (AronowAudit.P020.populationSize_pos (toPopulation P)))
  have hM1 : (P.M : ℝ) - 1 ≠ 0 := by
    have h : 1 < P.M := lt_of_le_of_lt (Nat.succ_le_of_lt P.mt_pos) P.mt_lt
    have h' : (1 : ℝ) < P.M := by exact_mod_cast h
    linarith
  constructor
  · have hv : designVariance (clusterLaw P) (desRaj P k) =
        (P.M : ℝ)^2 / ((populationSize P : ℝ)^2 * ((P.M : ℝ)-1)) * rajMomentObjective P k :=
      AronowAudit.P020.raj_design_variance_moment (toPopulation P) k
    rw [hv]
    unfold W1v
    field_simp
  · have hcov : clusterCovariance (rajPotential P false k) (rajPotential P true k) =
        clusterCovariance P.y0 P.y1 - k*W1SizeCovariance P false - k*W1SizeCovariance P true +
          k^2*W1SizeVariance P := by
      have hd : clusterCovariance (rajPotential P false k) (rajPotential P true k) =
          clusterCovariance P.y0 P.y1 - k*clusterCovariance P.y0 (W1Sizes P) -
            k*clusterCovariance P.y1 (W1Sizes P) + k^2*W1SizeVariance P :=
        (AronowAudit.P020.differenced_covariance (lt_trans P.mt_pos P.mt_lt) _ _ _ k).2
      have hc0 : clusterCovariance P.y0 (W1Sizes P) = W1SizeCovariance P false :=
        AronowAudit.P020.clusterCovariance_comm _ _
      have hc1 : clusterCovariance P.y1 (W1Sizes P) = W1SizeCovariance P true :=
        AronowAudit.P020.clusterCovariance_comm _ _
      rwa [hc0, hc1] at hd
    change W1c P * W1ArmVariance P false k + W1t P * W1ArmVariance P true k +
      2 * clusterCovariance (rajPotential P false k) (rajPotential P true k) = _
    rw [(arm_expansion P false k).2.2, (arm_expansion P true k).2.2, hcov]
    rfl
theorem retained_T14 : T14Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, AronowAudit.P020.coefficient_improvement_intervals⟩
  · intro P a hsize k
    exact AronowAudit.P020.arm_variance_completed_square (toPopulation P) a hsize k
  · intro P hsize a k
    exact AronowAudit.P020.arm_coefficient_optimal (toPopulation P) hsize a k
  · intro P k
    exact AronowAudit.P020.raj_design_variance_moment (toPopulation P) k
  · intro P k hsize
    exact AronowAudit.P020.raj_design_variance_completed_square (toPopulation P) k hsize
  · intro P k hsize
    exact AronowAudit.P020.raj_design_variance_gap (toPopulation P) k hsize
  · intro P hsize k
    exact AronowAudit.P020.optimal_raj_variance (toPopulation P) hsize k
theorem retained_T17 : T17Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, AronowAudit.P020.efficiency_inconsistent,
    AronowAudit.P020.efficiency_sample_size_grows, ?_,
    fun h => AronowAudit.P020.efficiency_inconsistent
      ((withinReplication_consistency_iff efficiencyPopulation).mp h), ?_⟩
  · intro P
    have h : DesignConsistent (copyLaw P) (copyAverage P true P.y1)
        (fun _ => (P.mt : ℝ) / P.M * ∑ j, P.y1 j) ∧
        DesignConsistent (copyLaw P) (copyAverage P false P.y0)
          (fun _ => (controlCount P : ℝ) / P.M * ∑ j, P.y0 j) ∧
        DesignConsistent (copyLaw P) (copyAverage P true (fun j => (P.n j : ℝ)))
          (fun _ => (P.mt : ℝ) / P.M * populationSize P) ∧
        DesignConsistent (copyLaw P) (copyAverage P false (fun j => (P.n j : ℝ)))
          (fun _ => (controlCount P : ℝ) / P.M * populationSize P) ∧
        DesignConsistent (copyLaw P) (copiedDifferenceInMeans P) (fun _ => averageTreatmentEffect P) :=
      AronowAudit.P020.growing_clusters_consistent (toPopulation P)
    exact ⟨consistent_succ (copyLaw P) (copyAverage P true P.y1)
        (fun _ => (P.mt : ℝ) / P.M * ∑ j, P.y1 j) h.1,
      consistent_succ (copyLaw P) (copyAverage P false P.y0)
        (fun _ => (controlCount P : ℝ) / P.M * ∑ j, P.y0 j) h.2.1,
      consistent_succ (copyLaw P) (copyAverage P true (fun j => (P.n j : ℝ)))
        (fun _ => (P.mt : ℝ) / P.M * populationSize P) h.2.2.1,
      consistent_succ (copyLaw P) (copyAverage P false (fun j => (P.n j : ℝ)))
        (fun _ => (controlCount P : ℝ) / P.M * populationSize P) h.2.2.2.1,
      consistent_succ (copyLaw P) (copiedDifferenceInMeans P)
        (fun _ => averageTreatmentEffect P) h.2.2.2.2⟩
  · intro P
    exact AronowAudit.P020.limit_ratio_identity (toPopulation P)
  · intro P h hh
    exact AronowAudit.P020.replicated_size (toPopulation P) h hh
  · intro P h hh s hs k
    exact AronowAudit.P020.within_replication_invariant (toPopulation P) h hh s k
  · intro P hbias
    exact AronowAudit.P020.fixed_clusters_persistent_bias (toPopulation P) hbias
  · intro h hh
    rfl
  · intro h hh
    exact (AronowAudit.P020.efficiency_all_replications_counterexample h hh 0).2.2.2.1
/-- Existing minima and gap results plus the missing calculus and algebra. -/
theorem T14_assembly (h1 : T14_L1) (h2 : T14_L2) (h3 : T14_L3) : T14WholeStatement := by
  refine ⟨retained_T14, arm_expansion, objective_expansion, h1,
    fun P hs => ⟨h2 P hs, h3 P hs⟩, ?_⟩
  intro P n hn k s
  exact AronowAudit.P020.equal_size_raj_eq_ht (toPopulation P) n hn k s
/-- Error probabilities are finite expectations of indicator functions. -/
theorem error_as_expectation {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (d ε : ℝ) : errorProbability L T d ε = expectation L (fun ω => if ε < |T ω-d| then 1 else 0) := by
  classical
  simp [errorProbability, expectation, mul_ite]
/-- Transfer the full-uniform event bridge to the supported assignment subtype. -/
theorem assignment_event_bridge (h2 : T17_L2) (P : ClusterPopulation) (T : Finset (Fin P.M) → ℝ) (d ε : ℝ) : (W1AssignmentMeasure P).real {s | ε < |T s.val-d|} = errorProbability (clusterLaw P) T d ε := by
  rw [show (W1AssignmentMeasure P).real {s | ε < |T s.val-d|} =
    errorProbability (fullLaw (W1Assignment P)) (fun s => T s.val) d ε from h2 (W1Assignment P) (fun s => T s.val) d ε]
  rw [error_as_expectation, error_as_expectation]
  exact AronowAudit.P020.assignment_subtype_expectation (toPopulation P)
    (fun s => if ε < |T s-d| then 1 else 0)
/-- Prefix marginal laws identify the probability of every statistic's error event, since functions on the finite discrete prefix space are measurable. -/
theorem copy_coupling (h2 : T17_L2) (h3 : T17_L3) (P : ClusterPopulation) : W1CopyCoupling P := by
  refine ⟨h3 P, ?_⟩
  intro h T d ε
  have hp : Measurable (W1Prefix P h) := by
    apply Measurable.of_eval
    intro i
    exact measurable_pi_apply i.val
  have hs : MeasurableSet {s : CopyAssignments P h | ε < |T s-d|} := Set.Finite.measurableSet (Set.toFinite _)
  have hm := congrArg (fun μ : Measure (CopyAssignments P h) => μ.real {s | ε < |T s-d|}) ((h3 P).2.2.2 h)
  rw [Measure.real, Measure.real, Measure.map_apply hp hs] at hm
  change (W1CopyMeasure P).real {ω | ε < |T (W1Prefix P h ω)-d|} = _ at hm
  exact hm.trans (h2 (CopyAssignments P h) T d ε)
/-- Transport one finite-prefix probability limit to the common path space. -/
theorem coupled_limit (P : ClusterPopulation) (hc : W1CopyCoupling P) (T : ∀ r, CopyAssignments P (r+1) → ℝ) (d : ℝ) (hl : DesignConsistent (fun r => copyLaw P (r+1)) T (fun _ => d)) : W1InProbability (W1CopyMeasure P) (fun r ω => T r (W1Prefix P (r+1) ω)) d := by
  refine ⟨inferInstance, ?_⟩
  intro ε hε
  simpa only [hc.2] using hl ε hε
/-- All growth and law certificates are supplied by the leaves; probability limits, replication invariance, preserved bias and the witness are donor results. -/
theorem T17_assembly (h1 : T17_L1) (h2 : T17_L2) (h3 : T17_L3) (h4 : T17_L4) : T17WholeStatement := by
  have hc := copy_coupling h2 h3
  have hd (P : ClusterPopulation) : W1WithinDetails P := by
    intro h hh
    have hi := AronowAudit.P020.within_replication_invariant (toPopulation P) h hh
    have hate : averageTreatmentEffect (replicateWithin P h hh) = averageTreatmentEffect P := (hi ∅ 0).1
    have hdm : differenceInMeans (replicateWithin P h hh) = differenceInMeans P := by
      funext s
      exact (hi s 0).2.1
    refine ⟨?_, rfl, ?_, ?_⟩
    · intro a s
      exact AronowAudit.P020.replicated_arm_size (toPopulation P) h hh a s
    · rw [hdm, hate]
      rfl
    · intro ε
      rw [hdm, hate]
      exact assignment_event_bridge h2 P (differenceInMeans P) (averageTreatmentEffect P) ε
  refine ⟨retained_T17, h1, ?_, hc, h4, ?_, hd, ?_, ?_, ?_⟩
  · intro P h
    simp [controlCount, Nat.mul_sub_left_distrib]
  · intro P
    have hl := retained_T17.1 P
    exact ⟨coupled_limit P (hc P) _ _ hl.1,
      coupled_limit P (hc P) _ _ hl.2.1,
      coupled_limit P (hc P) _ _ hl.2.2.1,
      coupled_limit P (hc P) _ _ hl.2.2.2.1,
      coupled_limit P (hc P) _ _ hl.2.2.2.2⟩
  · intro P
    have hM : (0 : ℝ) < P.M := by exact_mod_cast lt_trans P.mt_pos P.mt_lt
    have ht : (0 : ℝ) < P.mt := by exact_mod_cast P.mt_pos
    have hm : (0 : ℝ) < controlCount P := by exact_mod_cast Nat.sub_pos_of_lt P.mt_lt
    have hN : (0 : ℝ) < populationSize P := by
      exact_mod_cast AronowAudit.P020.populationSize_pos (toPopulation P)
    exact ⟨mul_pos (div_pos ht hM) hN, mul_pos (div_pos hm hM) hN⟩
  · intro P hb
    have hn : ¬ DesignConsistent (fun _ : ℕ => clusterLaw P) (fun _ => differenceInMeans P)
        (fun _ => averageTreatmentEffect P) :=
      (AronowAudit.P020.fixed_clusters_persistent_bias (toPopulation P) hb).2
    refine ⟨fun hh => hn ((withinReplication_consistency_iff P).mp hh), ?_⟩
    intro hh
    apply hn
    intro ε hε
    have he (r : ℕ) : (W1AssignmentMeasure P).real
        {s | ε < |differenceInMeans (replicateWithin P (r+1) (Nat.succ_pos r)) s.val - averageTreatmentEffect P|} =
          errorProbability (clusterLaw P) (differenceInMeans P) (averageTreatmentEffect P) ε := by
      have hi : differenceInMeans (replicateWithin P (r+1) (Nat.succ_pos r)) = differenceInMeans P := by
        funext s
        exact (AronowAudit.P020.within_replication_invariant (toPopulation P) (r+1) (Nat.succ_pos r) s 0).2.1
      rw [hi]
      exact assignment_event_bridge h2 P _ _ _
    simpa only [he] using hh.2 ε hε
  · intro h hh
    have hv := AronowAudit.P020.efficiency_all_replications_counterexample h hh 0
    exact ⟨hv.1, hv.2.1, hv.2.2.2.2.1⟩
end
end SAP.P020.WH.W1
