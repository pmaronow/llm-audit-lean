import AronowAudit.P018.Wave1.Gap.GP0181B1

/-!
P018-T3: the fair-sign Appendix B counterexample. All expectations below
are under the actual finite product law. The sign fit and its scalar
probability limit are those of P018-T11.
-/

noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

local instance appendixB_fairProbability : IsProbabilityMeasure fairLaw :=
  printed_fair_probability

lemma appendixB_sign_abs (b : Bool) : |signValue b| = 1 := by
  cases b <;> norm_num [signValue]

lemma appendixB_populationGram : populationGram signKernel = (1 : Mat 1) := by
  ext a b
  fin_cases a
  fin_cases b
  simp [populationGram, signKernel, meanMat, outer]

lemma appendixB_populationBeta : populationBeta signKernel = 0 := by
  have hm : meanVec (fairLaw.prod fairLaw)
      (fun uv : Bool × Bool => score (![1] : Vec 1) (signValue uv.1 + signValue uv.2)) = 0 := by
    ext a
    fin_cases a
    simp only [meanVec, score, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_fin_one,
      mul_one, Pi.zero_apply]
    rw [integral_prod _ (printed_finite_integrable _ _)]
    change (∫ u, ∫ v, signValue u + signValue v ∂ fairLaw ∂ fairLaw) = 0
    have hi (u : Bool) : (∫ v, signValue u + signValue v ∂ fairLaw) = signValue u := by
      rw [integral_add (integrable_const _) (printed_finite_integrable _ _)]
      rw [integral_const, printed_fair_integral, probReal_univ]
      simp
    simp_rw [hi]
    simp [printed_fair_integral]
  change (populationGram signKernel)⁻¹.mulVec (meanVec (fairLaw.prod fairLaw)
    (fun uv : Bool × Bool => score (![1] : Vec 1) (signValue uv.1 + signValue uv.2))) = 0
  rw [hm, Matrix.mulVec_zero]

lemma appendixB_standing : Standing signKernel := by
  refine ⟨appendixB_fairProbability, measurable_of_countable _, measurable_of_countable _,
    ?_, ?_, ?_, ?_⟩
  · intro u v
    exact ⟨rfl, add_comm _ _⟩
  · refine ⟨2, by norm_num, Filter.Eventually.of_forall (fun uv => ?_)⟩
    constructor
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
      intro a
      fin_cases a
      norm_num [signKernel]
    · change |signValue uv.1 + signValue uv.2| ≤ 2
      calc
        _ ≤ |signValue uv.1| + |signValue uv.2| := abs_add_le _ _
        _ = 2 := by rw [appendixB_sign_abs, appendixB_sign_abs]; norm_num
  · exact ⟨0, fun _ _ => rfl⟩
  · rw [appendixB_populationGram]
    simp

lemma appendixB_sampleRank : SampleRank signKernel := by
  refine ⟨2, fun N hN => Filter.Eventually.of_forall (fun ω => ?_)⟩
  rw [printed_gram]
  simpa [Matrix.det_fin_one] using ne_of_gt (printed_Dpos hN)

lemma appendixB_residual {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → Bool) (d : Dyad N) :
    fittedResidual (design signKernel ω) (response signKernel ω) d =
      signValue (ω (firstUnit d)) + signValue (ω (secondUnit d)) -
        2 / (N : ℝ) * printed_S ω := by
  simp only [fittedResidual, dot, Fin.sum_univ_one, printed_fit hN]
  simp [design, response, signKernel]

lemma appendixB_S_bound {N : ℕ} (ω : Fin N → Bool) : |printed_S ω| ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ i : Fin N, |signValue (ω i)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp [appendixB_sign_abs]

lemma appendixB_residual_bound {N : ℕ} (ω : Fin N → Bool) (d : Dyad N) :
    |fittedResidual (design signKernel ω) (response signKernel ω) d| ≤ 4 := by
  have hN : 2 ≤ N := by
    have h := Finset.card_le_univ (members d)
    simpa only [members_card, Fintype.card_fin] using h
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hfit : |2 / (N : ℝ) * printed_S ω| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 / (N : ℝ))]
    calc
      _ ≤ (2 / (N : ℝ)) * (N : ℝ) :=
        mul_le_mul_of_nonneg_left (appendixB_S_bound ω) (by positivity)
      _ = 2 := by field_simp
  rw [appendixB_residual hN]
  calc
    _ ≤ |signValue (ω (firstUnit d)) + signValue (ω (secondUnit d))| +
        |2 / (N : ℝ) * printed_S ω| := by simpa using (abs_sub_le
          (signValue (ω (firstUnit d)) + signValue (ω (secondUnit d))) 0
          (2 / (N : ℝ) * printed_S ω))
    _ ≤ (|signValue (ω (firstUnit d))| + |signValue (ω (secondUnit d))|) + 2 :=
      add_le_add (abs_add_le _ _) hfit
    _ = 4 := by norm_num [appendixB_sign_abs]

lemma appendixB_coord_mean {N : ℕ} (i : Fin N) :
    (∫ ω, signValue (ω i) ∂ unitSampleLaw signKernel N) = 0 := by
  change (∫ ω : Fin N → Bool, signValue (ω i) ∂ Measure.pi (fun _ => fairLaw)) = 0
  rw [integral_comp_eval (measurable_of_countable signValue).aestronglyMeasurable,
    printed_fair_integral]

lemma appendixB_coord_product {N : ℕ} (i j : Fin N) :
    (∫ ω, signValue (ω i) * signValue (ω j) ∂ unitSampleLaw signKernel N) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp_rw [← pow_two, printed_sign_square]
    simp
  · have hi : iIndepFun (fun i (ω : Fin N → Bool) => signValue (ω i))
        (unitSampleLaw signKernel N) :=
      by simpa only [unitSampleLaw, signKernel] using
        (iIndepFun_pi (μ := fun _ : Fin N => fairLaw) (X := fun _ => signValue)
          (fun _ => (measurable_of_countable signValue).aemeasurable))
    rw [(hi.indepFun hij).integral_fun_mul_eq_mul_integral
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aestronglyMeasurable]
    simp [appendixB_coord_mean, hij]

/-- The exact inner product formula for linear combinations of iid signs. -/
lemma appendixB_linear_product {N : ℕ} (a b : Fin N → ℝ) :
    (∫ ω, (∑ i, a i * signValue (ω i)) * (∑ j, b j * signValue (ω j))
      ∂ unitSampleLaw signKernel N) = ∑ i, a i * b i := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun _ _ => printed_finite_integrable _ _)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun _ _ => printed_finite_integrable _ _)]
  have he (j : Fin N) (ω : Fin N → Bool) :
      a i * signValue (ω i) * (b j * signValue (ω j)) =
        (a i * b j) * (signValue (ω i) * signValue (ω j)) := by ring
  simp_rw [he, integral_const_mul, appendixB_coord_product]
  simp

lemma appendixB_indicator_sum {N : ℕ} (s : Finset (Fin N)) (u : Fin N → ℝ) :
    (∑ i : Fin N, if i ∈ s then u i else 0) = ∑ i ∈ s, u i := by
  classical
  rw [← Finset.sum_filter]
  simp

lemma appendixB_residual_linear {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → Bool) (d : Dyad N) :
    fittedResidual (design signKernel ω) (response signKernel ω) d =
      ∑ i : Fin N, ((if i ∈ members d then 1 else 0) - 2 / (N : ℝ)) *
        signValue (ω i) := by
  classical
  rw [appendixB_residual hN]
  simp_rw [sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, appendixB_indicator_sum,
    printed_members_endpoints, Finset.sum_pair (ne_of_lt (printed_endpoints_lt d))]
  rfl

lemma appendixB_residual_product {N : ℕ} (hN : 2 ≤ N) (d f : Dyad N) :
    (∫ ω, fittedResidual (design signKernel ω) (response signKernel ω) d *
      fittedResidual (design signKernel ω) (response signKernel ω) f
      ∂ unitSampleLaw signKernel N) =
        ((members d ∩ members f).card : ℝ) - 4 / (N : ℝ) := by
  classical
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp_rw [appendixB_residual_linear hN]
  rw [appendixB_linear_product]
  have he (i : Fin N) :
      ((if i ∈ members d then (1 : ℝ) else 0) - 2 / (N : ℝ)) *
        ((if i ∈ members f then (1 : ℝ) else 0) - 2 / (N : ℝ)) =
      (if i ∈ members d ∩ members f then (1 : ℝ) else 0) -
        (2 / (N : ℝ)) * (if i ∈ members d then 1 else 0) -
        (2 / (N : ℝ)) * (if i ∈ members f then 1 else 0) + (2 / (N : ℝ))^2 := by
    by_cases hd : i ∈ members d <;> by_cases hf : i ∈ members f <;> simp [hd, hf] <;> ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [appendixB_indicator_sum]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, members_card, Nat.cast_ofNat]
  field_simp [hn]
  <;> ring

lemma appendixB_extra : Proposition1Extra signKernel := by
  refine ⟨⟨4, by norm_num, fun N => Filter.Eventually.of_forall (fun ω d =>
    appendixB_residual_bound ω d)⟩, ?_, ?_, ?_⟩
  · intro a b
    fin_cases a
    fin_cases b
    simp [appendixB_populationGram]
  · intro a b
    fin_cases a
    fin_cases b
    simp [meanMat, outer, signKernel]
  · filter_upwards [eventually_ge_atTop 5] with N hN
    have hn : (5 : ℝ) ≤ N := by exact_mod_cast hN
    have hN2 : 2 ≤ N := by omega
    have hnpos : (0 : ℝ) < N := by linarith
    constructor
    · intro d
      simp_rw [pow_two]
      rw [appendixB_residual_product hN2]
      simp only [Finset.inter_self, members_card, Nat.cast_ofNat]
      have : 4 / (N : ℝ) < 2 := (div_lt_iff₀ hnpos).mpr (by linarith)
      linarith
    · intro d f hf
      obtain ⟨hfd, hov⟩ := Finset.mem_filter.mp hf |>.2
      have hc := intersection_count members members_card (fun d e h => Subtype.ext h) d f
      simp only [hov, if_true, Ne.symm hfd, if_false, add_zero] at hc
      rw [appendixB_residual_product hN2, hc]
      have : 4 / (N : ℝ) < 1 := (div_lt_iff₀ hnpos).mpr (by linarith)
      linarith

lemma appendixB_scoreSum {N : ℕ} (ω : Fin N → Bool) :
    scoreSum signKernel ω 0 = ((N : ℝ) - 1) * printed_S ω := by
  simp only [scoreSum, Finset.sum_apply, score, Pi.smul_apply, smul_eq_mul,
    epsilon, populationResidual, appendixB_populationBeta, dot,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]
  simp only [design, signKernel, Matrix.cons_val_fin_one, mul_one]
  exact printed_pair_add (fun i => signValue (ω i))

lemma appendixB_trueTarget {N : ℕ} (hN : 4 ≤ N) : trueTarget signKernel N = !![4] := by
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hv : varMat (unitSampleLaw signKernel N) (scoreSum signKernel) 0 0 =
      (N : ℝ) * ((N : ℝ) - 1)^2 := by
    change ProbabilityTheory.covariance (fun ω => scoreSum signKernel ω 0)
      (fun ω => scoreSum signKernel ω 0) (unitSampleLaw signKernel N) = _
    simp_rw [appendixB_scoreSum]
    rw [covariance_self (measurable_of_countable _).aemeasurable,
      variance_const_mul, printed_S_variance]
    ring
  ext a b
  fin_cases a
  fin_cases b
  simp only [trueTarget, appendixB_populationGram, inv_one, sandwich,
    Matrix.one_mul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul, hv,
    Matrix.of_apply, Matrix.cons_val_zero]
  change ((N : ℝ) / (Dreal N)^2) *
    varMat (unitSampleLaw signKernel N) (scoreSum signKernel) 0 0 = 4
  rw [hv]
  dsimp [Dreal]
  field_simp [hn0, hn1]
  <;> ring

lemma appendixB_variance_mean {N : ℕ} (hN : 4 ≤ N) :
    (∫ ω, (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0
      ∂ unitSampleLaw signKernel N) =
        4*((N : ℝ)-2)*((N : ℝ)-3)/((N : ℝ)^2*((N : ℝ)-1)) := by
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have he := congrArg (fun f : (Fin N → Bool) → ℝ =>
    ∫ ω, f ω ∂ unitSampleLaw signKernel N) (funext (printed_scaled_sandwich hN))
  change (∫ ω, (N : ℝ) *
    (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0
    ∂ unitSampleLaw signKernel N) =
      ∫ ω, printed_A N * (1 - (printed_S ω / (N : ℝ))^2)
        ∂ unitSampleLaw signKernel N at he
  rw [integral_const_mul, integral_const_mul,
    integral_sub (integrable_const _) (printed_finite_integrable _ _),
    integral_const, probReal_univ, smul_eq_mul, one_mul,
    printed_Z_mean (by omega : 1 ≤ N)] at he
  apply mul_left_cancel₀ hn0
  rw [he]
  dsimp [printed_A]
  field_simp [hn0, hn1]
  <;> ring

lemma appendixB_meat_sandwich {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → Bool) :
    (Dreal N)^2 * (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 =
      meat members (fun d => score (design signKernel ω d)
        (fittedResidual (design signKernel ω) (response signKernel ω) d)) 0 0 := by
  have hD := ne_of_gt (printed_Dpos hN)
  unfold sampleVariance
  rw [printed_gram_inv hN]
  simp only [sandwich, Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply,
    Matrix.one_apply, if_true, smul_eq_mul]
  field_simp [hD]
  <;> ring

lemma appendixB_meat_mean {N : ℕ} (hN : 4 ≤ N) :
    meanMat (unitSampleLaw signKernel N) (fun ω =>
      meat members (fun d => score (design signKernel ω d)
        (fittedResidual (design signKernel ω) (response signKernel ω) d))) =
      !![((N : ℝ)-1)*((N : ℝ)-2)*((N : ℝ)-3)] := by
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ) - 1 ≠ 0 := by linarith
  ext a b
  fin_cases a
  fin_cases b
  change (∫ ω, meat members (fun d => score (design signKernel ω d)
    (fittedResidual (design signKernel ω) (response signKernel ω) d)) 0 0
    ∂ unitSampleLaw signKernel N) = ((N : ℝ)-1)*((N : ℝ)-2)*((N : ℝ)-3)
  calc
    _ = ∫ ω, (Dreal N)^2 *
        (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0
          ∂ unitSampleLaw signKernel N :=
      integral_congr_ae (Filter.Eventually.of_forall (fun ω =>
        (appendixB_meat_sandwich (by omega : 2 ≤ N) ω).symm))
    _ = _ := by
      rw [integral_const_mul, appendixB_variance_mean hN]
      dsimp [Dreal]
      field_simp [hn0, hn1]
      <;> ring

lemma appendixB_variance_mean_limit :
    Tendsto (fun N : ℕ => (∫ ω,
      (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0
        ∂ unitSampleLaw signKernel N)) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => printed_A N * (N : ℝ)⁻¹ * (1 - (N : ℝ)⁻¹))
      atTop (𝓝 0) := by
    have hh := (printed_A_limit.mul printed_inv_n_limit).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub printed_inv_n_limit)
    simpa using hh
  apply h.congr'
  filter_upwards [eventually_ge_atTop 4] with N hN
  rw [appendixB_variance_mean hN]
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ) - 1 ≠ 0 := by linarith
  dsimp [printed_A]
  field_simp [hn0, hn1]
  <;> ring

lemma appendixB_matrix_norm (A : Mat 1) : ‖A‖ = ‖A 0 0‖ := by
  apply le_antisymm
  · apply (Matrix.norm_le_iff (norm_nonneg (A 0 0))).mpr
    intro a b
    fin_cases a
    fin_cases b
    exact le_rfl
  · exact (norm_le_pi_norm (A 0) 0).trans (norm_le_pi_norm A 0)

lemma appendixB_probability_limit :
    inProbability (unitSampleLaw signKernel) (fun N ω =>
      (N : ℝ) • sampleVariance members (design signKernel ω) (response signKernel ω) -
        (!![4] : Mat 1)) := by
  intro ε hε
  have h := printed_sandwich_probability_limit ε hε
  simpa only [appendixB_matrix_norm, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.of_apply] using h

theorem appendixB_counterexample_proof :
    Standing signKernel ∧ SampleRank signKernel ∧ Proposition1Extra signKernel ∧
    populationBeta signKernel = 0 ∧
    (∀ N : ℕ, 4 ≤ N → trueTarget signKernel N = !![4] ∧
      meanMat (unitSampleLaw signKernel N) (fun ω =>
        meat members (fun d => score (design signKernel ω d)
          (fittedResidual (design signKernel ω) (response signKernel ω) d))) =
          !![((N : ℝ)-1)*((N : ℝ)-2)*((N : ℝ)-3)] ∧
      (∫ ω, (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 ∂ unitSampleLaw signKernel N) =
        4*((N : ℝ)-2)*((N : ℝ)-3)/((N : ℝ)^2*((N : ℝ)-1))) ∧
    Tendsto (fun N : ℕ => (∫ ω,
      (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 ∂ unitSampleLaw signKernel N)-4)
      atTop (𝓝 (-4)) ∧
    inProbability (unitSampleLaw signKernel) (fun N ω =>
      (N : ℝ) • sampleVariance members (design signKernel ω) (response signKernel ω) - (!![4] : Mat 1)) := by
  refine ⟨appendixB_standing, appendixB_sampleRank, appendixB_extra,
    appendixB_populationBeta, ?_, ?_, appendixB_probability_limit⟩
  · intro N hN
    exact ⟨appendixB_trueTarget hN, appendixB_meat_mean hN, appendixB_variance_mean hN⟩
  · simpa using appendixB_variance_mean_limit.sub_const 4

end AronowAudit.P018.Wave1
