import AronowAudit.P011.P011_FiniteLawCompletion
import AronowAudit.P011.P011_SampleCompletion
import AronowAudit.P011.P011_SpectralCompletion
import AronowAudit.P011.P011_StarCompletion


namespace AronowAudit.P011.Wave1
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

/- P011-T11: the full sequence, including odd sample sizes. -/
private def t11_mu (n : ℕ) (i : Fin n) : ℝ := if i.val % 2 = 0 then 2 else 0

private lemma t11_sum_mu (n : ℕ) :
    (∑ i : Fin n, t11_mu n i) = 2 * (((n+1)/2 : ℕ) : ℝ) := by
  induction n with
  | zero => simp [t11_mu]
  | succ n ih =>
    simp only [t11_mu, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last] at ih ⊢
    rw [ih]
    by_cases h : n % 2 = 0
    · have he : (n+1+1)/2 = (n+1)/2+1 := by omega
      simp [h, he, Nat.cast_add]
      <;> ring
    · have he : (n+1+1)/2 = (n+1)/2 := by omega
      simp [h, he]

private lemma t11_weight_bounds (n : ℕ) (hn : 0 < n) :
    1/2 ≤ alternatingWeight n ∧ alternatingWeight n ≤ 1 ∧
    (n : ℝ)/((n : ℝ)+1) ≤ alternatingWeight n := by
  have hp : 0 < (n+1)/2 := by omega
  have hpn : n ≤ 2*((n+1)/2) := by omega
  have hnp : 2*((n+1)/2) ≤ n+1 := by omega
  have hp2 : (n+1)/2 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (0 : ℝ) < 2 * (((n+1)/2 : ℕ) : ℝ) := by positivity
  have hpnR : (n : ℝ) ≤ 2 * (((n+1)/2 : ℕ) : ℝ) := by exact_mod_cast hpn
  have hnpR : 2 * (((n+1)/2 : ℕ) : ℝ) ≤ (n : ℝ)+1 := by exact_mod_cast hnp
  have hp2R : (((n+1)/2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hp2
  dsimp [alternatingWeight]
  refine ⟨(le_div_iff₀ hd).mpr (by linarith),
    (div_le_iff₀ hd).mpr (by linarith), ?_⟩
  exact div_le_div_of_nonneg_left hnR.le hd hnpR

private lemma t11_weight_limit :
    Tendsto (fun k => alternatingWeight (k+1)) atTop (𝓝 1) := by
  have hN : Tendsto (fun k : ℕ => (k+1 : ℝ)+1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        (show Tendsto (fun k : ℕ => k+1+1) atTop atTop from
          tendsto_atTop_mono (fun k => by change k ≤ k+1+1; omega) tendsto_id))
  have hlow : Tendsto (fun k : ℕ => (k+1 : ℝ)/((k+1 : ℝ)+1)) atTop (𝓝 1) := by
    have he : (fun k : ℕ => (k+1 : ℝ)/((k+1 : ℝ)+1)) =
        (fun (k : ℕ) => 1-1/((k+1 : ℝ)+1)) := by
      funext k
      have hden : (k+1 : ℝ)+1 ≠ 0 := by positivity
      field_simp [hden]
      <;> ring
    rw [he]
    simpa using tendsto_const_nhds.sub (hN.const_div_atTop 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun k => by simpa only [Nat.cast_add, Nat.cast_one] using (t11_weight_bounds (k+1) (by omega)).2.2)
    (fun k => (t11_weight_bounds (k+1) (by omega)).2.1)

private lemma t11_dependency (n : ℕ) : Dependency (alternatingModel n) := by
  exact uniform_coordinate_dependency Bool
    (fun i b => t11_mu n i + sign b) (fun _ => measurable_of_finite _)

private lemma t11_mean (n : ℕ) (i : Fin n) :
    expectation (alternatingModel n) (fun y => weighted (alternatingModel n) y i) =
      alternatingWeight n * t11_mu n i := by
  change (∫ y : Fin n → ℝ, alternatingWeight n * y i ∂uniformLaw (fun (u : Fin n → Bool) j => t11_mu n j + sign (u j))) = _
  rw [NewFiniteCompletion.coord_integral Bool
    (fun i b => t11_mu n i + sign b) i (fun x => alternatingWeight n*x) (by fun_prop)]
  simp [Fintype.sum_bool, sign]
  <;> ring

private lemma t11_beta (n : ℕ) (hn : 0 < n) : beta (alternatingModel n) = 1 := by
  let : IsProbabilityMeasure (alternatingModel n).law := (alternatingModel n).probability
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hp : (((n+1)/2 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < (n+1)/2 := by omega
    positivity
  have hL2 (i : Fin n) : MemLp (fun y => weighted (alternatingModel n) y i) 2
      (alternatingModel n).law :=
    NewFiniteCompletion.finite_memLp (alternatingOutcome n) _ (by unfold weighted; fun_prop) 2
  unfold beta betaHat average expectation
  rw [integral_div, integral_finsetSum Finset.univ
    (fun i _ => (hL2 i).integrable (by norm_num))]
  change (∑ i, expectation (alternatingModel n)
    (fun y => weighted (alternatingModel n) y i))/(n : ℝ) = 1
  simp_rw [t11_mean]
  rw [← Finset.mul_sum, t11_sum_mu]
  dsimp [alternatingWeight]
  field_simp
  <;> ring

private lemma t11_covariance (n : ℕ) (i j : Fin n) :
    covariance (alternatingModel n) i j =
      if i=j then alternatingWeight n^2 else 0 := by
  let m := alternatingModel n
  let : IsProbabilityMeasure m.law := m.probability
  have hL2 (i : Fin n) : MemLp (fun y => weighted m y i) 2 m.law :=
    NewFiniteCompletion.finite_memLp (alternatingOutcome n) _ (by unfold weighted; fun_prop) 2
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    unfold covariance
    rw [t11_mean]
    change (∫ y : Fin n → ℝ, (alternatingWeight n*y i-alternatingWeight n*t11_mu n i)*
      (alternatingWeight n*y i-alternatingWeight n*t11_mu n i)
      ∂uniformLaw (fun (u : Fin n → Bool) j => t11_mu n j + sign (u j))) = _
    rw [NewFiniteCompletion.coord_integral Bool (fun i b => t11_mu n i+sign b) i
      (fun x => (alternatingWeight n*x-alternatingWeight n*t11_mu n i)*
        (alternatingWeight n*x-alternatingWeight n*t11_mu n i)) (by fun_prop)]
    simp [Fintype.sum_bool, sign]
    <;> ring
  · rw [if_neg hij, QuadraticCompletion.covariance_eq_mathlib]
    have hi := t11_dependency n {i} {j} (by simpa using hij)
      (by simp [alternatingModel, emptyGraph])
    have hr : IndepFun (fun y : Fin n → ℝ => y i) (fun y => y j) m.law := by
      simpa only [Function.comp_def] using hi.comp
        (measurable_pi_apply ⟨i, by simp⟩) (measurable_pi_apply ⟨j, by simp⟩)
    have hw : IndepFun (fun y => weighted m y i) (fun y => weighted m y j) m.law := by
      exact hr.comp (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
    exact hw.covariance_eq_zero (hL2 i) (hL2 j)

private lemma t11_scaled_variance (n : ℕ) (hn : 0 < n) :
    (n : ℝ)*var (alternatingModel n) (betaHat (alternatingModel n)) =
      alternatingWeight n^2 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [QuadraticCompletion.beta_variance _ (fun i =>
    NewFiniteCompletion.finite_memLp (alternatingOutcome n) _ (by unfold weighted; fun_prop) 2)]
  simp [QuadraticCompletion.total, t11_covariance]
  <;> field_simp
  <;> ring

private lemma t11_spread (n : ℕ) (hn : 0 < n) :
    meanSpread (alternatingModel n) = 2*alternatingWeight n-1 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hp : (((n+1)/2 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < (n+1)/2 := by omega
    positivity
  have hterm (i : Fin n) : (alternatingWeight n*t11_mu n i-1)^2 =
      (2*alternatingWeight n^2-2*alternatingWeight n)*t11_mu n i+1 := by
    unfold t11_mu
    split_ifs <;> ring
  unfold meanSpread delta
  simp_rw [t11_mean,t11_beta n hn,hterm]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,t11_sum_mu]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  dsimp [alternatingWeight]
  field_simp
  <;> ring

private lemma t11_bound (n : ℕ) (hn : 0 < n) :
    ∀ᵐ y ∂(alternatingModel n).law, ∀ i,
      |weighted (alternatingModel n) y i-beta (alternatingModel n)| ≤ 2 := by
  have ht := t11_weight_bounds n hn
  have hf : Measurable (alternatingOutcome n) := measurable_of_finite _
  have hlaw : (alternatingModel n).law =
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure.map (alternatingOutcome n) :=
    (PMF.toMeasure_map _ _ hf).symm
  rw [hlaw]
  apply (ae_map_iff hf.aemeasurable (by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (by unfold weighted; fun_prop)
      measurable_const)).mpr
  filter_upwards [] with u i
  rw [t11_beta n hn]
  change |alternatingWeight n*((if i.val%2=0 then 2 else 0)+sign (u i))-1| ≤ 2
  by_cases hi : i.val%2=0 <;> cases hu : u i <;>
    simp [hi,sign,hu] <;>
    apply abs_le.mpr <;> constructor <;> nlinarith [ht.1, ht.2.1]

private lemma t11_scaling : Scaling alternatingFamily 2 1 1 2 := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num,
    (fun k => t11_dependency (k+1)), ?_, ?_, ?_, ?_⟩
  · constructor
    · intro a b hab
      exact Nat.succ_le_succ hab
    · intro k
      exact ⟨Fin.castSuccEmb, fun _ _ => rfl⟩
  · intro k
    exact t11_bound (k+1) (by omega)
  · intro k i
    simp [degree, alternatingFamily, alternatingModel, emptyGraph]
  · have he : (fun k => (alternatingFamily.size k : ℝ)*
        var (alternatingFamily.model k) (betaHat (alternatingFamily.model k))) =
        (fun k => alternatingWeight (k+1)^2) := by
      funext k
      exact t11_scaled_variance (k+1) (by omega)
    rw [he]
    simpa using t11_weight_limit.pow 2
  · intro k i
    have ht := t11_weight_bounds (k+1) (by omega)
    change |alternatingWeight (k+1)| < 2
    rw [abs_of_nonneg (by linarith [ht.1])]
    linarith [ht.2.1]

private lemma t11_V2 (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) :
    (n : ℝ)*V2 (emptyGraph n) x = sampleVariance x := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp [V2, adjacency, emptyGraph]
  <;> field_simp

private def t11_D (k : ℕ) (y : Fin (k+1) → ℝ) : ℝ :=
  (k+1 : ℝ)*V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y)
    - scaledTrue alternatingFamily k

private lemma t11_D_measurable (k : ℕ) : Measurable (t11_D k) := by
  unfold t11_D V2 sampleVariance centered average weighted
  fun_prop

private lemma t11_limit : InProbability alternatingFamily t11_D (fun _ => 1) := by
  let (k : ℕ) : IsProbabilityMeasure (alternatingFamily.model k).law :=
    (alternatingFamily.model k).probability
  have hs := revised_sample_variance alternatingFamily 2 1 1 2 t11_scaling
  have hm (k : ℕ) : meanVariance (alternatingFamily.model k) = alternatingWeight (k+1)^2 := by
    change (∑ i : Fin (k+1), covariance (alternatingModel (k+1)) i i)/((k+1 : ℕ) : ℝ) = _
    simp only [t11_covariance,eq_self_iff_true,ite_true,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    have hn0 : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring
  have hmove : ∀ ε > (0 : ℝ), Tendsto
      (fun k => (alternatingFamily.model k).law.real
        {y | |t11_D k y-(2*alternatingWeight (k+1)-1)| > ε}) atTop (𝓝 0) := by
    intro ε hε
    convert hs ε hε using 1
    funext k
    apply congrArg (fun E => (alternatingFamily.model k).law.real E)
    ext y
    change Fin (k+1) → ℝ at y
    change (|t11_D k y-(2*alternatingWeight (k+1)-1)| > ε) ↔
      ε < |sampleVariance (weighted (alternatingFamily.model k) y) -
        (meanVariance (alternatingFamily.model k) + meanSpread (alternatingFamily.model k))|
    rw [hm k, show meanSpread (alternatingFamily.model k) = 2*alternatingWeight (k+1)-1
      from t11_spread (k+1) (by omega)]
    have hv := t11_scaled_variance (k+1) (by omega)
    have hV := t11_V2 (k+1) (by omega) (weighted (alternatingFamily.model k) y)
    change (|t11_D k y-(2*alternatingWeight (k+1)-1)| > ε) ↔ _
    dsimp [t11_D, scaledTrue, alternatingFamily] at *
    simp only [Nat.cast_add,Nat.cast_one] at hV hv ⊢
    change (|((k : ℝ)+1) * V2 (emptyGraph (k+1)) (weighted (alternatingModel (k+1)) y) -
      ((k : ℝ)+1) * var (alternatingModel (k+1)) (betaHat (alternatingModel (k+1))) -
      (2*alternatingWeight (k+1)-1)| > ε) ↔ _
    rw [hV, hv]
    congr 2
    ring
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hcenter : Tendsto (fun k => 2*alternatingWeight (k+1)-1) atTop (𝓝 1) := by
    convert (htwo.mul t11_weight_limit).sub hone using 1 <;> norm_num
  exact CoverageCompletion.rowCP_moving_center _ _ _ 1 hmove hcenter

private lemma t11_event_limit (E : ∀ k, Set (Fin (k+1) → ℝ))
    (δ : ℝ) (hδ : 0 < δ)
    (hgood : ∀ k y, |t11_D k y-1| ≤ δ → y ∈ E k) :
    Tendsto (fun k => probability (alternatingFamily.model k) (E k)) atTop (𝓝 1) := by
  let (k : ℕ) : IsProbabilityMeasure (alternatingFamily.model k).law :=
    (alternatingFamily.model k).probability
  have ht := t11_limit δ hδ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using tendsto_const_nhds.sub ht) tendsto_const_nhds
  · intro k
    have hset : MeasurableSet {y | |t11_D k y-1| > δ} :=
      measurableSet_lt measurable_const ((t11_D_measurable k).sub_const 1).abs
    have hc := measureReal_compl (μ := (alternatingFamily.model k).law) hset
    rw [probReal_univ] at hc
    change 1 - (alternatingFamily.model k).law.real {y | |t11_D k y-1| > δ} ≤ _
    apply le_trans (le_of_eq hc.symm)
    exact measureReal_mono (μ := (alternatingFamily.model k).law)
      (fun y hy => hgood k y (by
        change ¬ δ < |t11_D k y-1| at hy
        exact le_of_not_gt hy))
      (measure_ne_top _ _)
  · intro k
    simpa [probability] using measureReal_mono (μ := (alternatingFamily.model k).law)
      (Set.subset_univ (E k)) (measure_ne_top _ _)

theorem alternating_counterexample_proof :
    Scaling alternatingFamily 2 1 1 2 ∧ Valid alternatingFamily ∧
    (∀ k, Homoskedastic (alternatingFamily.model k) ∧ beta (alternatingFamily.model k) = 1 ∧
      scaledTrue alternatingFamily k = alternatingWeight (k+1)^2) ∧
    InProbability alternatingFamily
      (fun k y => (k+1 : ℝ)*V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y)
        - scaledTrue alternatingFamily k) (fun _ => 1) ∧
    Tendsto (fun k => probability (alternatingFamily.model k)
      {y | |(k+1 : ℝ)*V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y)
        - scaledTrue alternatingFamily k| > 1/2}) atTop (𝓝 1) ∧
    Tendsto (fun k => probability (alternatingFamily.model k)
      {y | |(k+1 : ℝ)*V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y)
        - scaledTrue alternatingFamily k| < 3/2}) atTop (𝓝 1) ∧
    Conservative alternatingFamily
      (fun k y => V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y)) := by
  refine ⟨t11_scaling, ?_, ?_, t11_limit, ?_, ?_, ?_⟩
  · intro k
    constructor
    · intro i j hij
      simp [alternatingFamily, alternatingModel, emptyGraph] at hij
    · intro i
      simp [degree, alternatingFamily, alternatingModel, emptyGraph]
  · intro k
    refine ⟨?_, t11_beta (k+1) (by omega), t11_scaled_variance (k+1) (by omega)⟩
    intro i j
    simp only [alternatingFamily, t11_covariance, if_pos rfl]
  · apply t11_event_limit _ (1/4) (by norm_num)
    intro k y hy
    have hh := abs_le.mp hy
    change 1/2 < |t11_D k y|
    exact lt_of_lt_of_le (by linarith [hh.1]) (le_abs_self _)
  · apply t11_event_limit _ (1/4) (by norm_num)
    intro k y hy
    have hh := abs_le.mp hy
    change |t11_D k y| < 3/2
    exact abs_lt.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩
  · intro ε hε
    let (k : ℕ) : IsProbabilityMeasure (alternatingFamily.model k).law :=
      (alternatingFamily.model k).probability
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun k => ?_)
      (t11_limit (1/2) (by norm_num))
    apply measureReal_mono (μ := (alternatingFamily.model k).law) ?_ (measure_ne_top _ _)
    intro y hy
    have hD : t11_D k y < 0 := by
      change ε < (alternatingFamily.size k : ℝ)*
        (var (alternatingFamily.model k) (betaHat (alternatingFamily.model k)) -
          V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y)) at hy
      dsimp [t11_D, scaledTrue, alternatingFamily] at *
      push_cast at hy ⊢
      nlinarith
    change 1/2 < |t11_D k y-1|
    rw [abs_of_neg (by linarith : t11_D k y-1 < 0)]
    linarith

/- P011-T13: small exact matching certificates. -/
private def t13_e01 : Edge 4 := ⟨(0,1), by decide⟩
private def t13_e02 : Edge 4 := ⟨(0,2), by decide⟩
private def t13_e03 : Edge 4 := ⟨(0,3), by decide⟩
private def t13_e12 : Edge 4 := ⟨(1,2), by decide⟩
private def t13_e13 : Edge 4 := ⟨(1,3), by decide⟩
private def t13_e23 : Edge 4 := ⟨(2,3), by decide⟩

private lemma t13_edges : (Finset.univ : Finset (Edge 4)) =
    {t13_e01,t13_e02,t13_e03,t13_e12,t13_e13,t13_e23} := by
  ext e
  rcases e with ⟨⟨i,j⟩, hij⟩
  fin_cases i <;> fin_cases j
  all_goals dsimp only [Prod.fst,Prod.snd] at hij
  all_goals norm_num at hij
  all_goals simp [t13_e01,t13_e02,t13_e03,t13_e12,t13_e13,t13_e23]


private lemma t13_optional_false : optionalEdges (matchingWitness false) =
    {t13_e01,t13_e03,t13_e12,t13_e13} := by
  unfold optionalEdges
  rw [t13_edges]
  ext e
  simp [matchingWitness,t13_e01,t13_e02,t13_e03,t13_e12,t13_e13,t13_e23]
  <;> aesop

private lemma t13_optional_true : optionalEdges (matchingWitness true) =
    {t13_e01,t13_e03,t13_e12,t13_e13,t13_e23} := by
  unfold optionalEdges
  rw [t13_edges]
  ext e
  simp [matchingWitness,t13_e01,t13_e02,t13_e03,t13_e12,t13_e13,t13_e23]
  <;> aesop

private lemma t13_caps_false (i : Fin 4) :
    remainingCap (matchingWitness false) i = (![1,1,0,2] : Fin 4 → ℕ) i := by
  fin_cases i <;> norm_num [remainingCap,edgeDegree,matchingWitness,Finset.filter_insert,Finset.filter_singleton]

private lemma t13_caps_true (i : Fin 4) :
    remainingCap (matchingWitness true) i = (![0,1,0,1] : Fin 4 → ℕ) i := by
  fin_cases i <;> norm_num [remainingCap,edgeDegree,matchingWitness,Finset.filter_insert,Finset.filter_singleton]

private lemma t13_L (second : Bool) : denominatorLCM (matchingWitness second) = 4 := by
  cases second <;> unfold denominatorLCM
  · rw [t13_optional_false]
    norm_num [matchingWitness,t13_e01,t13_e03,t13_e12,t13_e13,
      Finset.lcm_insert,Finset.lcm_singleton]
  · rw [t13_optional_true]
    norm_num [matchingWitness,t13_e01,t13_e03,t13_e12,t13_e13,t13_e23,
      Finset.lcm_insert,Finset.lcm_singleton]

private lemma t13_M (second : Bool) : gadgetM (matchingWitness second) = 10 := by
  cases second <;> unfold gadgetM
  · rw [t13_optional_false]
    simp only [integerWeight,t13_L]
    norm_num [matchingWitness,t13_e01,t13_e03,t13_e12,t13_e13]
  · rw [t13_optional_true]
    simp only [integerWeight,t13_L]
    norm_num [matchingWitness,t13_e01,t13_e03,t13_e12,t13_e13,t13_e23]

private lemma t13_graph_value (second : Bool) :
    EdgeFeasible (matchingWitness second) (matchingWitnessSolution second) ∧
    edgeObjective (matchingWitness second) (matchingWitnessSolution second) =
      (if second then -3/4 else 3/4) := by
  cases second <;> constructor
  · constructor
    · simp [matchingWitnessSolution]
    · intro i
      fin_cases i <;> norm_num [edgeDegree,matchingWitnessSolution,matchingWitness,
        Finset.filter_insert,Finset.filter_singleton]
  · norm_num [edgeObjective,matchingWitnessSolution,matchingWitness]
  · constructor
    · simp [matchingWitnessSolution]
    · intro i
      fin_cases i <;> norm_num [edgeDegree,matchingWitnessSolution,matchingWitness,
        Finset.filter_insert,Finset.filter_singleton]
  · norm_num [edgeObjective,matchingWitnessSolution,matchingWitness]

private lemma t13_graph_upper (second : Bool) (T : Finset (Edge 4))
    (hT : EdgeFeasible (matchingWitness second) T) :
    edgeObjective (matchingWitness second) T ≤
      edgeObjective (matchingWitness second) (matchingWitnessSolution second) := by
  have h02 : t13_e02 ∈ T := hT.1 (by cases second <;> simp [matchingWitness,t13_e02])
  have hobj : edgeObjective (matchingWitness second) T =
      (if t13_e01 ∈ T then (3/4 : ℚ) else 0) +
      (if t13_e02 ∈ T then (-3/4 : ℚ) else 0) +
      (if t13_e03 ∈ T then (-9/4 : ℚ) else 0) +
      (if t13_e12 ∈ T then (-1/4 : ℚ) else 0) +
      (if t13_e13 ∈ T then (-3/4 : ℚ) else 0) +
      (if t13_e23 ∈ T then (3/4 : ℚ) else 0) := by
    have he : edgeObjective (matchingWitness second) T =
        ∑ e ∈ (Finset.univ : Finset (Edge 4)),
          if e ∈ T then (matchingWitness second).weight e else 0 := by
      simp [edgeObjective]
    rw [he,t13_edges]
    rw [Finset.sum_insert (by decide : t13_e01 ∉ {t13_e02,t13_e03,t13_e12,t13_e13,t13_e23}),
      Finset.sum_insert (by decide : t13_e02 ∉ {t13_e03,t13_e12,t13_e13,t13_e23}),
      Finset.sum_insert (by decide : t13_e03 ∉ {t13_e12,t13_e13,t13_e23}),
      Finset.sum_insert (by decide : t13_e12 ∉ {t13_e13,t13_e23}),
      Finset.sum_insert (by decide : t13_e13 ∉ {t13_e23}), Finset.sum_singleton]
    norm_num [matchingWitness,t13_e01,t13_e02,t13_e03,t13_e12,t13_e13,t13_e23]
    <;> ring
  rw [(t13_graph_value second).2]
  cases second
  · have h23 : t13_e23 ∈ T := hT.1 (by simp [matchingWitness,t13_e23])
    rw [hobj,if_pos h02,if_pos h23]
    split_ifs <;> norm_num <;> contradiction
  · have hnot (e : Edge 4) (he : e ≠ t13_e02)
        (hi : e.val.1 = 0 ∨ e.val.2 = 0 ∨ e.val.1 = 2 ∨ e.val.2 = 2) : e ∉ T := by
      intro heT
      have h0 := hT.2 0
      have h2 := hT.2 2
      change edgeDegree T 0 ≤ 1 at h0
      change edgeDegree T 2 ≤ 1 at h2
      have hcard : ({t13_e02,e} : Finset (Edge 4)).card = 2 := by simp [Ne.symm he]
      simp only [t13_e02] at hcard
      have hsub : ({t13_e02,e} : Finset (Edge 4)) ⊆ T := by
        intro a ha
        rcases Finset.mem_insert.mp ha with ha | ha
        · exact ha ▸ h02
        · exact (Finset.mem_singleton.mp ha) ▸ heT
      have hc (i : Fin 4) : edgeDegree {t13_e02,e} i ≤ edgeDegree T i :=
        Finset.card_le_card (Finset.filter_subset_filter _ hsub)
      rcases hi with hi | hi | hi | hi
      · have hh := hc 0
        norm_num [edgeDegree,matchingWitness,Finset.filter_insert,Finset.filter_singleton,t13_e02,hi,he,Ne.symm he] at hh
        try simp only [hcard] at hh
        unfold edgeDegree at h0
        omega
      · have hh := hc 0
        norm_num [edgeDegree,matchingWitness,Finset.filter_insert,Finset.filter_singleton,t13_e02,hi,he,Ne.symm he] at hh
        try simp only [hcard] at hh
        unfold edgeDegree at h0
        omega
      · have hh := hc 2
        norm_num [edgeDegree,matchingWitness,Finset.filter_insert,Finset.filter_singleton,t13_e02,hi,he,Ne.symm he] at hh
        try simp only [hcard] at hh
        unfold edgeDegree at h2
        omega
      · have hh := hc 2
        norm_num [edgeDegree,matchingWitness,Finset.filter_insert,Finset.filter_singleton,t13_e02,hi,he,Ne.symm he] at hh
        try simp only [hcard] at hh
        unfold edgeDegree at h2
        omega
    have h01 := hnot t13_e01 (by decide) (by simp [t13_e01])
    have h03 := hnot t13_e03 (by decide) (by simp [t13_e03])
    have h12 := hnot t13_e12 (by decide) (by simp [t13_e12])
    have h23 := hnot t13_e23 (by decide) (by simp [t13_e23])
    rw [hobj,if_pos h02,if_neg h01,if_neg h03,if_neg h12,if_neg h23]
    split_ifs <;> norm_num

/-- The standard matching dual bound, proved here for the tagged gadget type.
Every endpoint is charged at most once. -/
private lemma t13_matching_potential {n : ℕ} {P : DegreeProblem n}
    (c : GadgetVertex P → ℤ) (hc : ∀ v, 0 ≤ c v)
    (hedge : ∀ e : GadgetEdge P, gadgetWeight e ≤ c (gadgetEnds e).1+c (gadgetEnds e).2)
    (J : Finset (GadgetEdge P)) (hJ : IsMatching J) :
    (∑ e ∈ J, gadgetWeight e) ≤ ∑ v, c v := by
  let ends : GadgetEdge P → Finset (GadgetVertex P) :=
    fun e => {(gadgetEnds e).1,(gadgetEnds e).2}
  have hne (e : GadgetEdge P) : (gadgetEnds e).1 ≠ (gadgetEnds e).2 := by
    cases e <;> simp [gadgetEnds]
  have hdisj : Set.PairwiseDisjoint (↑J) ends := by
    intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have hh := hJ e he f hf hef
    simp only [ends,Finset.mem_insert,Finset.mem_singleton] at hv hw
    rcases hv with hv | hv <;> rcases hw with hw | hw
    · exact hh.1 (hv.symm.trans hw)
    · exact hh.2.1 (hv.symm.trans hw)
    · exact hh.2.2.1 (hv.symm.trans hw)
    · exact hh.2.2.2 (hv.symm.trans hw)
  calc
    _ ≤ ∑ e ∈ J, (c (gadgetEnds e).1+c (gadgetEnds e).2) :=
      Finset.sum_le_sum (fun e _ => hedge e)
    _ = ∑ e ∈ J, ∑ v ∈ ends e, c v := by
      apply Finset.sum_congr rfl
      intro e he
      simp [ends,hne e]
    _ = ∑ v ∈ J.biUnion ends, c v := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ v, c v := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ => hc v)

/-- Slots cost zero. Positive optional edges get three extra units at an
available endpoint and three fewer at a saturated endpoint. -/
private def t13_potential (second : Bool) : GadgetVertex (matchingWitness second) → ℤ
  | .inl _ => 0
  | .inr (e,side) =>
      if integerWeight (matchingWitness second) e.val > 0 then
        if remainingCap (matchingWitness second) (endpoint e.val side) = 0 then 17 else 23
      else 20

private lemma t13_potential_nonneg (second : Bool)
    (v : GadgetVertex (matchingWitness second)) : 0 ≤ t13_potential second v := by
  cases v with
  | inl v => exact le_rfl
  | inr v => rcases v with ⟨e,side⟩; dsimp [t13_potential]; split_ifs <;> norm_num

private lemma t13_potential_edge (second : Bool) (g : GadgetEdge (matchingWitness second)) :
    gadgetWeight g ≤ t13_potential second (gadgetEnds g).1+
      t13_potential second (gadgetEnds g).2 := by
  cases g with
  | internal e =>
    rcases e with ⟨e,he⟩
    cases second
    · rw [t13_optional_false] at he
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl <;>
        simp only [gadgetWeight,gadgetEnds,t13_potential,t13_M,integerWeight,t13_L]
      all_goals norm_num [remainingCap,edgeDegree,Finset.filter_insert,Finset.filter_singleton,
          t13_caps_false,endpoint,matchingWitness,t13_e01,t13_e03,t13_e12,t13_e13]
    · rw [t13_optional_true] at he
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl <;>
        simp only [gadgetWeight,gadgetEnds,t13_potential,t13_M,integerWeight,t13_L]
      all_goals norm_num [remainingCap,edgeDegree,Finset.filter_insert,Finset.filter_singleton,
          t13_caps_true,endpoint,matchingWitness,t13_e01,t13_e03,t13_e12,t13_e13,t13_e23]
  | external e side slot =>
    rcases e with ⟨e,he⟩
    have hs := slot.isLt
    cases second
    · rw [t13_optional_false] at he
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl <;> cases side <;>
        simp only [gadgetWeight,gadgetEnds,t13_potential,t13_M,integerWeight,t13_L]
      all_goals norm_num [remainingCap,edgeDegree,Finset.filter_insert,Finset.filter_singleton,
          t13_caps_false,endpoint,matchingWitness,t13_e01,t13_e03,t13_e12,t13_e13] at hs
      all_goals norm_num [remainingCap,edgeDegree,Finset.filter_insert,Finset.filter_singleton,endpoint,matchingWitness,
        t13_e01,t13_e03,t13_e12,t13_e13,t13_e23]
    · rw [t13_optional_true] at he
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl <;> cases side <;>
        simp only [gadgetWeight,gadgetEnds,t13_potential,t13_M,integerWeight,t13_L]
      all_goals norm_num [remainingCap,edgeDegree,Finset.filter_insert,Finset.filter_singleton,
          t13_caps_true,endpoint,matchingWitness,t13_e01,t13_e03,t13_e12,t13_e13,t13_e23] at hs
      all_goals norm_num [remainingCap,edgeDegree,Finset.filter_insert,Finset.filter_singleton,endpoint,matchingWitness,
        t13_e01,t13_e03,t13_e12,t13_e13,t13_e23]

private lemma t13_potential_total (second : Bool) :
    (∑ v : GadgetVertex (matchingWitness second), t13_potential second v) =
      if second then 200 else 166 := by
  change (∑ v : (Σ i : Fin 4, Fin (remainingCap (matchingWitness second) i)) ⊕
    ({e // e ∈ optionalEdges (matchingWitness second)} × Bool), t13_potential second v) = _
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool]
  simp only [t13_potential,Finset.sum_const_zero,zero_add]
  rw [Finset.sum_coe_sort (optionalEdges (matchingWitness second))
    (fun e : Edge 4 =>
      (if integerWeight (matchingWitness second) e > 0 then
        if remainingCap (matchingWitness second) (endpoint e true) = 0 then 17 else 23 else 20) +
      (if integerWeight (matchingWitness second) e > 0 then
        if remainingCap (matchingWitness second) (endpoint e false) = 0 then 17 else 23 else 20))]
  cases second
  · rw [t13_optional_false]
    simp only [integerWeight,t13_L]
    norm_num [remainingCap,edgeDegree,Finset.filter_insert,Finset.filter_singleton,t13_potential,t13_caps_false,endpoint,
      matchingWitness,t13_e01,t13_e03,t13_e12,t13_e13]
  · rw [t13_optional_true]
    simp only [integerWeight,t13_L]
    norm_num [remainingCap,edgeDegree,Finset.filter_insert,Finset.filter_singleton,t13_potential,t13_caps_true,endpoint,
      matchingWitness,t13_e01,t13_e03,t13_e12,t13_e13,t13_e23]

private def t13_opt01 (second : Bool) : {e // e ∈ optionalEdges (matchingWitness second)} :=
  ⟨t13_e01, by cases second <;> simp [t13_optional_false,t13_optional_true]⟩
private def t13_opt03 (second : Bool) : {e // e ∈ optionalEdges (matchingWitness second)} :=
  ⟨t13_e03, by cases second <;> simp [t13_optional_false,t13_optional_true]⟩
private def t13_opt12 (second : Bool) : {e // e ∈ optionalEdges (matchingWitness second)} :=
  ⟨t13_e12, by cases second <;> simp [t13_optional_false,t13_optional_true]⟩
private def t13_opt13 (second : Bool) : {e // e ∈ optionalEdges (matchingWitness second)} :=
  ⟨t13_e13, by cases second <;> simp [t13_optional_false,t13_optional_true]⟩
private def t13_opt23 : {e // e ∈ optionalEdges (matchingWitness true)} :=
  ⟨t13_e23, by simp [t13_optional_true]⟩

private def t13_Jfalse : Finset (GadgetEdge (matchingWitness false)) :=
  { .external (t13_opt01 false) false ⟨0, by norm_num [endpoint,t13_opt01,t13_e01,t13_caps_false]⟩,
    .external (t13_opt01 false) true ⟨0, by norm_num [endpoint,t13_opt01,t13_e01,t13_caps_false]⟩,
    .internal (t13_opt03 false), .internal (t13_opt12 false), .internal (t13_opt13 false) }

private def t13_Jtrue : Finset (GadgetEdge (matchingWitness true)) :=
  { .internal (t13_opt01 true), .internal (t13_opt03 true), .internal (t13_opt12 true),
    .internal (t13_opt13 true), .internal t13_opt23 }

private lemma t13_Jfalse_matching : IsMatching t13_Jfalse := by
  intro e he f hf hef
  simp only [t13_Jfalse,Finset.mem_insert,Finset.mem_singleton] at he hf
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
    rcases hf with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [gadgetEnds,t13_opt01,t13_opt03,t13_opt12,t13_opt13,
      endpoint,t13_e01,t13_e03,t13_e12,t13_e13]

private lemma t13_Jtrue_matching : IsMatching t13_Jtrue := by
  intro e he f hf hef
  simp only [t13_Jtrue,Finset.mem_insert,Finset.mem_singleton] at he hf
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
    rcases hf with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [gadgetEnds,t13_opt01,t13_opt03,t13_opt12,t13_opt13,t13_opt23,
      t13_e01,t13_e03,t13_e12,t13_e13,t13_e23]

private lemma t13_Jfalse_weight : (∑ e ∈ t13_Jfalse, gadgetWeight e) = 166 := by
  simp only [t13_Jfalse]
  simp only [gadgetWeight,t13_M,integerWeight,t13_L]
  norm_num [matchingWitness,
    t13_opt01,t13_opt03,t13_opt12,t13_opt13,t13_e01,t13_e03,t13_e12,t13_e13]

private lemma t13_Jtrue_weight : (∑ e ∈ t13_Jtrue, gadgetWeight e) = 200 := by
  simp only [t13_Jtrue]
  simp only [gadgetWeight,t13_M,integerWeight,t13_L]
  norm_num [matchingWitness,
    t13_opt01,t13_opt03,t13_opt12,t13_opt13,t13_opt23,t13_e01,t13_e03,t13_e12,t13_e13,t13_e23]

theorem matching_exact_instances_proof :
    (∀ i, remainingCap (matchingWitness false) i = (![1,1,0,2] : Fin 4 → ℕ) i) ∧
    (∀ i, remainingCap (matchingWitness true) i = (![0,1,0,1] : Fin 4 → ℕ) i) ∧
    (∀ second, denominatorLCM (matchingWitness second)=4 ∧ gadgetM (matchingWitness second)=10) ∧
    (optionalEdges (matchingWitness false)).card=4 ∧
    (optionalEdges (matchingWitness true)).card=5 ∧
    (∀ second, EdgeFeasible (matchingWitness second) (matchingWitnessSolution second) ∧
      edgeObjective (matchingWitness second) (matchingWitnessSolution second) =
        (if second then -3/4 else 3/4) ∧
      (∀ T, EdgeFeasible (matchingWitness second) T →
        edgeObjective (matchingWitness second) T ≤
          edgeObjective (matchingWitness second) (matchingWitnessSolution second))) ∧
    (∀ second, ∃ J : Finset (GadgetEdge (matchingWitness second)), IsMatching J ∧
      (∑ e ∈ J, gadgetWeight e) = (if second then 200 else 166) ∧
      (∀ J' : Finset (GadgetEdge (matchingWitness second)), IsMatching J' →
        (∑ e ∈ J', gadgetWeight e) ≤ ∑ e ∈ J, gadgetWeight e)) := by
  refine ⟨t13_caps_false, t13_caps_true, (fun s => ⟨t13_L s,t13_M s⟩), ?_, ?_, ?_, ?_⟩
  · rw [t13_optional_false]
    norm_num [t13_e01,t13_e03,t13_e12,t13_e13]
  · rw [t13_optional_true]
    norm_num [t13_e01,t13_e03,t13_e12,t13_e13,t13_e23]
  · intro second
    exact ⟨(t13_graph_value second).1,(t13_graph_value second).2,t13_graph_upper second⟩
  · intro second
    have hu (J : Finset (GadgetEdge (matchingWitness second))) (hJ : IsMatching J) :
        (∑ e ∈ J, gadgetWeight e) ≤ if second then 200 else 166 := by
      rw [← t13_potential_total second]
      exact t13_matching_potential (t13_potential second) (t13_potential_nonneg second)
        (t13_potential_edge second) J hJ
    cases second
    · exact ⟨t13_Jfalse,t13_Jfalse_matching,t13_Jfalse_weight,
        fun J hJ => by rw [t13_Jfalse_weight]; exact hu J hJ⟩
    · exact ⟨t13_Jtrue,t13_Jtrue_matching,t13_Jtrue_weight,
        fun J hJ => by rw [t13_Jtrue_weight]; exact hu J hJ⟩

/- P011-T6: actual spectral clipping on independent cycle blocks. -/
private lemma t6_blockIndex (m : ℕ) (b : Fin m) (r : Fin 4) :
    blockIndex (by decide) (StarCompletion.blockEquiv 4 m (b,r)) = b := by
  apply Fin.ext
  exact StarCompletion.block_quot (by decide) (b,r)

private def t6_lift (m : ℕ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin (4*m)) (Fin (4*m)) ℝ := fun i j =>
  if blockIndex (by decide) i = blockIndex (by decide) j then
    M (localIndex (by decide) i) (localIndex (by decide) j) else 0

private lemma t6_lift_apply (m : ℕ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (b c : Fin m) (r s : Fin 4) :
    t6_lift m M (StarCompletion.blockEquiv 4 m (b,r))
      (StarCompletion.blockEquiv 4 m (c,s)) = if b=c then M r s else 0 := by
  simp [t6_lift,t6_blockIndex,StarCompletion.block_local]

private lemma t6_lift_sub (m : ℕ) (M N : Matrix (Fin 4) (Fin 4) ℝ) :
    t6_lift m (M-N) = t6_lift m M-t6_lift m N := by
  ext i j
  simp only [t6_lift,Matrix.sub_apply]
  split_ifs <;> ring

private lemma t6_lift_zero (m : ℕ) : t6_lift m 0 = 0 := by
  ext i j
  simp [t6_lift]

private lemma t6_lift_mul (m : ℕ) (M N : Matrix (Fin 4) (Fin 4) ℝ) :
    t6_lift m M * t6_lift m N = t6_lift m (M*N) := by
  ext i j
  obtain ⟨⟨b,r⟩,rfl⟩ := (StarCompletion.blockEquiv 4 m).surjective i
  obtain ⟨⟨c,s⟩,rfl⟩ := (StarCompletion.blockEquiv 4 m).surjective j
  simp only [Matrix.mul_apply]
  rw [← (StarCompletion.blockEquiv 4 m).sum_comp,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · by_cases h : b=c
    · subst c
      simp [t6_lift_apply,Matrix.mul_apply]
    · simp [t6_lift_apply,h,Matrix.mul_apply]
  · intro d hd hdb
    simp [t6_lift_apply,Ne.symm hdb]
  · simp

private lemma t6_lift_oracle (m : ℕ) :
    t6_lift m (oracleMatrix cycleGraph) =
      oracleMatrix (blockGraph (by decide) cycleGraph m) := by
  ext i j
  obtain ⟨⟨b,r⟩,rfl⟩ := (StarCompletion.blockEquiv 4 m).surjective i
  obtain ⟨⟨c,s⟩,rfl⟩ := (StarCompletion.blockEquiv 4 m).surjective j
  rw [t6_lift_apply]
  by_cases h : b=c
  · subst c
    simp [oracleMatrix,adjacency,blockGraph,StarCompletion.block_local,
      StarCompletion.block_quot,Matrix.one_apply,Equiv.apply_eq_iff_eq]
  · have hv : b.val ≠ c.val := fun he => h (Fin.ext he)
    simp [oracleMatrix,adjacency,blockGraph,StarCompletion.block_local,
      StarCompletion.block_quot,Matrix.one_apply,Equiv.apply_eq_iff_eq,h,hv]

private lemma t6_lift_quadratic (m : ℕ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (x : Fin (4*m) → ℝ) : quadratic (t6_lift m M) x =
      ∑ b : Fin m, quadratic M (fun r => x (StarCompletion.blockEquiv 4 m (b,r))) := by
  have hi (b : Fin m) (r : Fin 4) :
      (∑ j, t6_lift m M (StarCompletion.blockEquiv 4 m (b,r)) j *
        x (StarCompletion.blockEquiv 4 m (b,r))*x j) =
      ∑ s : Fin 4, M r s*x (StarCompletion.blockEquiv 4 m (b,r))*
        x (StarCompletion.blockEquiv 4 m (b,s)) := by
    rw [← (StarCompletion.blockEquiv 4 m).sum_comp,Fintype.sum_prod_type]
    rw [Finset.sum_eq_single b]
    · simp [t6_lift_apply]
    · intro c hc hcb
      simp [t6_lift_apply,Ne.symm hcb]
    · simp
  unfold quadratic
  rw [← (StarCompletion.blockEquiv 4 m).sum_comp,Fintype.sum_prod_type]
  simp_rw [hi]

private lemma t6_lift_psd (m : ℕ) (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : PSD M) :
    PSD (t6_lift m M) := by
  constructor
  · intro i j
    dsimp [t6_lift]
    by_cases h : blockIndex (by decide) i = blockIndex (by decide) j
    · simp only [h,ite_true,eq_self_iff_true]
      exact hM.1 _ _
    · simp [h,Ne.symm h]
  · intro x
    rw [t6_lift_quadratic]
    exact Finset.sum_nonneg (fun b _ => hM.2 _)

private lemma t6_clipped_orthogonal :
    cycleClipped*(cycleClipped-oracleMatrix cycleGraph) = 0 := by
  rw [SpectralConfidence.cycle_clipped_eq_positive_part]
  exact SpectralConfidence.positive_part_orthogonal _ (SpectralConfidence.oracle_hermitian _)

private lemma t6_positive_part (m : ℕ) :
    positivePart (oracleMatrix (blockGraph (by decide) cycleGraph m)) =
      t6_lift m cycleClipped := by
  have hC : PSD cycleClipped := by
    rw [SpectralConfidence.cycle_clipped_eq_positive_part]
    exact positive_part_psd _
  have hN : PSD (cycleClipped-oracleMatrix cycleGraph) := by
    rw [SpectralConfidence.cycle_clipped_eq_positive_part]
    exact SpectralConfidence.positive_part_majorant _ (SpectralConfidence.oracle_hermitian _)
  symm
  apply SpectralConfidence.positive_part_of_orthogonal_decomposition _ _
    (SpectralConfidence.oracle_hermitian _)
  · exact t6_lift_psd m _ hC
  · rw [← t6_lift_oracle,← t6_lift_sub]
    exact t6_lift_psd m _ hN
  · rw [← t6_lift_oracle,← t6_lift_sub,t6_lift_mul,t6_clipped_orthogonal,t6_lift_zero]

private lemma t6_center_block (x : Fin 4 → ℝ) (a : ℝ) :
    quadratic cycleClipped (fun r => x r-a) =
      quadratic cycleClipped x-6*a*(∑ r, x r)+12*a^2 := by
  norm_num [quadratic,cycle_clipped_entries,cycleEigenvectors,Fin.sum_univ_succ]
  <;> ring

private def t6_raw (m : ℕ) (y : Fin (4*m) → ℝ) : ℝ :=
  (∑ b : Fin m, quadratic cycleClipped
    (fun r => y (StarCompletion.blockEquiv 4 m (b,r)))) / (4*m : ℝ)

private lemma t6_scaled_identity (m : ℕ) (hm : 0 < m) (y : Fin (4*m) → ℝ) :
    (4*m : ℝ)*VPositive (cycleModel (3/2) m).G (weighted (cycleModel (3/2) m) y) =
      t6_raw m y-3*(betaHat (cycleModel (3/2) m) y)^2 := by
  have hn0 : (4*m : ℝ) ≠ 0 := by positivity
  have hw : weighted (cycleModel (3/2) m) y = y := by
    funext i
    simp [weighted,cycleModel]
  have hsum : (∑ b : Fin m, ∑ r : Fin 4, y (StarCompletion.blockEquiv 4 m (b,r))) =
      ∑ i, y i := by
    rw [← (StarCompletion.blockEquiv 4 m).sum_comp,Fintype.sum_prod_type]
  have hbeta : betaHat (cycleModel (3/2) m) y = average y := by
    change average (fun i => 1*y i) = average y
    simp
  rw [hw,hbeta]
  change (4*m : ℝ)*
    (quadratic (positivePart (oracleMatrix (blockGraph (by decide) cycleGraph m))) (centered y) /
      ((4*m : ℕ) : ℝ)^2) = _
  push_cast
  rw [t6_positive_part,t6_lift_quadratic]
  simp only [centered]
  simp_rw [t6_center_block]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [hsum]
  change _ = t6_raw m y-3*(average y)^2
  dsimp [t6_raw,average]
  push_cast
  field_simp
  <;> ring

private def t6_bits : (Fin 4 → Bool) ≃ Bool × Bool × Bool × Bool where
  toFun u := (u 0,u 1,u 2,u 3)
  invFun v := ![v.1,v.2.1,v.2.2.1,v.2.2.2]
  left_inv u := by funext r; fin_cases r <;> rfl
  right_inv v := by rcases v with ⟨b0,b1,b2,b3⟩; rfl

private def t6_q (u : Fin 4 → Bool) : ℝ :=
  quadratic cycleClipped (cycleBlock (3/2) (fun r => sign (u r)))
private def t6_s (u : Fin 4 → Bool) : ℝ :=
  ∑ r, cycleBlock (3/2) (fun r => sign (u r)) r

private lemma t6_q_mean : (∑ u : Fin 4 → Bool, t6_q u)/16 = 16 := by
  rw [← t6_bits.symm.sum_comp]
  norm_num [t6_bits,t6_q,quadratic,cycle_clipped_entries,cycleEigenvectors,cycleBlock,sign,
    Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_succ]

private lemma t6_q_var : (∑ u : Fin 4 → Bool, (t6_q u-16)^2)/16 = 176 := by
  rw [← t6_bits.symm.sum_comp]
  norm_num [t6_bits,t6_q,quadratic,cycle_clipped_entries,cycleEigenvectors,cycleBlock,sign,
    Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_succ]

private lemma t6_s_mean : (∑ u : Fin 4 → Bool, t6_s u)/16 = 0 := by
  rw [← t6_bits.symm.sum_comp]
  norm_num [t6_bits,t6_s,cycleBlock,sign,Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_succ]

private lemma t6_s_var : (∑ u : Fin 4 → Bool, (t6_s u-0)^2)/16 = 16 := by
  rw [← t6_bits.symm.sum_comp]
  norm_num [t6_bits,t6_s,cycleBlock,sign,Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_succ]

/-- A scalar statistic of each independent four-sign block. -/
private def t6_aux (f : (Fin 4 → Bool) → ℝ) (m : ℕ) : Model m where
  law := uniformLaw (fun u : Fin m → Fin 4 → Bool => fun b => f (u b))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := emptyGraph m
  R := emptyGraph m
  d := fun _ => 0

private lemma t6_aux_moments (f : (Fin 4 → Bool) → ℝ) (a v : ℝ)
    (hmean : (∑ u : Fin 4 → Bool, f u)/16 = a)
    (hvar : (∑ u : Fin 4 → Bool, (f u-a)^2)/16 = v)
    (m : ℕ) (hm : 0 < m) :
    (∫ z, average z ∂(t6_aux f m).law) = a ∧
    (∫ z, (average z-a)^2 ∂(t6_aux f m).law) = v/(m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hh := NewFiniteCompletion.coordinate_moments hm (t6_aux f m) (Fin 4 → Bool)
    (fun _ u => f u) rfl (fun _ => rfl) rfl (fun _ => a) v
    (fun _ => by simpa using hmean) (fun _ => by simpa using hvar)
  have hb : betaHat (t6_aux f m) = (average : (Fin m → ℝ) → ℝ) := by
    funext z
    change average (fun i => 1*z i) = average z
    simp
  have ha : average (fun _ : Fin m => a) = a := by
    simp [average]
    field_simp
  have hmean' : (∫ z, average z ∂(t6_aux f m).law) = a := by
    simpa only [beta,expectation,hb,ha] using hh.2.1
  refine ⟨hmean', ?_⟩
  have hv : (m : ℝ)*(∫ z, (average z-a)^2 ∂(t6_aux f m).law) = v := by
    simpa only [var,expectation,hb,hmean'] using hh.2.2
  apply (eq_div_iff hm0).mpr
  nlinarith

/-- Equality of integrals through two finite pushforwards with the same source.
This uses only the proved finite-law bridge, including when the maps collide. -/
private lemma t6_integral_transfer {A : Type} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] {n m : ℕ}
    (f : A → Fin n → ℝ) (g : A → Fin m → ℝ)
    (p : (Fin n → ℝ) → ℝ) (q : (Fin m → ℝ) → ℝ)
    (hp : Measurable p) (hq : Measurable q) (he : ∀ u, p (f u) = q (g u)) :
    (∫ y, p y ∂uniformLaw f) = ∫ z, q z ∂uniformLaw g := by
  rw [uniform_integral f (measurable_of_finite _) p hp,
    uniform_integral g (measurable_of_finite _) q hq]
  congr 1
  exact Finset.sum_congr rfl (fun u _ => he u)

private def t6_source (m : ℕ) (u : Fin m → Fin 4 → Bool) : Fin (4*m) → ℝ := fun i =>
  cycleBlock (3/2) (fun r => sign (u (blockIndex (by decide) i) r)) (localIndex (by decide) i)

private lemma t6_source_apply (m : ℕ) (u : Fin m → Fin 4 → Bool)
    (b : Fin m) (r : Fin 4) :
    t6_source m u (StarCompletion.blockEquiv 4 m (b,r)) =
      cycleBlock (3/2) (fun s => sign (u b s)) r := by
  simp [t6_source,t6_blockIndex,StarCompletion.block_local]

private lemma t6_raw_source (m : ℕ) (u : Fin m → Fin 4 → Bool) :
    t6_raw m (t6_source m u) = average (fun b => t6_q (u b))/4 := by
  dsimp [t6_raw]
  simp_rw [t6_source_apply]
  dsimp [average,t6_q]
  push_cast
  simp only [div_mul_eq_div_div]
  ring

private lemma t6_beta_source (m : ℕ) (u : Fin m → Fin 4 → Bool) :
    betaHat (cycleModel (3/2) m) (t6_source m u) = average (fun b => t6_s (u b))/4 := by
  have hw : weighted (cycleModel (3/2) m) (t6_source m u) = t6_source m u := by
    funext i
    simp [weighted,cycleModel]
  rw [betaHat,hw]
  unfold average
  rw [← (StarCompletion.blockEquiv 4 m).sum_comp,Fintype.sum_prod_type]
  simp_rw [t6_source_apply]
  dsimp [t6_s]
  push_cast
  simp only [div_mul_eq_div_div]
  ring

private lemma t6_raw_push (m : ℕ) (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ y, g (t6_raw m y) ∂(cycleModel (3/2) m).law) =
      ∫ z, g (average z/4) ∂(t6_aux t6_q m).law := by
  apply t6_integral_transfer (t6_source m) (fun u b => t6_q (u b))
    (fun y => g (t6_raw m y)) (fun z => g (average z/4))
    (hg.comp (by unfold t6_raw quadratic; fun_prop))
    (hg.comp (by unfold average; fun_prop))
  intro u
  rw [t6_raw_source]

private lemma t6_beta_push (m : ℕ) (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ y, g (betaHat (cycleModel (3/2) m) y) ∂(cycleModel (3/2) m).law) =
      ∫ z, g (average z/4) ∂(t6_aux t6_s m).law := by
  apply t6_integral_transfer (t6_source m) (fun u b => t6_s (u b))
    (fun y => g (betaHat (cycleModel (3/2) m) y)) (fun z => g (average z/4))
    (hg.comp (ProbabilityCompletion.betaHat_measurable _))
    (hg.comp (by unfold average; fun_prop))
  intro u
  rw [t6_beta_source]

private lemma t6_moments (m : ℕ) (hm : 0 < m) :
    expectation (cycleModel (3/2) m) (t6_raw m) = 4 ∧
    var (cycleModel (3/2) m) (t6_raw m) = 11/(m : ℝ) ∧
    beta (cycleModel (3/2) m) = 0 ∧
    var (cycleModel (3/2) m) (betaHat (cycleModel (3/2) m)) = 1/(m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hq := t6_aux_moments t6_q 16 176 t6_q_mean t6_q_var m hm
  have hs := t6_aux_moments t6_s 0 16 t6_s_mean t6_s_var m hm
  have hmeanQ : expectation (cycleModel (3/2) m) (t6_raw m) = 4 := by
    change (∫ y, (fun x : ℝ => x) (t6_raw m y) ∂(cycleModel (3/2) m).law) = 4
    rw [t6_raw_push m (fun x => x) measurable_id,integral_div,hq.1]
    norm_num
  have hmeanS : beta (cycleModel (3/2) m) = 0 := by
    change (∫ y, (fun x : ℝ => x) (betaHat (cycleModel (3/2) m) y)
      ∂(cycleModel (3/2) m).law) = 0
    rw [t6_beta_push m (fun x => x) measurable_id,integral_div,hs.1]
    norm_num
  refine ⟨hmeanQ, ?_, hmeanS, ?_⟩
  · unfold var
    rw [hmeanQ]
    change (∫ y, (fun x : ℝ => (x-4)^2) (t6_raw m y) ∂(cycleModel (3/2) m).law) = _
    rw [t6_raw_push m (fun x => (x-4)^2) (by fun_prop)]
    have he : (fun z : Fin m → ℝ => (average z/4-4)^2) =
        (fun z => (average z-16)^2/16) := by funext z; ring
    rw [he,integral_div,hq.2]
    field_simp
    <;> ring
  · change expectation (cycleModel (3/2) m)
      (fun y => (betaHat (cycleModel (3/2) m) y-beta (cycleModel (3/2) m))^2) = _
    rw [hmeanS]
    change (∫ y, (fun x : ℝ => (x-0)^2) (betaHat (cycleModel (3/2) m) y)
      ∂(cycleModel (3/2) m).law) = _
    rw [t6_beta_push m (fun x => (x-0)^2) (by fun_prop)]
    have he : (fun z : Fin m → ℝ => (average z/4-0)^2) =
        (fun z => (average z-0)^2/16) := by funext z; ring
    rw [he,integral_div,hs.2]
    field_simp
    <;> ring

private lemma t6_expected (m : ℕ) (hm : 0 < m) :
    expectation (cycleModel (3/2) m)
      (fun y => (4*m : ℝ)*VPositive (cycleModel (3/2) m).G
        (weighted (cycleModel (3/2) m) y)) = 4-12/(4*m : ℝ) := by
  let : IsProbabilityMeasure (uniformLaw (t6_source m)) := by unfold uniformLaw; infer_instance
  have hmom := t6_moments m hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hraw : Integrable (t6_raw m) (cycleModel (3/2) m).law :=
    (NewFiniteCompletion.finite_memLp (t6_source m) (t6_raw m)
      (by unfold t6_raw quadratic; fun_prop) 1).integrable (by norm_num)
  have hsq : Integrable (fun y => betaHat (cycleModel (3/2) m) y^2)
      (cycleModel (3/2) m).law :=
    (NewFiniteCompletion.finite_memLp (t6_source m) _
      ((ProbabilityCompletion.betaHat_measurable _).pow_const 2) 1).integrable (by norm_num)
  have hs : expectation (cycleModel (3/2) m)
      (fun y => betaHat (cycleModel (3/2) m) y^2) = 1/(m : ℝ) := by
    have hv := hmom.2.2.2
    change expectation (cycleModel (3/2) m)
      (fun y => (betaHat (cycleModel (3/2) m) y-beta (cycleModel (3/2) m))^2) = _ at hv
    simpa only [hmom.2.2.1,sub_zero] using hv
  unfold expectation
  simp_rw [t6_scaled_identity m hm]
  rw [integral_sub hraw (hsq.const_mul 3),integral_const_mul]
  change expectation (cycleModel (3/2) m) (t6_raw m)-
    3*expectation (cycleModel (3/2) m) (fun y => betaHat (cycleModel (3/2) m) y^2) = _
  rw [hmom.1,hs]
  field_simp
  <;> ring

private lemma t6_limit : InProbability (cycleFamily (3/2))
    (fun k y => ((cycleFamily (3/2)).size k : ℝ)*VPositive ((cycleFamily (3/2)).model k).G
      (weighted ((cycleFamily (3/2)).model k) y)) (fun _ => 4) := by
  let μ := fun k => (cycleModel (3/2) (k+1)).law
  let (k : ℕ) : IsProbabilityMeasure (μ k) := (cycleModel (3/2) (k+1)).probability
  have hN : Tendsto (fun k : ℕ => (k+1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop).comp
        (show Tendsto (fun k : ℕ => k+1) atTop atTop from
          tendsto_atTop_mono (fun k => Nat.le_succ k) tendsto_id)
  have hrawMeas (k : ℕ) : Measurable (t6_raw (k+1)) := by
    unfold t6_raw quadratic
    fun_prop
  have hrawL2 (k : ℕ) : MemLp (t6_raw (k+1)) 2 (μ k) :=
    NewFiniteCompletion.finite_memLp (t6_source (k+1)) _ (hrawMeas k) 2
  have hbetaL2 (k : ℕ) : MemLp (betaHat (cycleModel (3/2) (k+1))) 2 (μ k) :=
    NewFiniteCompletion.finite_memLp (t6_source (k+1)) _
      (ProbabilityCompletion.betaHat_measurable _) 2
  have hrawMean (k : ℕ) : (∫ y, t6_raw (k+1) y ∂μ k) = 4 :=
    (t6_moments (k+1) (by omega)).1
  have hbetaMean (k : ℕ) : (∫ y, betaHat (cycleModel (3/2) (k+1)) y ∂μ k) = 0 :=
    (t6_moments (k+1) (by omega)).2.2.1
  have hrawVar (k : ℕ) : ProbabilityTheory.variance (t6_raw (k+1)) (μ k) = 11/(k+1 : ℝ) := by
    rw [ProbabilityTheory.variance_eq_integral (hrawMeas k).aemeasurable]
    simpa only [var,expectation,μ,Nat.cast_add,Nat.cast_one] using (t6_moments (k+1) (by omega)).2.1
  have hbetaVar (k : ℕ) : ProbabilityTheory.variance
      (betaHat (cycleModel (3/2) (k+1))) (μ k) = 1/(k+1 : ℝ) := by
    rw [ProbabilityTheory.variance_eq_integral
      (ProbabilityCompletion.betaHat_measurable _).aemeasurable]
    simpa only [var,expectation,μ,Nat.cast_add,Nat.cast_one] using (t6_moments (k+1) (by omega)).2.2.2
  have hrawCP : CoverageCompletion.RowCP μ (fun k => t6_raw (k+1)) 4 := by
    have hh := OracleCompletion.rowCP_of_variance μ _ hrawL2
      (by simpa only [hrawVar] using hN.const_div_atTop 11)
    intro ε hε
    simpa only [hrawMean] using hh ε hε
  have hbetaCP : CoverageCompletion.RowCP μ
      (fun k => betaHat (cycleModel (3/2) (k+1))) 0 := by
    have hh := OracleCompletion.rowCP_of_variance μ _ hbetaL2
      (by simpa only [hbetaVar] using hN.const_div_atTop 1)
    intro ε hε
    simpa only [hbetaMean] using hh ε hε
  have hfinal := CoverageCompletion.rowCP_continuous_pair μ _ _ 4 0 hrawCP hbetaCP
    (fun p : ℝ × ℝ => p.1-3*p.2^2) (by fun_prop)
  intro ε hε
  convert hfinal ε hε using 1
  funext k
  apply congrArg (fun E => (μ k).real E)
  ext y
  change Fin (4*(k+1)) → ℝ at y
  change (ε < |((4*(k+1) : ℕ) : ℝ)*VPositive (cycleModel (3/2) (k+1)).G
    (weighted (cycleModel (3/2) (k+1)) y)-4|) ↔ _
  have hid := t6_scaled_identity (k+1) (by omega) y
  norm_num only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] at hid ⊢
  rw [hid]
  simp only [Set.mem_setOf_eq,Prod.fst,Prod.snd]
  norm_num
  rfl

theorem positive_part_cycle_claims_proof :
    PSD (oracleMatrix cycleGraph + cycleMajorantDifference) ∧ PSD cycleMajorantDifference ∧
    quadratic (oracleMatrix cycleGraph + cycleMajorantDifference) (![0,1,-1,0] : Fin 4 → ℝ) = 3/5 ∧
    quadratic (positivePart (oracleMatrix cycleGraph)) (![0,1,-1,0] : Fin 4 → ℝ) = 1 ∧
    (∀ k, expectation ((cycleFamily (3/2)).model k)
      (fun y => ((cycleFamily (3/2)).size k : ℝ)*VPositive ((cycleFamily (3/2)).model k).G
        (weighted ((cycleFamily (3/2)).model k) y)) = 4-12/((cycleFamily (3/2)).size k : ℝ)) ∧
    InProbability (cycleFamily (3/2))
      (fun k y => ((cycleFamily (3/2)).size k : ℝ)*VPositive ((cycleFamily (3/2)).model k).G
        (weighted ((cycleFamily (3/2)).model k) y)) (fun _ => 4) := by
  refine ⟨cycle_majorant_certificate.2.1,cycle_majorant_certificate.1,
    cycle_majorant_certificate.2.2.1,SpectralConfidence.cycle_actual_positive_value,?_,t6_limit⟩
  intro k
  simpa only [cycleFamily,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using
    t6_expected (k+1) (by omega)

end
end AronowAudit.P011.Wave1
