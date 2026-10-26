import AronowAudit.P001.P001_Foundations

namespace AronowAudit.P001.Wave1
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The canonical independent uniform draw law retains entire sampled blocks. -/
theorem canonical_block_bootstrap_law {l m : ℕ} (hl : 0 < l) {E : Type*}
    (X : Fin l → Fin m → E) :
  letI : NeZero l := ⟨Nat.ne_of_gt hl⟩
  let ρ := Measure.pi (fun _ : Fin l => (PMF.uniformOfFintype (Fin l)).toMeasure)
  IsProbabilityMeasure ρ ∧
  iIndepFun (fun i (a : Fin l → Fin l) => a i) ρ ∧
  (∀ i j, prob ρ {a | a i = j} = 1 / (l : ℝ)) ∧
  (∀ a : Fin l → Fin l, prob ρ {b | b = a} = (1 / (l : ℝ))^l) ∧
  Fintype.card (Fin l × Fin m) = l * m ∧
  (∀ a i j, blockResample X a i j = X (a i) j) := by
  classical
  haveI instNonzero : NeZero l := ⟨Nat.ne_of_gt hl⟩
  let U := (PMF.uniformOfFintype (Fin l)).toMeasure
  let ρ := Measure.pi (fun _ : Fin l => U)
  have hi : iIndepFun (fun i (a : Fin l → Fin l) => a i) ρ :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hu (i j : Fin l) : prob ρ {a | a i = j} = 1 / (l : ℝ) := by
    unfold prob
    change (ρ ((fun a : Fin l → Fin l => a i) ⁻¹' {j})).toReal = _
    rw [← Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton j)]
    rw [(measurePreserving_eval (fun _ : Fin l => U) i).map_eq]
    dsimp [U]
    rw [PMF.toMeasure_uniformOfFintype_apply {j} (measurableSet_singleton j)]
    simp
  have hb := block_bootstrap_draw_count ρ hl X (fun i a => a i)
    (fun i => measurable_pi_apply i) hi hu
  refine ⟨inferInstance, hi, hu, ?_, hb.1, hb.2.1⟩
  intro a
  convert hb.2.2 a using 2
  ext b
  simp only [Set.mem_setOf_eq]
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

private theorem uniform_apd_probability : IsProbabilityMeasure (uniformLaw 0 1) := by
  constructor
  rw [uniformLaw_zero_one_eq_restrict]
  norm_num

private theorem uniform_apd_pair_measurable :
    Measurable (fun z : ℝ × ℝ => apdExample z.1 z.2) := by
  unfold apdExample
  exact Measurable.ite (measurableSet_le measurable_snd measurable_const)
    measurable_fst.neg (measurable_const.mul measurable_fst)

private theorem uniform_apd_integrable :
    Integrable (fun z : ℝ × ℝ => apdExample z.1 z.2)
      ((uniformLaw 0 1).prod (uniformLaw 0 1)) := by
  classical
  haveI instUniform : IsProbabilityMeasure (uniformLaw 0 1) := uniform_apd_probability
  have h : Integrable (fun x : ℝ => x) (uniformLaw 0 1) := by
    rw [uniformLaw_zero_one_eq_restrict]
    exact continuous_id.continuousOn.integrableOn_Icc
  have hfst := h.comp_fst (uniformLaw 0 1)
  exact Integrable.piecewise (measurableSet_le measurable_snd measurable_const)
    hfst.neg.integrableOn (hfst.const_mul 9).integrableOn

private theorem uniform_apd_partial (x : Fin 2 → ℝ) :
    partialAt (fun x : Fin 2 → ℝ => apdExample (x 0) (x 1)) x 0 =
      deriv (fun t => apdExample t (x 1)) (x 0) := by
  classical
  unfold partialAt
  simp only [Function.update_self, Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  rw [apd_pda_different_correct_coordinate_supporting.1]
  by_cases hx : x 1 ≤ 4/5
  · simp only [apdExample, if_pos hx]
    simpa using (((hasDerivAt_id (0 : ℝ)).const_add (x 0)).neg).deriv
  · simp only [apdExample, if_neg hx]
    simpa using (((hasDerivAt_id (0 : ℝ)).const_add (x 0)).const_mul 9).deriv

/-- The actual product-uniform CEF separates APD from PDA in coordinate zero. -/
theorem uniform_apd_pda_actual_example :
    let ν := (uniformLaw 0 1).prod (uniformLaw 0 1)
    let X : ℝ × ℝ → Fin 2 → ℝ := fun z => ![z.1, z.2]
    let m : (Fin 2 → ℝ) → ℝ := fun x => apdExample (x 0) (x 1)
    let Y : ℝ × ℝ → ℝ := fun z => apdExample z.1 z.2
    IsProbabilityMeasure ν ∧
    IndepFun (fun z : ℝ × ℝ => z.1) (fun z => z.2) ν ∧
    ν.map (fun z : ℝ × ℝ => z.1) = uniformLaw 0 1 ∧
    ν.map (fun z : ℝ × ℝ => z.2) = uniformLaw 0 1 ∧
    IsCEF ν X Y m ∧
    covariateMean ν X = (![1/2, 1/2] : Fin 2 → ℝ) ∧
    mean ν (fun z => partialAt m (X z) 0) = 1 ∧
    predictorPDA ν X m 0 = -1 ∧
    mean ν (fun z => partialAt m (X z) 0) ≠ predictorPDA ν X m 0 := by
  haveI instUniform : IsProbabilityMeasure (uniformLaw 0 1) := uniform_apd_probability
  let ν := (uniformLaw 0 1).prod (uniformLaw 0 1)
  let X : ℝ × ℝ → Fin 2 → ℝ := fun z => ![z.1, z.2]
  let m : (Fin 2 → ℝ) → ℝ := fun x => apdExample (x 0) (x 1)
  have hind : IndepFun (fun z : ℝ × ℝ => z.1) (fun z => z.2) ν :=
    indepFun_prod measurable_id measurable_id
  have hfst : ν.map Prod.fst = uniformLaw 0 1 := by simp [ν]
  have hsnd : ν.map Prod.snd = uniformLaw 0 1 := by simp [ν]
  have hY := uniform_apd_integrable
  have hpair : IsCEF ν (fun z : ℝ × ℝ => (z.1,z.2))
      (fun z => apdExample z.1 z.2) (fun z => apdExample z.1 z.2) :=
    ⟨uniform_apd_pair_measurable, hY, hY, fun _ _ => rfl⟩
  have hv := apd_pda_different_correct_coordinate ν Prod.fst Prod.snd
    (fun z => apdExample z.1 z.2) measurable_fst measurable_snd hY hind hfst hsnd hpair
  have hmean : covariateMean ν X = (![1/2,1/2] : Fin 2 → ℝ) := by
    funext k
    fin_cases k
    · exact hv.2.1
    · exact hv.2.2.1
  have hpartial (x : Fin 2 → ℝ) : partialAt m x 0 =
      deriv (fun t => apdExample t (x 1)) (x 0) := uniform_apd_partial x
  have hapd : mean ν (fun z => partialAt m (X z) 0) = 1 := by
    simp_rw [hpartial]
    exact hv.2.2.2.1
  have hpda : predictorPDA ν X m 0 = -1 := by
    unfold predictorPDA
    rw [hmean, hpartial]
    exact hv.1 _ _ |>.trans (by norm_num)
  refine ⟨inferInstance, hind, hfst, hsnd, ?_, hmean, hapd, hpda, ?_⟩
  · refine ⟨?_,hY,hY,fun _ _ => rfl⟩
    change Measurable (fun x : Fin 2 → ℝ => apdExample (x 0) (x 1))
    unfold apdExample
    exact Measurable.ite (measurableSet_le (measurable_pi_apply 1) measurable_const)
      (measurable_pi_apply 0).neg (measurable_const.mul (measurable_pi_apply 0))
  · rw [hapd,hpda]
    norm_num

private theorem pooled_mle_binary {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (hm : Measurable (fun ω => (X ω,Y ω)))
    (a b c d : ℝ≥0∞)
    (hlaw : μ.map (fun ω => (X ω,Y ω)) = a • Measure.dirac (0,0) +
      b • Measure.dirac (0,1) + c • Measure.dirac (1,0) + d • Measure.dirac (1,1)) :
    ∀ᵐ ω ∂μ, Y ω = 0 ∨ Y ω = 1 := by
  apply (ae_map_iff hm.aemeasurable
    (show MeasurableSet {z : ℝ × ℝ | z.2=0 ∨ z.2=1} from
      (measurable_snd (measurableSet_singleton 0)).union
      (measurable_snd (measurableSet_singleton 1)))).mp
  rw [hlaw]
  simp only [ae_add_measure_iff]
  have h (z : ℝ × ℝ) (hz : z.2=0 ∨ z.2=1) (e : ℝ≥0∞) :
      ∀ᵐ z' ∂e • Measure.dirac z, z'.2=0 ∨ z'.2=1 := by
    apply Measure.ae_smul_measure _ e
    simpa using hz
  exact ⟨⟨⟨h _ (Or.inl rfl) a,h _ (Or.inr rfl) b⟩,
    h _ (Or.inl rfl) c⟩,h _ (Or.inr rfl) d⟩

private theorem pooled_mle_cells {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (hm : Measurable (fun ω => (X ω,Y ω)))
    (a b c d : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) (hc : c ≠ ∞) (hd : d ≠ ∞)
    (hlaw : μ.map (fun ω => (X ω,Y ω)) = a • Measure.dirac (0,0) +
      b • Measure.dirac (0,1) + c • Measure.dirac (1,0) + d • Measure.dirac (1,1)) :
    conditionalMeanAt μ X Y 0 = b.toReal / (a+b).toReal ∧
    conditionalMeanAt μ X Y 1 = d.toReal / (c+d).toReal := by
  classical
  have hi (x : ℝ) : (∫ ω in {ω | X ω=x},Y ω ∂μ) =
      ∫ z, (if z.1=x then z.2 else 0) ∂μ.map (fun ω => (X ω,Y ω)) := by
    have hs : MeasurableSet {ω | X ω=x} :=
      (measurable_fst.comp hm) (measurableSet_singleton x)
    rw [← integral_indicator hs]
    have hmeas : Measurable (fun z : ℝ × ℝ => if z.1=x then z.2 else 0) :=
      Measurable.ite (measurable_fst (measurableSet_singleton x)) measurable_snd measurable_const
    simpa only [Set.indicator_apply,Set.mem_setOf_eq] using
      (integral_map hm.aemeasurable hmeas.aestronglyMeasurable).symm
  have hp (x : ℝ) : μ {ω | X ω=x} =
      (μ.map (fun ω => (X ω,Y ω))) {z | z.1=x} := by
    have hs : MeasurableSet {z : ℝ × ℝ | z.1=x} :=
      measurable_fst (measurableSet_singleton x)
    exact (Measure.map_apply hm hs).symm
  simp only [conditionalMeanAt,prob,hi,hp,hlaw]
  rw [four_atom_integral _ a b c d ha hb hc hd,
    four_atom_integral _ a b c d ha hb hc hd]
  simp [Measure.add_apply,Measure.smul_apply]


/-- The pooled clipped MLE converges in probability to the marginal mean `1/4+q/2`.
For `0 < q < 1`, this limit differs from both conditional cell means. -/
theorem pooled_mle_covariate_marginal_bridge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X Y : ℕ → Ω → ℝ) (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
  (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
  (hlaw : μ.map (fun ω => (X 0 ω, Y 0 ω)) =
    ENNReal.ofReal ((1-q)*3/4) • Measure.dirac (0,0) +
    ENNReal.ofReal ((1-q)/4) • Measure.dirac (0,1) +
    ENNReal.ofReal (q/4) • Measure.dirac (1,0) +
    ENNReal.ofReal (q*3/4) • Measure.dirac (1,1)) :
  let T := fun n ω => clip (1/10) (9/10) (sampleMean Y n ω)
  CP μ T (1/4+q/2) ∧
  (∀ n, 0 < n → ∀ᵐ ω ∂μ,
    T n ω ∈ Set.Icc (1/10 : ℝ) (9/10) ∧
    ∀ t ∈ Set.Icc (1/10 : ℝ) (9/10),
      (∏ i : Fin n, if Y i ω = 1 then t else 1-t) ≤
        (∏ i : Fin n, if Y i ω = 1 then T n ω else 1-T n ω) ∧
      ((∏ i : Fin n, if Y i ω = 1 then t else 1-t) =
        (∏ i : Fin n, if Y i ω = 1 then T n ω else 1-T n ω) ↔ t = T n ω)) ∧
  (0 < q ∧ q < 1 →
    conditionalMeanAt μ (X 0) (Y 0) 0 = 1/4 ∧
    conditionalMeanAt μ (X 0) (Y 0) 1 = 3/4 ∧
    ¬ CP μ T (1/4) ∧ ¬ CP μ T (3/4)) := by
  dsimp only
  have hcp := changed_covariate_marginal_mle_limit μ X Y hiid q hq hlaw
  have hbin (i : ℕ) : ∀ᵐ ω ∂μ, Y i ω=0 ∨ Y i ω=1 :=
    pooled_mle_binary μ (X i) (Y i) (hiid.1 i) _ _ _ _
      ((hiid.2.2 i).map_eq.trans hlaw)
  refine ⟨hcp, ?_, ?_⟩
  · intro n hn
    filter_upwards [ae_all_iff.mpr hbin] with ω hω
    have hfit := clipped_bernoulli_mle hn (fun i : Fin n => Y i ω) (fun i => hω i)
    dsimp only at hfit
    rw [Fin.sum_univ_eq_sum_range (fun i => Y i ω) n] at hfit
    exact hfit
  · rintro ⟨hq0,hq1⟩
    have ha : 0 ≤ (1-q)*3/4 := by nlinarith [hq.2]
    have hb : 0 ≤ (1-q)/4 := by linarith [hq.2]
    have hc : 0 ≤ q/4 := by linarith [hq.1]
    have hd : 0 ≤ q*3/4 := by nlinarith [hq.1]
    have hcells := pooled_mle_cells μ (X 0) (Y 0) (hiid.1 0) _ _ _ _
      (by simp) (by simp) (by simp) (by simp) hlaw
    rw [ENNReal.toReal_add (a := ENNReal.ofReal ((1-q)*3/4))
        (b := ENNReal.ofReal ((1-q)/4)) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_add (a := ENNReal.ofReal (q/4))
        (b := ENNReal.ofReal (q*3/4)) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top] at hcells
    simp only [ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb,
      ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hd] at hcells
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcells.1]
      apply (div_eq_iff (by nlinarith : (1-q)*3/4+(1-q)/4 ≠ 0)).mpr
      ring
    · rw [hcells.2]
      apply (div_eq_iff (by nlinarith : q/4+q*3/4 ≠ 0)).mpr
      ring
    · intro hbad
      have he := probability_limit_unique μ _ _ _ hcp hbad
      linarith
    · intro hbad
      have he := probability_limit_unique μ _ _ _ hcp hbad
      linarith

end
end AronowAudit.P001.Wave1
