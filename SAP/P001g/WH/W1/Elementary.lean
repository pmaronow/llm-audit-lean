import SAP.P001g.Defs.WholeW1
import SAP.P001g.Bridge
import AronowAudit.P001.P001_ConfidenceInstances
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P001g.WH.W1
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
/-- All the population equalities use restricted integral congruence and
linearity. Independence is used only for identification of the population ATE. -/
theorem population_chain {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y0 Y1 D : Ω → ℝ)
    (h0 : Measurable Y0) (h1 : Measurable Y1) (hD : Measurable D)
    (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ)
    (hp : 0 < prob μ {ω | D ω = 1} ∧ 0 < prob μ {ω | D ω = 0}) :
    let Y := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
    let τ := fun ω => Y1 ω - Y0 ω
    let arm := fun Z d => conditionalMeanAt μ D Z d
    (IndepFun (fun ω => (Y0 ω, Y1 ω)) D μ → mean μ τ = arm Y 1 - arm Y 0) ∧
    arm Y 1 - arm Y 0 = arm Y1 1 - arm Y0 0 ∧
    arm Y1 1 - arm Y0 0 = arm (fun ω => τ ω + Y0 ω) 1 - arm Y0 0 ∧
    arm (fun ω => τ ω + Y0 ω) 1 - arm Y0 0 = arm τ 1 + arm Y0 1 - arm Y0 0 := by
  let Y := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
  let arm := fun Z d => conditionalMeanAt μ D Z d
  have hA (d : ℝ) : MeasurableSet {ω | D ω = d} := measurableSet_eq_fun hD measurable_const
  have hy1 : arm Y 1 = arm Y1 1 := by
    unfold arm conditionalMeanAt
    congr 1
    apply setIntegral_congr_fun (hA 1)
    intro ω hω
    change D ω = _ at hω
    simp [Y, observedOutcome, hω]
  have hy0 : arm Y 0 = arm Y0 0 := by
    unfold arm conditionalMeanAt
    congr 1
    apply setIntegral_congr_fun (hA 0)
    intro ω hω
    change D ω = _ at hω
    simp [Y, observedOutcome, hω]
  have harm (Z : Ω → ℝ) (hc : IsCEF μ D Z (fun _ => mean μ Z))
      (d : ℝ) (hd : 0 < prob μ {ω | D ω = d}) : arm Z d = mean μ Z := by
    have he := hc.2.2.2 {d} (measurableSet_singleton d)
    have hset : D ⁻¹' ({d} : Set ℝ) = {ω | D ω = d} := by ext; simp
    rw [hset] at he
    have he' : (∫ ω in {ω | D ω = d}, Z ω ∂μ) = prob μ {ω | D ω = d} * mean μ Z := by
      simpa [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, prob, Measure.real] using he
    dsimp [arm, conditionalMeanAt]
    rw [he']
    field_simp [hd.ne']
  have hsum : (fun ω => (Y1 ω - Y0 ω) + Y0 ω) = Y1 := by funext; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hind
    have hc0 : IsCEF μ D Y0 (fun _ => mean μ Y0) :=
      AronowAudit.P001.independent_constant_cef μ D Y0 hD h0 hi0
        ((hind.comp measurable_fst measurable_id).symm)
    have hc1 : IsCEF μ D Y1 (fun _ => mean μ Y1) :=
      AronowAudit.P001.independent_constant_cef μ D Y1 hD h1 hi1
        ((hind.comp measurable_snd measurable_id).symm)
    change mean μ (fun ω => Y1 ω - Y0 ω) = arm Y 1 - arm Y 0
    rw [hy1, hy0, harm Y1 hc1 1 hp.1, harm Y0 hc0 0 hp.2]
    exact integral_sub hi1 hi0
  · change arm Y 1 - arm Y 0 = arm Y1 1 - arm Y0 0
    rw [hy1, hy0]
  · change arm Y1 1 - arm Y0 0 = arm (fun ω => (Y1 ω - Y0 ω) + Y0 ω) 1 - arm Y0 0
    rw [hsum]
  · change arm (fun ω => (Y1 ω - Y0 ω) + Y0 ω) 1 - arm Y0 0 =
      arm (fun ω => Y1 ω - Y0 ω) 1 + arm Y0 1 - arm Y0 0
    rw [hsum]
    dsimp [arm, conditionalMeanAt]
    rw [integral_sub hi1.integrableOn hi0.integrableOn, sub_div]
    ring
/-- Finite atomic integration for the empirical observed law. -/
theorem empiricalPairs_integral {n : ℕ} (_hn : 0 < n) (y d : Fin n → ℝ) (f : ℝ × ℝ → ℝ) :
    (∫ z, f z ∂wholeEmpiricalPairs y d) = (∑ i, f (y i, d i)) / (n : ℝ) := by
  classical
  unfold wholeEmpiricalPairs
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv, smul_eq_mul, div_eq_mul_inv, mul_comm]
  · intro i _
    exact integrable_dirac (by simp)
/-- Conditional means under a finite empirical law are indicator-weighted
sample averages, provided the arm count is positive. -/
theorem empiricalPairs_arm {n : ℕ} (hn : 0 < n) (y d : Fin n → ℝ) (a : ℝ)
    (hc : 0 < ∑ i : Fin n, if d i = a then (1 : ℝ) else 0) :
    conditionalMeanAt (wholeEmpiricalPairs y d) Prod.snd Prod.fst a =
      (∑ i, if d i = a then y i else 0) / (∑ i, if d i = a then (1 : ℝ) else 0) := by
  classical
  let Q := wholeEmpiricalPairs y d
  have hA : MeasurableSet {z : ℝ × ℝ | z.2 = a} :=
    measurableSet_eq_fun measurable_snd measurable_const
  have hnum : (∫ z in {z : ℝ × ℝ | z.2 = a}, z.1 ∂Q) =
      (∑ i, if d i = a then y i else 0) / (n : ℝ) := by
    rw [← integral_indicator hA]
    exact empiricalPairs_integral hn y d _
  have hden : prob Q {z : ℝ × ℝ | z.2 = a} =
      (∑ i, if d i = a then (1 : ℝ) else 0) / (n : ℝ) := by
    rw [prob, ← measureReal_def, ← integral_indicator_one hA]
    exact empiricalPairs_integral hn y d _
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold conditionalMeanAt
  rw [hnum, hden]
  field_simp [hnr, hc.ne']
/-- The complete finite-sample plug-in formula, with its denominator guards. -/
theorem empiricalPairs_formula {n : ℕ} (hn : 0 < n) (y d : Fin n → ℝ)
    (hb : ∀ i, d i = 0 ∨ d i = 1) (hc1 : 0 < ∑ i, d i) (hc0 : 0 < ∑ i, (1 - d i)) :
    IsProbabilityMeasure (wholeEmpiricalPairs y d) ∧
    conditionalMeanAt (wholeEmpiricalPairs y d) Prod.snd Prod.fst 1 =
      (∑ i, y i * d i) / (∑ i, d i) ∧
    conditionalMeanAt (wholeEmpiricalPairs y d) Prod.snd Prod.fst 0 =
      (∑ i, y i * (1 - d i)) / (∑ i, (1 - d i)) ∧
    wholeATEFunctional (wholeEmpiricalPairs y d) =
      (∑ i, y i * d i) / (∑ i, d i) - (∑ i, y i * (1 - d i)) / (∑ i, (1 - d i)) := by
  classical
  have hd1 (i : Fin n) : (if d i = 1 then (1 : ℝ) else 0) = d i := by
    rcases hb i with h | h <;> simp [h]
  have hd0 (i : Fin n) : (if d i = 0 then (1 : ℝ) else 0) = 1 - d i := by
    rcases hb i with h | h <;> simp [h]
  have hy1 (i : Fin n) : (if d i = 1 then y i else 0) = y i * d i := by
    rcases hb i with h | h <;> simp [h]
  have hy0 (i : Fin n) : (if d i = 0 then y i else 0) = y i * (1 - d i) := by
    rcases hb i with h | h <;> simp [h]
  have h1 := empiricalPairs_arm hn y d 1 (by simpa only [hd1] using hc1)
  have h0 := empiricalPairs_arm hn y d 0 (by simpa only [hd0] using hc0)
  simp only [hd1, hd0, hy1, hy0] at h1 h0
  refine ⟨?_, h1, h0, ?_⟩
  · constructor
    simp [wholeEmpiricalPairs, Measure.smul_apply, Measure.finsetSum_apply,
      ENNReal.inv_mul_cancel, Nat.ne_of_gt hn]
  · exact congrArg₂ (fun x y : ℝ => x - y) h1 h0
/-- An explicitly iid Gaussian observation stream. -/
abbrev NormalStream := ℕ → ℝ
def normalStreamLaw : Measure NormalStream := Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)
instance normalStreamLaw_probability : IsProbabilityMeasure normalStreamLaw := by
  dsimp [normalStreamLaw]
  infer_instance
def normalEstimate (n : ℕ) (ω : NormalStream) : ℝ :=
  if n = 0 then 0 else ω 0 / Real.sqrt n
/-- Overwriting a single variance estimate leaves the asymptotic premise intact. -/
def collapsedVariance (n : ℕ) (_ : NormalStream) : ℝ :=
  if n = 0 then 0 else if n = 1 then 0 else 1 / (n : ℝ)
theorem normalStream_iid : IID normalStreamLaw (fun i ω => ω i) := by
  have hlaw (i : ℕ) : normalStreamLaw.map (fun ω => ω i) = gaussianReal 0 1 :=
    Measure.infinitePi_map_eval _ i
  refine ⟨fun i => measurable_pi_apply i, iIndepFun_infinitePi (fun _ => measurable_id), ?_⟩
  intro i
  exact ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
    (hlaw i).trans (hlaw 0).symm⟩
theorem normalEstimate_statistic (n : ℕ) (hn : 0 < n) :
    ∃ h : (Fin n → ℝ) → ℝ × ℝ, Measurable h ∧
      ∀ ω, (normalEstimate n ω, collapsedVariance n ω) =
        h (firstSample (fun i ω => ω i) n ω) := by
  refine ⟨fun s => (s ⟨0, hn⟩ / Real.sqrt n, if n = 1 then 0 else 1 / (n : ℝ)), ?_, ?_⟩
  · exact ((measurable_pi_apply (⟨0, hn⟩ : Fin n)).div_const _).prodMk measurable_const
  · intro ω
    simp [normalEstimate, collapsedVariance, firstSample, hn.ne']
theorem normalEstimate_limit :
    CD normalStreamLaw (fun n ω => Real.sqrt n * (normalEstimate n ω - 0))
      (gaussianReal 0 ⟨(1 : ℝ) ^ 2, sq_nonneg _⟩) := by
  have hv : (⟨(1 : ℝ) ^ 2, sq_nonneg (1 : ℝ)⟩ : ℝ≥0) = 1 := by ext; norm_num
  rw [hv]
  intro x _hx
  have hCDF : cdf normalStreamLaw (fun ω => ω 0) x = prob (gaussianReal 0 1) (Set.Iic x) := by
    change (normalStreamLaw ((fun ω => ω 0) ⁻¹' Set.Iic x)).toReal = _
    rw [← Measure.map_apply (measurable_pi_apply 0) measurableSet_Iic]
    rw [show normalStreamLaw.map (fun ω => ω 0) = gaussianReal 0 1 from
      Measure.infinitePi_map_eval _ 0]
    rfl
  have he : (fun n : ℕ => cdf normalStreamLaw
      (fun ω => Real.sqrt n * (normalEstimate n ω - 0)) x) =ᶠ[atTop]
      (fun _ => prob (gaussianReal 0 1) (Set.Iic x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
    have hf : (fun ω : NormalStream => Real.sqrt n * (normalEstimate n ω - 0)) =
        (fun ω => ω 0) := by
      funext ω
      simp only [normalEstimate, hn.ne', ite_false, sub_zero]
      field_simp [hs]
    rw [hf, hCDF]
  exact tendsto_const_nhds.congr' he.symm
theorem collapsedVariance_consistent : VarianceConsistent normalStreamLaw collapsedVariance ((1 : ℝ) ^ 2) := by
  intro ε hε
  have he : (fun n : ℕ => prob normalStreamLaw
      {ω | ε ≤ dist ((n : ℝ) * collapsedVariance n ω) ((1 : ℝ) ^ 2)}) =ᶠ[atTop]
      (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    simp [collapsedVariance, show n ≠ 0 by omega, ne_of_gt hn, hn0, not_le_of_gt hε, prob]
  exact tendsto_const_nhds.congr' he.symm
/-- All normal-interval hypotheses hold in the concrete iid experiment. -/
theorem normalCounterexample_premises :
    (∀ n, Measurable (normalEstimate n)) ∧
    (∀ n, Measurable (collapsedVariance n)) ∧
    (∀ n ω, 0 ≤ collapsedVariance n ω) ∧
    0 < (1 : ℝ) ∧
    AronowAudit.P001.ConfidenceInstances.ciAlpha ∈ Set.Ioo (0 : ℝ) 1 ∧
    prob (gaussianReal 0 1) (Set.Iic (1 : ℝ)) =
      1 - AronowAudit.P001.ConfidenceInstances.ciAlpha / 2 ∧
    CD normalStreamLaw (fun n ω => Real.sqrt n * (normalEstimate n ω - 0))
      (gaussianReal 0 ⟨(1 : ℝ) ^ 2, sq_nonneg _⟩) ∧
    VarianceConsistent normalStreamLaw collapsedVariance ((1 : ℝ) ^ 2) := by
  refine ⟨?_, ?_, ?_, by norm_num,
    AronowAudit.P001.ConfidenceInstances.ci_alpha_admissible, ?_,
    normalEstimate_limit, collapsedVariance_consistent⟩
  · intro n
    change Measurable (fun ω : NormalStream => if n = 0 then 0 else ω 0 / Real.sqrt n)
    by_cases hn : n = 0
    · simp only [hn, ite_true]
      exact measurable_const
    · simp only [hn, ite_false]
      exact (measurable_pi_apply 0 : Measurable (fun ω : NormalStream => ω 0)).div_const _
  · intro n
    exact measurable_const
  · intro n ω
    dsimp [collapsedVariance]
    split_ifs
    · exact le_rfl
    · exact le_rfl
    · exact div_nonneg (by norm_num) (Nat.cast_nonneg n)
  · unfold AronowAudit.P001.ConfidenceInstances.ciAlpha
    change prob (gaussianReal 0 1) (Set.Iic 1) =
      1 - 2 * (1 - prob (gaussianReal 0 1) (Set.Iic 1)) / 2
    ring
/-- The omitted strict-endpoint requirement fails even for genuine statistics
of the first n observations of an infinite iid normal stream. -/
theorem normalInterval_refuted : T128WholeStatement := by
  intro h
  rcases normalCounterexample_premises with ⟨hm, hv, hp, hφ, hα, hz, hAN, hVC⟩
  have hc := h normalStreamLaw (fun i ω => ω i) normalStream_iid
    normalEstimate collapsedVariance normalEstimate_statistic hm hv hp
    0 1 AronowAudit.P001.ConfidenceInstances.ciAlpha 1 hφ hα hz hAN hVC
  have horder := hc.1 1 (by norm_num)
  simp [collapsedVariance, prob] at horder
/-- Half-mass on every covariate event identifies the constant propensity.
This argument uses only bounded indicators and finite measures. -/
theorem fair_indicator_cef {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (A : Set Ω) (hA : MeasurableSet A)
    (hhalf : ∀ B : Set E, MeasurableSet B →
      μ (X ⁻¹' B ∩ A) = (1 / 2 : ℝ≥0∞) * μ (X ⁻¹' B)) :
    IsCEF μ X (A.indicator (fun _ => (1 : ℝ))) (fun _ => 1 / 2) := by
  classical
  refine ⟨measurable_const, (integrable_const 1).indicator hA, integrable_const _, ?_⟩
  intro B _hB
  calc
    (∫ ω in X ⁻¹' B, A.indicator (fun _ => (1 : ℝ)) ω ∂μ) =
        (μ (X ⁻¹' B ∩ A)).toReal := by
      rw [integral_indicator_const 1 hA]
      simp [measureReal_def, Measure.restrict_apply hA, Set.inter_comm, smul_eq_mul]
    _ = (1 / 2 : ℝ) * (μ (X ⁻¹' B)).toReal := by
      rw [hhalf B _hB, ENNReal.toReal_mul]
      norm_num
    _ = ∫ ω in X ⁻¹' B, (1 / 2 : ℝ) ∂μ := by
      simp [integral_const, smul_eq_mul, Measure.real, mul_comm]
/-- A constant potential-outcome pair is conditionally independent of every
treatment, on any covariate sigma algebra. -/
theorem zero_pair_CI {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (D : Ω → ℝ) : CI μ X hX (fun _ => ((0 : ℝ), (0 : ℝ))) D := by
  classical
  intro A B _hA _hB
  have hm := measurable_iff_comap_le.mp hX
  by_cases h : ((0 : ℝ), (0 : ℝ)) ∈ A
  · simp only [h, true_and, ite_true, condExp_const hm, one_mul]
    exact Filter.EventuallyEq.rfl
  · simp only [h, false_and, ite_false, condExp_const hm, zero_mul]
    exact Filter.EventuallyEq.rfl
/-- Existing weighted-arm integrability applies to each IPW arm. -/
theorem causal_ipw_integrable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Fin K → ℝ) (hX : Measurable X)
    (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1) (hD : Measurable D)
    (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ)
    (hb : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) (p : (Fin K → ℝ) → ℝ)
    (hp : IsCEF μ X D p)
    (hpos : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω) ∧ p (X ω) < 1 - ε)
    (hCI : CI μ X hX (fun ω => (Y0 ω, Y1 ω)) D) :
    Integrable (fun ω => wholeIPWScore (observedOutcome (Y0 ω) (Y1 ω) (D ω)) (D ω) (p (X ω))) μ := by
  let U := fun ω => (Y0 ω, Y1 ω)
  have hU : Measurable U := h0.prodMk h1
  obtain ⟨ε, hε, hεp⟩ := hpos
  have hc := AronowAudit.P001.Wave1.CausalIpwDr.n1_proof μ X hX U D hCI
  have hb0 : ∀ᵐ ω ∂μ, 1 - D ω = 0 ∨ 1 - D ω = 1 :=
    hb.mono fun ω h => by rcases h with h | h <;> simp [h]
  have hI1 := (AronowAudit.P001.Wave1.MarSelection.n6_proof
    AronowAudit.P001.Wave1.MarSelection.n1_proof AronowAudit.P001.Wave1.MarSelection.n4_proof
    AronowAudit.P001.Wave1.MarSelection.n3_proof AronowAudit.P001.Wave1.MarSelection.n2_proof
    μ X hX U D (fun z => z.2.2) p hU hD measurable_snd.snd hp.1 hb hCI hi1
    ⟨ε, hε, hεp.mono fun _ h => h.1.le⟩).1
  have hI0 := (AronowAudit.P001.Wave1.MarSelection.n6_proof
    AronowAudit.P001.Wave1.MarSelection.n1_proof AronowAudit.P001.Wave1.MarSelection.n4_proof
    AronowAudit.P001.Wave1.MarSelection.n3_proof AronowAudit.P001.Wave1.MarSelection.n2_proof
    μ X hX U (fun ω => 1 - D ω) (fun z => z.2.1) (fun x => 1 - p x) hU
    (measurable_const.sub hD) measurable_snd.fst (measurable_const.sub hp.1) hb0 hc hi0
    ⟨ε, hε, hεp.mono fun _ h => by linarith [h.2]⟩).1
  apply (hI1.sub hI0).congr
  filter_upwards [hb] with ω hω
  rcases hω with hω | hω <;> simp [wholeIPWScore, observedOutcome, hω, U]
end
end SAP.P001g.WH.W1
