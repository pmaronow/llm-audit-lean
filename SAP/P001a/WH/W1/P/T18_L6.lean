import SAP.P001a.WH.W1.Leaves
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.IntegrableTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical

noncomputable section

namespace SAP.P001a.WH.W1.P.T18_L6

lemma tail_prob_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (H : Ω → ℝ) (hH : Integrable H μ) (hHm : Measurable H)
    (hHnn : ∀ ω, 0 ≤ H ω)
    (a : ℝ) (ha : 0 < a) :
    SAP.P001a.prob μ {ω | a ≤ H ω} ≤
      (∫ ω in {ω | a / 2 < H ω}, H ω ∂μ) / a := by
  let s : Set Ω := {ω | a / 2 < H ω}
  let f : Ω → ℝ := s.indicator (fun ω => H ω / a)
  have hs : MeasurableSet s := measurableSet_lt measurable_const hHm
  have hf : Integrable f μ := by
    dsimp [f]
    exact (hH.div_const a).indicator hs
  have hf_nonneg : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ s
    · simp [f, hω, div_nonneg (hHnn ω) (le_of_lt ha)]
    · simp [f, hω]
  have hle : ∀ ω ∈ {ω | a ≤ H ω}, 1 ≤ f ω := by
    intro ω hω
    change a ≤ H ω at hω
    have hsω : ω ∈ s := lt_of_lt_of_le (by linarith [ha]) hω
    simp only [f, Set.indicator_of_mem hsω]
    exact (one_le_div₀ ha).2 hω
  have hmeasure := hf.measure_le_integral hf_nonneg hle
  have hinter : (∫ ω, f ω ∂μ) =
      (∫ ω in s, H ω ∂μ) / a := by
    rw [show f = s.indicator (fun ω => H ω / a) by rfl,
      integral_indicator hs, integral_div]
  have htail_nonneg : 0 ≤ ∫ ω in s, H ω ∂μ :=
    setIntegral_nonneg hs (fun ω hω => hHnn ω)
  change (μ {ω | a ≤ H ω}).toReal ≤
    (∫ ω in s, H ω ∂μ) / a
  have hmeasure' := ENNReal.toReal_mono (by simp) hmeasure
  rw [hinter, ENNReal.toReal_ofReal (div_nonneg htail_nonneg (le_of_lt ha))] at hmeasure'
  exact hmeasure'

end SAP.P001a.WH.W1.P.T18_L6

theorem SAP.P001a.WH.W1.T18_L6_proof : SAP.P001a.WH.W1.T18_L6 := by
  intro Ω _ μ hμ p Z hiid h2
  let H : Ω → ℝ := fun ω => ‖Z 0 ω‖ ^ 2
  have hZ : MemLp (fun ω => Z 0 ω) 2 μ := by
    apply (MeasureTheory.memLp_pi_iff).2
    exact h2
  have hH : Integrable H μ := by
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm
      hZ.aestronglyMeasurable).mp hZ
  have hHm : Measurable H := by
    dsimp [H]
    exact (hiid.1 0).norm.pow_const 2
  have hHnn : ∀ ω, 0 ≤ H ω := fun ω => sq_nonneg ‖Z 0 ω‖
  have hTail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => ∫ ω in {ω | ((n : ℝ) * ε) / 2 < H ω}, H ω ∂μ)
        atTop (nhds 0) := by
    intro ε hε
    apply AsymptoticStatistics.ForMathlib.tendsto_setIntegral_tail_of_integrable hH hHm
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      tendsto_natCast_atTop_atTop.const_mul_atTop
        (by positivity : 0 < ε / 2)
  have hrow_nonneg : ∀ n ω, 0 ≤ SAP.P001a.wholeMaxRow Z n ω := by
    intro n ω
    by_cases hn : 0 < n
    · rw [SAP.P001a.wholeMaxRow, dif_pos hn]
      apply div_nonneg
      · exact le_trans (sq_nonneg ‖Z 0 ω‖)
          (Finset.le_sup' (fun i => ‖Z i ω‖ ^ 2) (Finset.mem_range.mpr hn))
      · exact Nat.cast_nonneg n
    · rw [SAP.P001a.wholeMaxRow, dif_neg hn]
  change ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => SAP.P001a.prob μ
      {ω | ε ≤ dist (SAP.P001a.wholeMaxRow Z n ω) 0}) atTop (nhds 0)
  intro ε hε
  have hprob_nonneg : ∀ n, 0 ≤ SAP.P001a.prob μ
      {ω | ε ≤ dist (SAP.P001a.wholeMaxRow Z n ω) 0} := by
    intro n
    exact ENNReal.toReal_nonneg
  have hbound : ∀ᶠ n : ℕ in atTop,
      SAP.P001a.prob μ {ω | ε ≤ dist (SAP.P001a.wholeMaxRow Z n ω) 0} ≤
        (∫ ω in {ω | ((n : ℝ) * ε) / 2 < H ω}, H ω ∂μ) / ε := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hEqDist : ∀ ω, dist (SAP.P001a.wholeMaxRow Z n ω) 0 =
        SAP.P001a.wholeMaxRow Z n ω := by
      intro ω
      simpa [Real.dist_eq, abs_of_nonneg (hrow_nonneg n ω)]
    have hevent : {ω | ε ≤ dist (SAP.P001a.wholeMaxRow Z n ω) 0} ⊆
        ⋃ i ∈ Finset.range n, {ω | (n : ℝ) * ε ≤ ‖Z i ω‖ ^ 2} := by
      intro ω hω
      change ε ≤ dist (SAP.P001a.wholeMaxRow Z n ω) 0 at hω
      rw [hEqDist ω] at hω
      rw [SAP.P001a.wholeMaxRow, dif_pos hn] at hω
      have hsup : ε * (n : ℝ) ≤ (Finset.range n).sup'
          (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn)) (fun i => ‖Z i ω‖ ^ 2) := by
        exact (le_div_iff₀ hnR).mp hω
      obtain ⟨i, hi, hval⟩ := (Finset.le_sup'_iff _).mp hsup
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, by simpa [mul_comm] using hval⟩⟩
    have hunion := measureReal_mono hevent (measure_ne_top μ _)
    have hfinite := measureReal_biUnion_finset_le (μ := μ) (Finset.range n)
      (fun i => {ω | (n : ℝ) * ε ≤ ‖Z i ω‖ ^ 2})
    have hdist : ∀ i, SAP.P001a.prob μ {ω | (n : ℝ) * ε ≤ ‖Z i ω‖ ^ 2} =
        SAP.P001a.prob μ {ω | (n : ℝ) * ε ≤ H ω} := by
      intro i
      have hid := (hiid.2.2 i).comp
        (u := fun z : Fin p → ℝ => ‖z‖ ^ 2) (by fun_prop)
      have hmeas : MeasurableSet {x : ℝ | (n : ℝ) * ε ≤ x} := measurableSet_Ici
      change (μ {ω | (n : ℝ) * ε ≤ ‖Z i ω‖ ^ 2}).toReal =
        (μ {ω | (n : ℝ) * ε ≤ H ω}).toReal
      simpa [H] using congrArg ENNReal.toReal (hid.measure_mem_eq hmeas)
    have hsingle := SAP.P001a.WH.W1.P.T18_L6.tail_prob_le μ H hH hHm hHnn
      ((n : ℝ) * ε) (mul_pos hnR hε)
    have hsum : (∑ i ∈ Finset.range n,
        SAP.P001a.prob μ {ω | (n : ℝ) * ε ≤ ‖Z i ω‖ ^ 2}) =
        (n : ℝ) * SAP.P001a.prob μ {ω | (n : ℝ) * ε ≤ H ω} := by
      simp_rw [hdist]
      simp
    have hcomb : SAP.P001a.prob μ
        {ω | ε ≤ dist (SAP.P001a.wholeMaxRow Z n ω) 0} ≤
        (n : ℝ) * SAP.P001a.prob μ {ω | (n : ℝ) * ε ≤ H ω} := by
      calc
        _ ≤ μ.real (⋃ i ∈ Finset.range n,
            {ω | (n : ℝ) * ε ≤ ‖Z i ω‖ ^ 2}) := hunion
        _ ≤ ∑ i ∈ Finset.range n,
            μ.real {ω | (n : ℝ) * ε ≤ ‖Z i ω‖ ^ 2} := hfinite
        _ = _ := hsum
    calc
      _ ≤ (n : ℝ) * SAP.P001a.prob μ {ω | (n : ℝ) * ε ≤ H ω} := hcomb
      _ ≤ (n : ℝ) * ((∫ ω in {ω | ((n : ℝ) * ε) / 2 < H ω}, H ω ∂μ) /
          ((n : ℝ) * ε)) :=
        mul_le_mul_of_nonneg_left hsingle hnR.le
      _ = (∫ ω in {ω | ((n : ℝ) * ε) / 2 < H ω}, H ω ∂μ) / ε := by
        field_simp
  have hlim := (hTail ε hε).div_const ε
  simp only [zero_div] at hlim
  exact squeeze_zero' (Eventually.of_forall hprob_nonneg) hbound hlim
