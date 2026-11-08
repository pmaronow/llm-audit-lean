import SAP.P001a.WH.W1.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix Matrix.Norms.Elementwise

noncomputable section

universe u v

namespace SAP.P001a.WH.W1

lemma discrepancy_small {Ω A T : Type*} [MeasurableSpace A] {κ : Measure ℝ}
    (X : ℕ → Ω → A) (Y : ℕ → Ω → ℝ) (G : T → WholeDensity A κ)
    (M : T → ℝ) (n : ℕ) (ω : Ω) (r : ℝ) (hr : 0 < r)
    (hsmall : wholeLogDiscrepancy X Y G M n ω < ENNReal.ofReal r) (t : T) :
    (∀ i ∈ Finset.range n, 0 < (G t).density (X i ω) (Y i ω)) ∧
    |(∑ i ∈ Finset.range n, Real.log ((G t).density (X i ω) (Y i ω))) /
      (n : ℝ) - M t| < r := by
  have ht := (le_iSup (fun t : T => if ∀ i ∈ Finset.range n,
      0 < (G t).density (X i ω) (Y i ω) then ENNReal.ofReal
      |(∑ i ∈ Finset.range n, Real.log ((G t).density (X i ω) (Y i ω))) /
        (n : ℝ) - M t| else ∞) t).trans_lt hsmall
  split_ifs at ht with hp
  · exact ⟨hp, (ENNReal.ofReal_lt_ofReal_iff hr).mp ht⟩
  · exact (not_lt_of_ge le_top ht).elim

lemma product_max_log_comparison {Ω A T : Type*} [MeasurableSpace A] {κ : Measure ℝ}
    (X : ℕ → Ω → A) (Y : ℕ → Ω → ℝ) (G : T → WholeDensity A κ)
    (n : ℕ) (hn : 0 < n) (ω : Ω) (s t : T)
    (hs : ∀ i ∈ Finset.range n, 0 < (G s).density (X i ω) (Y i ω))
    (ht : ∀ i ∈ Finset.range n, 0 < (G t).density (X i ω) (Y i ω))
    (hop : (∏ i ∈ Finset.range n, (G s).density (X i ω) (Y i ω)) ≤
      ∏ i ∈ Finset.range n, (G t).density (X i ω) (Y i ω)) :
    (∑ i ∈ Finset.range n, Real.log ((G s).density (X i ω) (Y i ω))) / (n : ℝ) ≤
      (∑ i ∈ Finset.range n, Real.log ((G t).density (X i ω) (Y i ω))) / (n : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  rw [← Real.log_prod (fun i hi => (hs i hi).ne'),
    ← Real.log_prod (fun i hi => (ht i hi).ne')]
  exact Real.log_le_log (Finset.prod_pos hs) hop

lemma likelihood_argmax {Ω A T : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [PseudoMetricSpace T] (μ : Measure Ω) [IsProbabilityMeasure μ] {κ : Measure ℝ}
    (X : ℕ → Ω → A) (Y : ℕ → Ω → ℝ) (G : T → WholeDensity A κ)
    (M : T → ℝ) (tstar : T) (that : ℕ → Ω → T)
    (e : ℕ → Ω → ℝ) (hen : ∀ n, 0 < n → ∀ᵐ ω ∂μ, 0 ≤ e n ω) (he : CP μ e 0)
    (hsep : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : T,
      ε ≤ dist t tstar → M t ≤ M tstar - δ)
    (hUC : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => prob μ
      {ω | ENNReal.ofReal ε ≤ wholeLogDiscrepancy X Y G M n ω}) atTop (nhds 0))
    (hmax : (∀ n, 0 < n → ∀ᵐ ω ∂μ, ∀ t : T,
      (∏ i ∈ Finset.range n, (G t).density (X i ω) (Y i ω)) ≤
      ∏ i ∈ Finset.range n, (G (that n ω)).density (X i ω) (Y i ω)) ∨
    (∀ n, 0 < n → ∀ᵐ ω ∂μ, ∀ t : T,
      wholeSampleLog X Y G n ω t ≤ wholeSampleLog X Y G n ω (that n ω) +
        (e n ω : EReal))) : CP μ that tstar := by
  intro ε hε
  obtain ⟨δ, hδ, hsepδ⟩ := hsep ε hε
  have hd4 : 0 < δ / 4 := by positivity
  have hd2 : 0 < δ / 2 := by positivity
  have hlim := (hUC (δ / 4) hd4).add (he (δ / 2) hd2)
  simp only [add_zero] at hlim
  have hbound : ∀ᶠ n in atTop, prob μ {ω | ε ≤ dist (that n ω) tstar} ≤
      prob μ {ω | ENNReal.ofReal (δ / 4) ≤ wholeLogDiscrepancy X Y G M n ω} +
      prob μ {ω | δ / 2 ≤ dist (e n ω) 0} := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hopt : ∀ᵐ ω ∂μ, ∀ s t : T,
        wholeLogDiscrepancy X Y G M n ω < ENNReal.ofReal (δ / 4) →
        (∑ i ∈ Finset.range n, Real.log ((G s).density (X i ω) (Y i ω))) /
          (n : ℝ) - e n ω ≤
        (∑ i ∈ Finset.range n, Real.log ((G (that n ω)).density (X i ω) (Y i ω))) /
          (n : ℝ) := by
      rcases hmax with hprod | hlog
      · filter_upwards [hprod n hn, hen n hn] with ω hω hnonneg
        intro s t hsmall
        have hs := (discrepancy_small X Y G M n ω _ hd4 hsmall s).1
        have ht := (discrepancy_small X Y G M n ω _ hd4 hsmall (that n ω)).1
        have hc := product_max_log_comparison X Y G n hn ω s (that n ω) hs ht (hω s)
        linarith
      · filter_upwards [hlog n hn] with ω hω
        intro s t hsmall
        have hs := (discrepancy_small X Y G M n ω _ hd4 hsmall s).1
        have ht := (discrepancy_small X Y G M n ω _ hd4 hsmall (that n ω)).1
        have hop := hω s
        simp only [wholeSampleLog, ite_eq_left hs, ite_eq_left ht] at hop
        rw [← EReal.coe_add] at hop
        have hop' := EReal.coe_le_coe_iff.mp hop
        linarith
    have hsub : ∀ᵐ ω ∂μ, ω ∈ {ω | ε ≤ dist (that n ω) tstar} →
        ω ∈ {ω | ENNReal.ofReal (δ / 4) ≤ wholeLogDiscrepancy X Y G M n ω} ∪
          {ω | δ / 2 ≤ dist (e n ω) 0} := by
      filter_upwards [hopt] with ω hoptω
      intro hbad
      by_contra hnot
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
      have hfit := (discrepancy_small X Y G M n ω _ hd4 hnot.1 (that n ω)).2.le
      have hstar := (discrepancy_small X Y G M n ω _ hd4 hnot.1 tstar).2.le
      have hop := hoptω tstar tstar hnot.1
      have hgap := AronowAudit.P001.argmax_finite_gap M
        (fun t => (∑ i ∈ Finset.range n, Real.log ((G t).density (X i ω) (Y i ω))) /
          (n : ℝ)) (that n ω) tstar (δ / 4) (e n ω) hfit hstar hop
      have hfar := hsepδ (that n ω) hbad
      have hel : e n ω < δ / 2 := by
        have hd : |e n ω| < δ / 2 := by simpa only [Real.dist_eq, sub_zero] using hnot.2
        exact (le_abs_self (e n ω)).trans_lt hd
      linarith
    have hmono : prob μ {ω | ε ≤ dist (that n ω) tstar} ≤
        prob μ ({ω | ENNReal.ofReal (δ / 4) ≤ wholeLogDiscrepancy X Y G M n ω} ∪
          {ω | δ / 2 ≤ dist (e n ω) 0}) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    exact hmono.trans (measureReal_union_le _ _)
  exact squeeze_zero' (Eventually.of_forall (fun n => ENNReal.toReal_nonneg)) hbound hlim

end SAP.P001a.WH.W1
