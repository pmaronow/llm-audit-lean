import SAP.P001d.WH.W2.P.T61_L6Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.WH.W2.P.T61_L6

open SAP.P001d
open AronowAudit.P001.TailA

local instance instDecidableT61Tail (p : Prop) : Decidable p := Classical.propDecidable p


private lemma bootstrap_test_transfer_bound {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (f : ℝ → ℝ) (C : ℝ) (hC : ∀ z, |f z| ≤ C)
    (hp : SAP.P001d.wholeEmpiricalCDF x 0 ∈ Set.Icc (3/8 : ℝ) (5/8)) :
    |SAP.P001d.bootstrapTestMean (@SAP.P001d.wholeRegularStatistic n) x f -
      SAP.P001d.bootstrapTestMean (@SAP.P001d.wholeSignStatistic n) x f| ≤
        2*C*(16/(n : ℝ)) := by
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  have hfd (z w : ℝ) : |f z-f w| ≤ 2*C := by
    calc
      |f z-f w| ≤ |f z|+|f w| := abs_sub _ _
      _ ≤ C+C := add_le_add (hC z) (hC w)
      _ = 2*C := by ring
  have hden : 0 < (n : ℝ)^n := pow_pos (by exact_mod_cast hn) _
  let bad : (Fin n → Fin n) → Prop := fun a =>
    SAP.P001d.wholeEmpiricalCDF (AronowAudit.P001.resample x a) 0 ∉ Set.Icc (1/4 : ℝ) (3/4)
  have hpoint (a : Fin n → Fin n) :
      |f (Real.sqrt n * (@SAP.P001d.wholeRegularStatistic n
          (AronowAudit.P001.resample x a) - @SAP.P001d.wholeRegularStatistic n x)) -
        f (Real.sqrt n * (@SAP.P001d.wholeSignStatistic n
          (AronowAudit.P001.resample x a) - @SAP.P001d.wholeSignStatistic n x))| ≤
      2*C*(if bad a then (1 : ℝ) else 0) := by
    by_cases hb : bad a
    · rw [if_pos hb]
      simpa only [mul_one] using hfd _ _
    · have hq : SAP.P001d.wholeEmpiricalCDF
          (AronowAudit.P001.resample x a) 0 ∈ Set.Icc (1/4 : ℝ) (3/4) := by
        simpa only [bad, not_not] using hb
      have hpx : SAP.P001d.wholeEmpiricalCDF x 0 ∈ Set.Icc (1/4 : ℝ) (3/4) := by
        constructor <;> linarith [hp.1, hp.2]
      have hregularx : @SAP.P001d.wholeRegularStatistic n x =
          @SAP.P001d.wholeSignStatistic n x := by
        change (if SAP.P001d.wholeEmpiricalCDF x 0 ∈ Set.Icc (1/4 : ℝ) (3/4) then
          SAP.P001d.wholeEmpiricalCDF x 0 - 1/2 else
            sInf {t : ℝ | 1/2 ≤ SAP.P001d.wholeEmpiricalCDF x t}) =
          SAP.P001d.wholeEmpiricalCDF x 0 - 1/2
        rw [if_pos hpx]
      have hregularq : @SAP.P001d.wholeRegularStatistic n
          (AronowAudit.P001.resample x a) =
          @SAP.P001d.wholeSignStatistic n (AronowAudit.P001.resample x a) := by
        change (if SAP.P001d.wholeEmpiricalCDF (AronowAudit.P001.resample x a) 0 ∈
          Set.Icc (1/4 : ℝ) (3/4) then
          SAP.P001d.wholeEmpiricalCDF (AronowAudit.P001.resample x a) 0 - 1/2 else
            sInf {t : ℝ | 1/2 ≤ SAP.P001d.wholeEmpiricalCDF (AronowAudit.P001.resample x a) t}) =
          SAP.P001d.wholeEmpiricalCDF (AronowAudit.P001.resample x a) 0 - 1/2
        rw [if_pos hq]
      rw [if_neg hb, hregularq, hregularx]
      simp
  have hbasic :
      |SAP.P001d.bootstrapTestMean (@SAP.P001d.wholeRegularStatistic n) x f -
        SAP.P001d.bootstrapTestMean (@SAP.P001d.wholeSignStatistic n) x f| ≤
      (∑ a : Fin n → Fin n,
        |f (Real.sqrt n * (@SAP.P001d.wholeRegularStatistic n
          (fun i => x (a i)) - @SAP.P001d.wholeRegularStatistic n x)) -
        f (Real.sqrt n * (@SAP.P001d.wholeSignStatistic n
          (fun i => x (a i)) - @SAP.P001d.wholeSignStatistic n x))|)/(n : ℝ)^n := by
    change |(∑ a : Fin n → Fin n, f (Real.sqrt n *
        (@SAP.P001d.wholeRegularStatistic n (fun i => x (a i))-
          @SAP.P001d.wholeRegularStatistic n x)))/(n : ℝ)^n -
      (∑ a : Fin n → Fin n, f (Real.sqrt n *
        (@SAP.P001d.wholeSignStatistic n (fun i => x (a i))-
          @SAP.P001d.wholeSignStatistic n x)))/(n : ℝ)^n| ≤ _
    rw [← sub_div, abs_div, abs_of_pos hden, ← Finset.sum_sub_distrib]
    apply div_le_div_of_nonneg_right _ hden.le
    exact Finset.abs_sum_le_sum_abs
      (fun a : Fin n → Fin n => f (Real.sqrt n *
        (@SAP.P001d.wholeRegularStatistic n (fun i => x (a i)) -
          @SAP.P001d.wholeRegularStatistic n x)) -
        f (Real.sqrt n * (@SAP.P001d.wholeSignStatistic n (fun i => x (a i)) -
          @SAP.P001d.wholeSignStatistic n x))) Finset.univ
  have hsum :
      (∑ a : Fin n → Fin n,
        |f (Real.sqrt n * (@SAP.P001d.wholeRegularStatistic n
          (AronowAudit.P001.resample x a) - @SAP.P001d.wholeRegularStatistic n x)) -
        f (Real.sqrt n * (@SAP.P001d.wholeSignStatistic n
          (AronowAudit.P001.resample x a) - @SAP.P001d.wholeSignStatistic n x))|) ≤
      ∑ a : Fin n → Fin n, 2*C*(if bad a then (1 : ℝ) else 0) :=
    Finset.sum_le_sum fun a _ => hpoint a
  have hprobBad :
      (∑ a : Fin n → Fin n, if bad a then (1 : ℝ) else 0)/(n : ℝ)^n =
        AronowAudit.P001.prob (UniformResampling n) {a | bad a} := by
    rw [← AronowAudit.P001.TailA.uniform_resampling_mean n (fun a => if bad a then (1 : ℝ) else 0)]
    rw [AronowAudit.P001.mean]
    have hi : (fun a : Fin n → Fin n => if bad a then (1 : ℝ) else 0) =
        {a | bad a}.indicator (fun _ => (1 : ℝ)) := by
      funext a
      simp [Set.indicator]
    rw [hi]
    change (∫ a, ({a | bad a}.indicator (1 : (Fin n → Fin n) → ℝ)) a
      ∂UniformResampling n) = ((UniformResampling n) {a | bad a}).toReal
    exact integral_indicator_one MeasurableSet.of_discrete
  have hscale :
      (∑ a : Fin n → Fin n, 2*C*(if bad a then (1 : ℝ) else 0))/(n : ℝ)^n =
        2*C*((∑ a : Fin n → Fin n, if bad a then (1 : ℝ) else 0)/(n : ℝ)^n) := by
    calc
      (∑ a : Fin n → Fin n, 2*C*(if bad a then (1 : ℝ) else 0))/(n : ℝ)^n =
          (2*C * ∑ a : Fin n → Fin n, if bad a then (1 : ℝ) else 0)/(n : ℝ)^n := by
        congr 1
        exact (Finset.mul_sum Finset.univ
          (fun a : Fin n → Fin n => if bad a then (1 : ℝ) else 0) (2*C)).symm
      _ = 2*C*((∑ a : Fin n → Fin n, if bad a then (1 : ℝ) else 0)/(n : ℝ)^n) := by
        field_simp [ne_of_gt hden] <;> ring
  have hbound :
      |SAP.P001d.bootstrapTestMean (@SAP.P001d.wholeRegularStatistic n) x f -
        SAP.P001d.bootstrapTestMean (@SAP.P001d.wholeSignStatistic n) x f| ≤
        2*C*(16/(n : ℝ)) := by
    calc
      _ ≤ (∑ a : Fin n → Fin n, 2*C*(if bad a then (1 : ℝ) else 0))/(n : ℝ)^n := by
        apply hbasic.trans
        apply div_le_div_of_nonneg_right _ hden.le
        exact hsum
      _ = 2*C*AronowAudit.P001.prob (UniformResampling n) {a | bad a} := by
        rw [hscale, hprobBad]
      _ ≤ 2*C*(16/(n : ℝ)) :=
        mul_le_mul_of_nonneg_left (resampling_bad_branch_bound hn x hp) (by positivity)
  exact hbound

end SAP.P001d.WH.W2.P.T61_L6

/-- The centered sign bootstrap tests and the exact functional bootstrap tests
have the same limit under convergence of the empirical zero fraction. -/
theorem SAP.P001d.WH.W2.T61_L6_proof : SAP.P001d.WH.W2.T61_L6 := by
  intro Ω hΩ μ hμ X hX hCP hSign
  intro f hf hfbd
  obtain ⟨C, hC⟩ := hfbd
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  let L := ∫ z, f z ∂(gaussianReal 0 (1/4))
  let S : ℕ → Ω → ℝ := fun k ω =>
    SAP.P001d.bootstrapTestMean (@SAP.P001d.wholeSignStatistic (k+1))
      (SAP.P001d.firstSample X (k+1) ω) f
  let R : ℕ → Ω → ℝ := fun k ω =>
    SAP.P001d.bootstrapTestMean (@SAP.P001d.wholeRegularStatistic (k+1))
      (SAP.P001d.firstSample X (k+1) ω) f
  let B : ℕ → Set Ω := fun k =>
    {ω | SAP.P001d.wholeEmpiricalCDF (SAP.P001d.firstSample X (k+1) ω) 0 ∉
      Set.Icc (3/8 : ℝ) (5/8)}
  let F : ℕ → Set Ω := fun k =>
    {ω | (1/8 : ℝ) ≤ dist
      (SAP.P001d.wholeEmpiricalCDF (SAP.P001d.firstSample X (k+1) ω) 0) (1/2 : ℝ)}
  have hFar : Tendsto (fun k => AronowAudit.P001.prob μ (F k)) atTop (nhds 0) := by
    have hh := hCP (1/8 : ℝ) (by norm_num)
    simpa only [F, SAP.P001d.Bridge.prob_eq, dist_eq_norm, Real.norm_eq_abs] using hh
  have hBsub : ∀ k, B k ⊆ F k := by
    intro k ω hω
    simp only [B, Set.mem_setOf_eq, Set.mem_Icc, not_and_or, not_le] at hω
    simp only [F, Set.mem_setOf_eq, dist_eq_norm, Real.norm_eq_abs]
    rcases hω with hω | hω
    · have hnonpos : SAP.P001d.wholeEmpiricalCDF
          (SAP.P001d.firstSample X (k+1) ω) 0 - 1/2 ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      linarith
    · have hnonneg : 0 ≤ SAP.P001d.wholeEmpiricalCDF
          (SAP.P001d.firstSample X (k+1) ω) 0 - 1/2 := by linarith
      rw [abs_of_nonneg hnonneg]
      linarith
  have hB : Tendsto (fun k => AronowAudit.P001.prob μ (B k)) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hFar
    · intro k
      unfold AronowAudit.P001.prob
      exact ENNReal.toReal_nonneg
    · intro k
      unfold AronowAudit.P001.prob
      apply ENNReal.toReal_mono (measure_ne_top μ _)
      exact measure_mono (hBsub k)
  have hDiff : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun k => AronowAudit.P001.prob μ {ω | ε ≤ |R k ω-S k ω|}) atTop (nhds 0) := by
    intro ε hε
    have hinv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (nhds 0) := by
      simpa only [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hlim : Tendsto (fun k : ℕ => 2*C*(16/((k : ℝ)+1))) atTop (nhds 0) := by
      have hh := hinv.const_mul (32*C)
      have heq : (fun k : ℕ => 2*C*(16/((k : ℝ)+1))) =
          fun k : ℕ => 32*C * (((k : ℝ)+1)⁻¹) := by
        funext k
        have hk : (0 : ℝ) < (k : ℝ)+1 := by positivity
        field_simp
        <;> ring
      rw [heq]
      simpa using hh
    have hsmall : ∀ᶠ k : ℕ in atTop, 2*C*(16/((k : ℝ)+1)) < ε :=
      hlim.eventually (Iio_mem_nhds hε)
    have hdom (k : ℕ) : AronowAudit.P001.prob μ {ω | ε ≤ |R k ω-S k ω|} ≤
        AronowAudit.P001.prob μ (B k) +
          (if 2*C*(16/((k : ℝ)+1)) < ε then 0 else 1) := by
      by_cases hk : 2*C*(16/((k : ℝ)+1)) < ε
      · have hsub : {ω | ε ≤ |R k ω-S k ω|} ⊆ B k := by
          intro ω hω
          by_contra hnot
          have hp : SAP.P001d.wholeEmpiricalCDF
              (SAP.P001d.firstSample X (k+1) ω) 0 ∈ Set.Icc (3/8 : ℝ) (5/8) := by
            simpa only [B, Set.mem_setOf_eq, not_not] using hnot
          have hn : 0 < k+1 := by omega
          have hc := SAP.P001d.WH.W2.P.T61_L6.bootstrap_test_transfer_bound hn
            (SAP.P001d.firstSample X (k+1) ω) f C hC hp
          have hc' : 2*C*(16/((k : ℝ)+1)) < ε := hk
          have hc'' : 2*C*(16/((k+1 : ℕ) : ℝ)) < ε := by
            simpa only [Nat.cast_add, Nat.cast_one] using hc'
          change ε ≤ |R k ω-S k ω| at hω
          dsimp [R, S] at hω ⊢
          have hbound : |R k ω-S k ω| ≤ 2*C*(16/((k+1 : ℕ) : ℝ)) := hc
          linarith
        unfold AronowAudit.P001.prob
        have hm : μ {ω | ε ≤ |R k ω-S k ω|} ≤ μ (B k) := measure_mono hsub
        have htop : μ (B k) ≠ ∞ := measure_ne_top μ (B k)
        simpa [hk] using (ENNReal.toReal_mono htop hm)
      · have hleft : AronowAudit.P001.prob μ {ω | ε ≤ |R k ω-S k ω|} ≤ 1 := by
          unfold AronowAudit.P001.prob
          exact measureReal_le_one
        have hnonneg : 0 ≤ AronowAudit.P001.prob μ (B k) := by
          unfold AronowAudit.P001.prob
          exact ENNReal.toReal_nonneg
        have hk' : ¬ 2*C*(16/((k : ℝ)+1)) < ε := hk
        calc
          AronowAudit.P001.prob μ {ω | ε ≤ |R k ω-S k ω|} ≤ 1 := hleft
          _ ≤ AronowAudit.P001.prob μ (B k) +
              (if 2*C*(16/((k : ℝ)+1)) < ε then 0 else 1) := by
            simp [hk']
            linarith
    have hG : Tendsto (fun k => AronowAudit.P001.prob μ (B k) +
        (if 2*C*(16/((k : ℝ)+1)) < ε then 0 else 1)) atTop (nhds 0) := by
      apply hB.congr'
      filter_upwards [hsmall] with k hk
      simp [hk]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG
    · intro k
      unfold AronowAudit.P001.prob
      exact ENNReal.toReal_nonneg
    · exact hdom
  have hSignCP : AronowAudit.P001.CP μ S L := by
    have hh := hSign f hf ⟨C, hC⟩
    have hh' : SAP.P001d.CP μ S L := by
      simpa only [S, L] using hh
    exact (SAP.P001d.Bridge.cp_iff μ S L).mp hh'
  have hRCP : AronowAudit.P001.CP μ R L := by
    intro ε hε
    have hs := hSignCP (ε/2) (by linarith)
    have hd := hDiff (ε/2) (by linarith)
    have hpoint (k : ℕ) :
        {ω | ε ≤ |R k ω-L|} ⊆
          {ω | ε/2 ≤ |S k ω-L|} ∪ {ω | ε/2 ≤ |R k ω-S k ω|} := by
      intro ω hω
      change ε ≤ |R k ω-L| at hω
      have ht := abs_sub_le (R k ω) (S k ω) L
      by_cases h₁ : ε/2 ≤ |S k ω-L|
      · exact Or.inl h₁
      · right
        have h₂ : |S k ω-L| < ε/2 := lt_of_not_ge h₁
        have hsum : ε ≤ |R k ω-S k ω| + |S k ω-L| := hω.trans ht
        by_contra hbad
        have h₃ : |R k ω-S k ω| < ε/2 := lt_of_not_ge hbad
        nlinarith
    have hsum (k : ℕ) :
        AronowAudit.P001.prob μ {ω | ε ≤ |R k ω-L|} ≤
          AronowAudit.P001.prob μ {ω | ε/2 ≤ |S k ω-L|} +
          AronowAudit.P001.prob μ {ω | ε/2 ≤ |R k ω-S k ω|} := by
      unfold AronowAudit.P001.prob
      calc
        (μ {ω | ε ≤ |R k ω-L|}).toReal ≤
            (μ ({ω | ε/2 ≤ |S k ω-L|} ∪ {ω | ε/2 ≤ |R k ω-S k ω|})).toReal := by
          apply ENNReal.toReal_mono (measure_ne_top μ _)
          exact measure_mono (hpoint k)
        _ ≤ (μ {ω | ε/2 ≤ |S k ω-L|}).toReal +
              (μ {ω | ε/2 ≤ |R k ω-S k ω|}).toReal := measureReal_union_le _ _
    have hs' : Tendsto (fun k => AronowAudit.P001.prob μ
        {ω | ε/2 ≤ |S k ω-L|}) atTop (nhds 0) := by
      simpa only [dist_eq_norm, Real.norm_eq_abs] using hs
    have hsumTendsto : Tendsto
        (fun k => AronowAudit.P001.prob μ {ω | ε/2 ≤ |S k ω-L|} +
          AronowAudit.P001.prob μ {ω | ε/2 ≤ |R k ω-S k ω|}) atTop (nhds 0) := by
      simpa using hs'.add hd
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsumTendsto
    · intro k
      unfold AronowAudit.P001.prob
      exact ENNReal.toReal_nonneg
    · exact hsum
  have hRcpSap : SAP.P001d.CP μ R L := (SAP.P001d.Bridge.cp_iff μ R L).mpr hRCP
  simpa only [R, L] using hRcpSap
