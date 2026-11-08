import SAP.P004a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W2.P.T9_L4

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1000000

private theorem normalCDF_eq_donor : SAP.P004a.normalCDF = AronowAudit.P004.normalCDF := rfl

private theorem normalCDF_continuous : Continuous SAP.P004a.normalCDF := by
  rw [normalCDF_eq_donor]
  exact AronowAudit.P004.Wave1.GP0042B2b_capped_pd_normalCDF_continuous

private theorem normalCDF_zero : SAP.P004a.normalCDF 0 = (1/2 : ℝ) := by
  have h := AronowAudit.P004.Wave1.GP0042B2b_capped_pd_normalCDF_neg 0
  have hh : SAP.P004a.normalCDF 0 = 1 - SAP.P004a.normalCDF 0 := by
    simpa [normalCDF_eq_donor] using h
  linarith

private theorem fair_prob_mono {N : ℕ} (A B : Assignment N → Prop)
    (hAB : ∀ z, A z → B z) : prob (fun _ => (1/2 : ℝ)) A ≤ prob (fun _ => (1/2 : ℝ)) B :=
  AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_mono _ (fun _ => by norm_num) A B hAB

private theorem fair_prob_congr {N : ℕ} (A B : Assignment N → Prop)
    (hAB : ∀ z, A z ↔ B z) : prob (fun _ => (1/2 : ℝ)) A = prob (fun _ => (1/2 : ℝ)) B :=
  AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_congr _ A B hAB

/-- A CDF limit is unchanged when its cutoff converges to a continuity point. -/
private theorem normalLimit_moving_cutoff
    (U : ∀ N : ℕ, Assignment N → ℝ) (c : ℕ → ℝ) (a : ℝ)
    (hU : ∀ x : ℝ, Tendsto (fun N => prob (fun _ => (1/2 : ℝ))
      (fun z : Assignment N => U N z ≤ x)) atTop (nhds (SAP.P004a.normalCDF x)))
    (hc : Tendsto c atTop (nhds a)) :
    Tendsto (fun N => prob (fun _ => (1/2 : ℝ))
      (fun z : Assignment N => U N z ≤ c N)) atTop (nhds (SAP.P004a.normalCDF a)) := by
  apply tendsto_order.mpr
  constructor
  · intro y hy
    have hnear : ∀ᶠ t in 𝓝 a, y < SAP.P004a.normalCDF t :=
      (tendsto_order.mp normalCDF_continuous.continuousAt.tendsto).1 y hy
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
    let d := a - δ / 2
    have hd : d < a := by dsimp [d]; linarith
    have hdball : d ∈ Metric.ball a δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [d]
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hfixed : y < SAP.P004a.normalCDF d := hball hdball
    have hcut : ∀ᶠ N in atTop, d < c N := (tendsto_order.mp hc).1 d hd
    have hprob : ∀ᶠ N in atTop, y < prob (fun _ => (1/2 : ℝ))
        (fun z : Assignment N => U N z ≤ d) :=
      (tendsto_order.mp (hU d)).1 y hfixed
    filter_upwards [hcut, hprob] with N hcut hprob
    exact hprob.trans_le (fair_prob_mono (fun z => U N z ≤ d)
      (fun z => U N z ≤ c N) (fun z hz => hz.trans hcut.le))
  · intro y hy
    have hnear : ∀ᶠ t in 𝓝 a, SAP.P004a.normalCDF t < y :=
      (tendsto_order.mp normalCDF_continuous.continuousAt.tendsto).2 y hy
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
    let d := a + δ / 2
    have hd : a < d := by dsimp [d]; linarith
    have hdball : d ∈ Metric.ball a δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [d]
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hfixed : SAP.P004a.normalCDF d < y := hball hdball
    have hcut : ∀ᶠ N in atTop, c N < d := (tendsto_order.mp hc).2 d hd
    have hprob : ∀ᶠ N in atTop, prob (fun _ => (1/2 : ℝ))
        (fun z : Assignment N => U N z ≤ d) < y :=
      (tendsto_order.mp (hU d)).2 y hfixed
    filter_upwards [hcut, hprob] with N hcut hprob
    exact (fair_prob_mono (fun z => U N z ≤ c N)
      (fun z => U N z ≤ d) (fun z hz => hz.trans hcut.le)).trans_lt hprob

private theorem logistic_eq_sigmoid : SAP.P004a.logistic = Real.sigmoid := by
  funext t
  unfold SAP.P004a.logistic Real.sigmoid
  rw [Real.exp_neg]
  field_simp
  <;> ring

private theorem logistic_strictMono : StrictMono SAP.P004a.logistic := by
  rw [logistic_eq_sigmoid]
  exact Real.sigmoid_strictMono

private theorem logistic_eq_donor : SAP.P004a.logistic = AronowAudit.P004.logistic := rfl

private theorem signSum_count {N : ℕ} (z : Assignment N) :
    SAP.P004a.boundarySignSum z = 2 * SAP.P004a.armCount z true - N := by
  unfold SAP.P004a.boundarySignSum SAP.P004a.armCount
  have hterm : ∀ i : Fin N,
      2 * SAP.P004a.bit (z i) - 1 = 2 * (if z i = true then (1 : ℝ) else 0) - 1 := by
    intro i
    cases z i <;> simp [SAP.P004a.bit]
  calc
    (∑ i : Fin N, (2 * SAP.P004a.bit (z i) - 1)) =
        ∑ i : Fin N, (2 * (if z i = true then (1 : ℝ) else 0) - 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i
    _ = 2 * (∑ i : Fin N, (if z i = true then (1 : ℝ) else 0)) - N := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          simp

private theorem boundaryLeading_eq_signSum {N : ℕ} (hN : 0 < N) (z : Assignment N) :
    SAP.P004a.boundaryLeading z = 2 * SAP.P004a.boundarySignSum z / N := by
  have hs := signSum_count z
  unfold SAP.P004a.boundaryLeading
  rw [hs]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  field_simp [hn]
  <;> ring

private theorem scaledLeading_eq_signSum {N : ℕ} (hN : 0 < N) (z : Assignment N) :
    Real.sqrt N * SAP.P004a.boundaryLeading z =
      2 * (SAP.P004a.boundarySignSum z / Real.sqrt N) := by
  rw [boundaryLeading_eq_signSum hN z]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hs : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
  field_simp [hn, hs]
  rw [hs2]
  <;> ring

private theorem armCount_bounds {N : ℕ} (z : Assignment N) :
    0 ≤ SAP.P004a.armCount z true ∧ SAP.P004a.armCount z true ≤ N := by
  constructor
  · unfold SAP.P004a.armCount
    apply Finset.sum_nonneg
    intro i hi
    cases z i <;> simp
  · unfold SAP.P004a.armCount
    calc
      (∑ i : Fin N, if z i = true then (1 : ℝ) else 0) ≤ ∑ _i : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum (fun i hi => by cases z i <;> simp)
      _ = N := by simp

private theorem logistic_logit {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    SAP.P004a.logistic (Real.log (q / (1-q))) = q := by
  simpa [logistic_eq_donor] using
    (AronowAudit.P004.Wave1.t9b6_logistic_logit hq0 hq1)

private theorem choice_le_iff_logistic {q t : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ht0 : 0 < t) (ht1 : t < 1) :
    (if q ≤ 1/2 then (0 : ℝ) else
      if SAP.P004a.logistic 1 ≤ q then 1 else Real.log (q/(1-q))) ≤ t ↔
      q ≤ SAP.P004a.logistic t := by
  by_cases hq : q ≤ 1/2
  · have hlog : (1/2 : ℝ) < SAP.P004a.logistic t := by
      have hz : SAP.P004a.logistic 0 = 1/2 := by
        simpa [logistic_eq_donor] using AronowAudit.P004.Wave1.t9b6_logistic_zero
      rw [← hz]
      exact logistic_strictMono ht0
    simp only [if_pos hq]
    constructor
    · intro _
      linarith [hq, hlog]
    · intro _
      linarith
  · have hqhalf : (1/2 : ℝ) < q := lt_of_not_ge hq
    by_cases hcap : SAP.P004a.logistic 1 ≤ q
    · have hlog : SAP.P004a.logistic t < SAP.P004a.logistic 1 := logistic_strictMono ht1
      simp only [if_neg hq, if_pos hcap]
      constructor
      · intro h
        have hf : False := (not_le_of_gt ht1) h
        exact hf.elim
      · intro h
        have hf : False := (not_le_of_gt hlog) (hcap.trans h)
        exact hf.elim
    · have hq_lt_cap : q < SAP.P004a.logistic 1 := lt_of_not_ge hcap
      have hq_lt_one : q < 1 := hq_lt_cap.trans
        (by simpa [logistic_eq_donor] using AronowAudit.P004.Wave1.t9b6_logistic_lt_one 1)
      have hlogit := logistic_logit (by linarith) hq_lt_one
      simp only [if_neg hq, if_neg hcap]
      change Real.log (q/(1-q)) ≤ t ↔ q ≤ SAP.P004a.logistic t
      constructor
      · intro h
        have hh := logistic_strictMono.le_iff_le.mpr h
        simpa only [hlogit] using hh
      · intro h
        have hh : SAP.P004a.logistic (Real.log (q/(1-q))) ≤ SAP.P004a.logistic t := by
          simpa only [hlogit] using h
        exact logistic_strictMono.le_iff_le.mp hh

private theorem boundaryMLE_le_iff_cutoff {N : ℕ} (hN : 0 < N) (z : Assignment N)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (SAP.P004a.boundaryMLE z ≤ t) ↔ SAP.P004a.boundarySignSum z / Real.sqrt N ≤
      Real.sqrt N * (2 * SAP.P004a.logistic t - 1) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  have hs2 := Real.sq_sqrt hn.le
  have ⟨hK0, hKN⟩ := armCount_bounds z
  have hq : 0 ≤ SAP.P004a.armCount z true / (N : ℝ) ∧
      SAP.P004a.armCount z true / (N : ℝ) ≤ 1 := by
    constructor
    · exact div_nonneg hK0 hn.le
    · exact (div_le_iff₀ hn).2 (by simpa using hKN)
  unfold SAP.P004a.boundaryMLE
  dsimp only
  rw [choice_le_iff_logistic hq.1 hq.2 ht0 ht1]
  have hsCount := signSum_count z
  have hT : SAP.P004a.boundarySignSum z / (N : ℝ) =
      2 * (SAP.P004a.armCount z true / (N : ℝ)) - 1 := by
    rw [hsCount]
    field_simp [ne_of_gt hn]
    <;> ring
  constructor
  · intro h
    have h' : SAP.P004a.boundarySignSum z / (N : ℝ) ≤ 2 * SAP.P004a.logistic t - 1 := by
      rw [hT]
      linarith
    have hmul := (div_le_iff₀ hn).mp h'
    apply (div_le_iff₀ hs).2
    have heq : (Real.sqrt (N : ℝ) * (2 * SAP.P004a.logistic t - 1)) *
        Real.sqrt (N : ℝ) = (N : ℝ) * (2 * SAP.P004a.logistic t - 1) := by
      calc
        _ = (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) *
            (2 * SAP.P004a.logistic t - 1) := by ring
        _ = (Real.sqrt (N : ℝ))^2 * (2 * SAP.P004a.logistic t - 1) := by ring
        _ = _ := by rw [hs2]
    rw [heq]
    simpa [mul_comm] using hmul
  · intro h
    have hmul := (div_le_iff₀ hs).mp h
    have hmul' : SAP.P004a.boundarySignSum z ≤ (N : ℝ) * (2 * SAP.P004a.logistic t - 1) := by
      have heq : (Real.sqrt (N : ℝ) * (2 * SAP.P004a.logistic t - 1)) *
          Real.sqrt (N : ℝ) = (N : ℝ) * (2 * SAP.P004a.logistic t - 1) := by
        calc
          _ = (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) *
              (2 * SAP.P004a.logistic t - 1) := by ring
          _ = (Real.sqrt (N : ℝ))^2 * (2 * SAP.P004a.logistic t - 1) := by ring
          _ = _ := by rw [hs2]
      rw [heq] at hmul
      simpa [mul_comm] using hmul
    have h' : SAP.P004a.boundarySignSum z / (N : ℝ) ≤ 2 * SAP.P004a.logistic t - 1 := by
      apply (div_le_iff₀ hn).2
      simpa [mul_comm] using hmul'
    rw [hT] at h'
    linarith

private theorem cutoff_tendsto (x : ℝ) (hx : 0 < x) :
    Tendsto (fun N : ℕ => Real.sqrt N * (2 * SAP.P004a.logistic (x / Real.sqrt N) - 1))
      atTop (nhds (x/2)) := by
  have hder0 : HasDerivAt SAP.P004a.logistic (1/4 : ℝ) 0 := by
    rw [logistic_eq_sigmoid]
    convert Real.hasDerivAt_sigmoid 0 using 1 <;> norm_num
  have hder : HasDerivAt (fun t : ℝ => 2 * SAP.P004a.logistic t - 1) (1/2 : ℝ) 0 := by
    convert (hder0.const_mul 2).sub_const 1 using 1 <;> norm_num
  have hratio : Tendsto (fun t : ℝ => (2 * SAP.P004a.logistic t - 1) / t)
      (𝓝[≠] (0 : ℝ)) (nhds (1/2 : ℝ)) := by
    have hz : SAP.P004a.logistic 0 = 1/2 := by
      simpa [logistic_eq_donor] using AronowAudit.P004.Wave1.t9b6_logistic_zero
    have heq : slope (fun t : ℝ => 2 * SAP.P004a.logistic t - 1) 0 =
        fun t => (2 * SAP.P004a.logistic t - 1) / t := by
      funext t
      simp [slope, hz]
      <;> ring
    simpa only [heq] using hder.tendsto_slope
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have ht : Tendsto (fun N : ℕ => x / Real.sqrt (N : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  have htnz : ∀ᶠ N : ℕ in atTop, x / Real.sqrt (N : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    apply div_ne_zero hx.ne'
    exact ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))
  have htNE : Tendsto (fun N : ℕ => x / Real.sqrt (N : ℝ)) atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, htnz⟩
  have hratioN := hratio.comp htNE
  have hproduct : Tendsto (fun N : ℕ => x *
      ((2 * SAP.P004a.logistic (x / Real.sqrt (N : ℝ)) - 1) / (x / Real.sqrt (N : ℝ))))
      atTop (nhds (x * (1/2))) := tendsto_const_nhds.mul hratioN
  have heq : ∀ᶠ N : ℕ in atTop, Real.sqrt (N : ℝ) *
      (2 * SAP.P004a.logistic (x / Real.sqrt (N : ℝ)) - 1) = x *
      ((2 * SAP.P004a.logistic (x / Real.sqrt (N : ℝ)) - 1) / (x / Real.sqrt (N : ℝ))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hs : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))
    have ht' : x / Real.sqrt (N : ℝ) ≠ 0 := div_ne_zero hx.ne' hs
    field_simp [hs, ht']
    <;> ring
  have hlim : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) *
      (2 * SAP.P004a.logistic (x / Real.sqrt (N : ℝ)) - 1)) atTop (nhds (x * (1/2))) := by
    apply hproduct.congr'
    filter_upwards [heq] with N hN
    exact hN.symm
  convert hlim using 1 <;> ring

private theorem boundaryMLE_nonneg {N : ℕ} (z : Assignment N) :
    0 ≤ SAP.P004a.boundaryMLE z := by
  dsimp only [SAP.P004a.boundaryMLE]
  split_ifs with hq hcap
  · norm_num
  · norm_num
  · have hqhalf : (1/2 : ℝ) < SAP.P004a.armCount z true / N := lt_of_not_ge hq
    have hq_lt_one : SAP.P004a.armCount z true / N < 1 :=
      (lt_of_not_ge hcap).trans (by
        simpa [logistic_eq_donor] using AronowAudit.P004.Wave1.t9b6_logistic_lt_one 1)
    have hlog : 0 ≤ Real.log ((SAP.P004a.armCount z true / N) /
        (1-SAP.P004a.armCount z true / N)) := by
      apply Real.log_nonneg
      apply (le_div_iff₀ (sub_pos.mpr hq_lt_one)).2
      linarith
    exact hlog

private theorem mle_zero_iff_count {N : ℕ} (hN : 0 < N) (z : Assignment N) :
    SAP.P004a.boundaryMLE z = 0 ↔ SAP.P004a.armCount z true / (N : ℝ) ≤ 1/2 := by
  dsimp only [SAP.P004a.boundaryMLE]
  split_ifs with hq hcap
  · constructor
    · intro _
      nlinarith [hq]
    · intro _
      rfl
  · constructor
    · intro h
      norm_num at h
    · intro hh
      exact (hq hh).elim
  · have hqhalf : (1/2 : ℝ) < SAP.P004a.armCount z true / (N : ℝ) := lt_of_not_ge hq
    have hq_lt_one : SAP.P004a.armCount z true / (N : ℝ) < 1 :=
      (lt_of_not_ge hcap).trans (by
        simpa [logistic_eq_donor] using AronowAudit.P004.Wave1.t9b6_logistic_lt_one 1)
    have hratio : 1 < (SAP.P004a.armCount z true / (N : ℝ)) /
        (1-SAP.P004a.armCount z true / (N : ℝ)) := by
      -- The likelihood ratio is larger than one because q exceeds one half.
      apply (lt_div_iff₀ (sub_pos.mpr hq_lt_one)).2
      linarith
    have hlog : 0 < Real.log ((SAP.P004a.armCount z true / (N : ℝ)) /
        (1-SAP.P004a.armCount z true / (N : ℝ))) := by
      apply Real.log_pos
      exact hratio
    constructor
    · intro heq
      exact False.elim ((ne_of_gt hlog) heq)
    · intro hh
      exact (hq hh).elim

end
end SAP.P004a.WH.W2.P.T9_L4

open SAP.P004a.WH.W2.P.T9_L4
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology

theorem SAP.P004a.WH.W2.T9_L4_proof : SAP.P004a.WH.W2.T9_L4 := by
  intro hCLT
  have hlead : ∀ x : ℝ, Tendsto (fun N => SAP.P004a.prob (fun _ => (1/2 : ℝ))
      (fun z : SAP.P004a.Assignment N => Real.sqrt N * SAP.P004a.boundaryLeading z ≤ x)) atTop
      (nhds (SAP.P004a.normalCDF (x/2))) := by
    intro x
    have hseq : ∀ᶠ N : ℕ in atTop, ∀ z : SAP.P004a.Assignment N,
        Real.sqrt N * SAP.P004a.boundaryLeading z ≤ x ↔
          SAP.P004a.boundarySignSum z / Real.sqrt N ≤ x/2 := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN z
      rw [scaledLeading_eq_signSum hN z]
      constructor <;> intro h <;> nlinarith
    have hprob : ∀ᶠ N : ℕ in atTop,
        SAP.P004a.prob (fun _ => (1/2 : ℝ))
          (fun z : SAP.P004a.Assignment N => SAP.P004a.boundarySignSum z / Real.sqrt N ≤ x/2) =
        SAP.P004a.prob (fun _ => (1/2 : ℝ))
          (fun z : SAP.P004a.Assignment N => Real.sqrt N * SAP.P004a.boundaryLeading z ≤ x) := by
      filter_upwards [hseq] with N hN
      exact (fair_prob_congr _ _ hN).symm
    exact Filter.Tendsto.congr' hprob (hCLT (x/2))
  have hmle : ∀ x : ℝ, x ≠ 0 → Tendsto
      (fun N => SAP.P004a.prob (fun _ => (1/2 : ℝ)) (fun z : SAP.P004a.Assignment N =>
        Real.sqrt N * SAP.P004a.boundaryMLE z ≤ x)) atTop
        (nhds (if x < 0 then 0 else SAP.P004a.normalCDF (x/2))) := by
    intro x hx
    by_cases hneg : x < 0
    · have hzero : ∀ N : ℕ, SAP.P004a.prob (fun _ => (1/2 : ℝ))
          (fun z : SAP.P004a.Assignment N => Real.sqrt N * SAP.P004a.boundaryMLE z ≤ x) = 0 := by
        intro N
        have hcongr : ∀ z : SAP.P004a.Assignment N,
            (Real.sqrt N * SAP.P004a.boundaryMLE z ≤ x) ↔ False := by
          intro z
          have hprod : 0 ≤ Real.sqrt (N : ℝ) * SAP.P004a.boundaryMLE z :=
            mul_nonneg (Real.sqrt_nonneg _) (boundaryMLE_nonneg z)
          constructor
          · intro hh
            linarith
          · intro hh
            exact False.elim hh
        rw [fair_prob_congr _ (fun _ => False) hcongr]
        simp [SAP.P004a.prob, SAP.P004a.expect]
      have heq : (fun N : ℕ => SAP.P004a.prob (fun _ => (1/2 : ℝ))
          (fun z : SAP.P004a.Assignment N => Real.sqrt N * SAP.P004a.boundaryMLE z ≤ x)) = fun _ => 0 :=
        funext hzero
      rw [heq]
      simpa [hneg] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    · have hpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hx)
      let cutoff : ℕ → ℝ := fun N => Real.sqrt N *
        (2 * SAP.P004a.logistic (x / Real.sqrt N) - 1)
      have hcut := cutoff_tendsto x hpos
      have htime : Tendsto (fun N : ℕ => x / Real.sqrt (N : ℝ)) atTop (nhds 0) := by
        have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
          Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
        have hinv := tendsto_inv_atTop_zero.comp hsqrt
        simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
      have htlt : ∀ᶠ N : ℕ in atTop, x / Real.sqrt (N : ℝ) < 1 :=
        (tendsto_order.mp htime).2 1 (by norm_num)
      have hevent : ∀ᶠ N : ℕ in atTop, ∀ z : SAP.P004a.Assignment N,
          (Real.sqrt N * SAP.P004a.boundaryMLE z ≤ x) ↔
            (SAP.P004a.boundarySignSum z / Real.sqrt N ≤ cutoff N) := by
        filter_upwards [eventually_gt_atTop (0 : ℕ), htlt] with N hN ht z
        have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
        have ht0 : 0 < x / Real.sqrt (N : ℝ) := div_pos hpos hs
        have hMLE := boundaryMLE_le_iff_cutoff hN z ht0 ht
        have hscale : (Real.sqrt (N : ℝ) * SAP.P004a.boundaryMLE z ≤ x) ↔
            SAP.P004a.boundaryMLE z ≤ x / Real.sqrt (N : ℝ) := by
          constructor
          · intro hh
            apply (le_div_iff₀ hs).2
            nlinarith
          · intro hh
            have hh' := (le_div_iff₀ hs).1 hh
            nlinarith
        exact hscale.trans hMLE
      have hmove := normalLimit_moving_cutoff
        (fun N z => SAP.P004a.boundarySignSum z / Real.sqrt N) cutoff (x/2) hCLT hcut
      have hprob : ∀ᶠ N : ℕ in atTop,
          SAP.P004a.prob (fun _ => (1/2 : ℝ))
            (fun z : SAP.P004a.Assignment N => SAP.P004a.boundarySignSum z / Real.sqrt N ≤ cutoff N) =
          SAP.P004a.prob (fun _ => (1/2 : ℝ))
            (fun z : SAP.P004a.Assignment N => Real.sqrt N * SAP.P004a.boundaryMLE z ≤ x) := by
        filter_upwards [hevent] with N hN
        exact (fair_prob_congr _ _ hN).symm
      have hresult := Filter.Tendsto.congr' hprob hmove
      have htarget : (if x < 0 then (0 : ℝ) else SAP.P004a.normalCDF (x/2)) =
          SAP.P004a.normalCDF (x/2) := if_neg (not_lt_of_gt hpos)
      rw [htarget]
      exact hresult
  have hzero : Tendsto (fun N => SAP.P004a.prob (fun _ => (1/2 : ℝ))
      (fun z : SAP.P004a.Assignment N => SAP.P004a.boundaryMLE z = 0)) atTop (nhds (1/2 : ℝ)) := by
    have hevent : ∀ᶠ N : ℕ in atTop, ∀ z : SAP.P004a.Assignment N,
        (SAP.P004a.boundaryMLE z = 0) ↔ SAP.P004a.boundarySignSum z / Real.sqrt N ≤ 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN z
      have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
      have hcount := mle_zero_iff_count hN z
      have hT : SAP.P004a.armCount z true / (N : ℝ) ≤ 1/2 ↔
          SAP.P004a.boundarySignSum z ≤ 0 := by
        rw [signSum_count]
        constructor <;> intro hh <;> field_simp [ne_of_gt hn] at hh ⊢ <;> linarith
      rw [hcount, hT]
      rw [div_le_iff₀ hs]
      constructor <;> intro hh <;> linarith
    have hprobEq : ∀ᶠ N : ℕ in atTop,
        SAP.P004a.prob (fun _ => (1/2 : ℝ))
          (fun z : SAP.P004a.Assignment N => SAP.P004a.boundarySignSum z / Real.sqrt N ≤ 0) =
        SAP.P004a.prob (fun _ => (1/2 : ℝ))
          (fun z : SAP.P004a.Assignment N => SAP.P004a.boundaryMLE z = 0) := by
      filter_upwards [hevent] with N hN
      exact (fair_prob_congr _ _ hN).symm
    have hprob := Filter.Tendsto.congr' hprobEq (hCLT 0)
    simpa [normalCDF_zero] using hprob
  exact ⟨hlead, hmle, hzero⟩
