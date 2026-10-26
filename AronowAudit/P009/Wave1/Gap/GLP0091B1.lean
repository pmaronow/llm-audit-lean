import AronowAudit.P009.P009_NormalCompletion

namespace AronowAudit.P009.Wave1

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory

noncomputable section

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

theorem sparseCoverage_noI_dRMS {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (h : NoInterference E) : dRMS E = 1 := by
  simp [dRMS, SparseCompletion.noI_degree E h, ne_of_gt hn]

theorem sparseCoverage_noI_quad {n : ℕ} (E : Experiment n)
    (h : NoInterference E) (v : Fin n → ℝ) : quadD E v = ∑ i, v i ^ 2 := by
  simp [quadD, SparseCompletion.noI_d E h, mul_ite, ite_mul, pow_two]

theorem sparseCoverage_noI_lambdaMax {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (h : NoInterference E) : lambdaMax E = 1 := by
  let v : Fin n → ℝ := fun i => if i = ⟨0, hn⟩ then 1 else 0
  have hv : (∑ i, v i ^ 2) = 1 := by simp [v, ite_pow]
  have hs : {r | ∃ w : Fin n → ℝ, (∑ i, w i ^ 2) = 1 ∧ r = quadD E w} =
      ({1} : Set ℝ) := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [sparseCoverage_noI_quad E h w, hw]
    · intro hr
      subst r
      exact ⟨v, hv, by rw [sparseCoverage_noI_quad E h v, hv]⟩
  rw [lambdaMax, hs, csSup_singleton]

theorem sparseCoverage_graph (t : ℕ) :
    dAvg (sparseStudy.experiment t) = 1 ∧ dMax (sparseStudy.experiment t) = 1 ∧
    dRMS (sparseStudy.experiment t) = 1 ∧ lambdaMax (sparseStudy.experiment t) = 1 := by
  exact ⟨SparseCompletion.noI_dAvg (sparseStudy.positive t) _
      (SparseCompletion.sparse_NoI_sequence t),
    SparseCompletion.noI_dMax (sparseStudy.positive t) _
      (SparseCompletion.sparse_NoI_sequence t),
    sparseCoverage_noI_dRMS (sparseStudy.positive t) _
      (SparseCompletion.sparse_NoI_sequence t),
    sparseCoverage_noI_lambdaMax (sparseStudy.positive t) _
      (SparseCompletion.sparse_NoI_sequence t)⟩

theorem sparseCoverage_adse (t : ℕ) :
    adse (sparseStudy.experiment t) = 1 / size sparseStudy t := by
  rw [← BernoulliCompletion.eate_eq_adse _ (SparseCompletion.sparse_BER_sequence t),
    SparseCompletion.sparse_eate]

theorem sparseCoverage_effect (t : ℕ) (i : Fin (t + 1)) :
    effect (sparseExperiment (t + 1)) i =
      fun _ => if i.val = 0 then (1 : ℝ) else 0 := by
  funext z
  by_cases hi : i = 0 <;>
    simp [effect, potential, sparseExperiment, fairExperiment, hi, bit]

theorem sparseCoverage_msq (t : ℕ) :
    msq (sparseStudy.experiment t) = 1 / size sparseStudy t := by
  change (∑ i : Fin (t + 1),
    mean (sparseExperiment (t + 1)).design (effect (sparseExperiment (t + 1)) i) ^ 2) /
      (t + 1 : ℕ) = 1 / (t + 1 : ℕ)
  simp only [sparseCoverage_effect, mean_const]
  simp [Fin.sum_univ_succ]

theorem sparseCoverage_sigmaSq (t : ℕ) (i : Fin (t + 1)) :
    sigmaSq (sparseExperiment (t + 1)) i = if i.val = 0 then 1 else 0 := by
  have hm (b : Bool) : marginal (sparseExperiment (t + 1)) i b = 1 / 2 :=
    SparseCompletion.fair_marginal _ _ i b
  unfold sigmaSq
  simp only [hm]
  have hc : (fun z : Assignment (t + 1) =>
      (if z i then (sparseExperiment (t + 1)).outcome i z else 0) / (1 / 2) -
      (if z i then 0 else (sparseExperiment (t + 1)).outcome i z) / (1 / 2)) =
      (fun z => if i.val = 0 then 2 * bit (z i) else 0) := by
    funext z
    by_cases hi : i = 0
    · subst i
      cases hz : z 0 <;> norm_num [sparseExperiment, fairExperiment, bit, hz]
    · cases hz : z i <;> norm_num [sparseExperiment, fairExperiment, bit, hi, hz]
  rw [hc, variance_second_moment]
  by_cases hi : i.val = 0
  · simp only [hi, ite_true]
    change mean (fairLaw (t + 1)) (fun z => (2 * bit (z i)) ^ 2) -
      mean (fairLaw (t + 1)) (fun z => 2 * bit (z i)) ^ 2 = 1
    rw [SparseCompletion.fair_coordinate (t + 1) i (fun b => (2 * bit b) ^ 2),
      SparseCompletion.fair_coordinate (t + 1) i (fun b => 2 * bit b)]
    norm_num [bit]
  · simp [hi, mean_const]

theorem sparseCoverage_sdSigmaSq (t : ℕ) :
    sdSigmaSq (sparseStudy.experiment t) ^ 2 =
      (size sparseStudy t - 1) / size sparseStudy t ^ 2 := by
  change sdSigmaSq (sparseExperiment (t + 1)) ^ 2 =
    ((t + 1 : ℕ) - 1 : ℝ) / (t + 1 : ℕ) ^ 2
  unfold sdSigmaSq
  rw [Real.sq_sqrt (div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    (Nat.cast_nonneg (t + 1)))]
  simp_rw [sparseCoverage_sigmaSq]
  have hs : (∑ j : Fin (t + 1), if j.val = 0 then (1 : ℝ) else 0) = 1 := by
    simp [Fin.sum_univ_succ]
  rw [hs]
  simp [Fin.sum_univ_succ]
  have hn : ((t + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast at hn ⊢
  field_simp
  ring

theorem sparseCoverage_inflations (t : ℕ) (z : Assignment (t + 1)) :
    vAVG (sparseStudy.experiment t) z = vBER (sparseStudy.experiment t) z ∧
    vMAX (sparseStudy.experiment t) z = vBER (sparseStudy.experiment t) z ∧
    vSR (sparseStudy.experiment t) z = vBER (sparseStudy.experiment t) z := by
  simp [vAVG, vMAX, vSR, (sparseCoverage_graph t).1,
    (sparseCoverage_graph t).2.1, (sparseCoverage_graph t).2.2.2]

theorem sparseCoverage_scaled_error (t : ℕ) (z : Assignment (t + 1)) :
    size sparseStudy t / dAvg (sparseStudy.experiment t) *
      (vBER (sparseStudy.experiment t) z -
        var (sparseStudy.experiment t).design (ht (sparseStudy.experiment t))) =
      (4 * bit (z 0) - 1) / size sparseStudy t := by
  rw [(sparseCoverage_graph t).1]
  change (t + 1 : ℕ) / (1 : ℝ) *
    (vBER (sparseExperiment (t + 1)) z -
      var (sparseExperiment (t + 1)).design (ht (sparseExperiment (t + 1)))) =
    (4 * bit (z 0) - 1) / (t + 1 : ℕ)
  rw [(sparse_estimators_finite t z).2, (sparse_moments_finite t).2.1]
  have hn : ((t + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem sparseCoverage_conservative
    (Vhat : (t : ℕ) → Assignment (sparseStudy.N t) → ℝ)
    (hV : ∀ t z, Vhat t z = vBER (sparseStudy.experiment t) z) :
    Conservative sparseStudy Vhat := by
  refine ⟨fun _ => 0, ?_, tendsto_const_nhds⟩
  intro ε hε
  have he : ∀ᶠ t in atTop, 1 / size sparseStudy t < ε :=
    SparseCompletion.inv_size_zero.eventually_lt tendsto_const_nhds hε
  have hz : ∀ᶠ t in atTop,
      prob (sparseStudy.experiment t).design (fun z =>
        size sparseStudy t / dAvg (sparseStudy.experiment t) *
          (Vhat t z - var (sparseStudy.experiment t).design
            (ht (sparseStudy.experiment t))) ≤ -ε) = 0 := by
    filter_upwards [he] with t hsmall
    have hempty : ∀ z, ¬ (size sparseStudy t / dAvg (sparseStudy.experiment t) *
        (Vhat t z - var (sparseStudy.experiment t).design
          (ht (sparseStudy.experiment t))) ≤ -ε) := by
      intro z h
      rw [hV t z, sparseCoverage_scaled_error] at h
      change (4 * bit (z ⟨0, sparseStudy.positive t⟩) - 1) /
        size sparseStudy t ≤ -ε at h
      have hb : 0 ≤ bit (z ⟨0, sparseStudy.positive t⟩) := by
        cases z ⟨0, sparseStudy.positive t⟩ <;> norm_num [bit]
      have hn : 0 ≤ size sparseStudy t := by
        change (0 : ℝ) ≤ (t + 1 : ℕ)
        positivity
      have hl := div_le_div_of_nonneg_right
        (show (-1 : ℝ) ≤ 4 * bit (z ⟨0, sparseStudy.positive t⟩) - 1 by linarith) hn
      have hl' : -(1 / size sparseStudy t) ≤
          (4 * bit (z ⟨0, sparseStudy.positive t⟩) - 1) / size sparseStudy t := by
        simpa only [neg_div] using hl
      linarith
    simp [prob, hempty, mean_const]
  exact (tendsto_congr' hz).2 tendsto_const_nhds

theorem sparseCoverage_equation_error (t : ℕ) (z : Assignment (t + 1)) :
    |size sparseStudy t * (vBER (sparseStudy.experiment t) z -
      var (sparseStudy.experiment t).design (ht (sparseStudy.experiment t))) -
        msq (sparseStudy.experiment t)| = 2 / size sparseStudy t := by
  rw [sparseCoverage_msq]
  change |(t + 1 : ℕ) * (vBER (sparseExperiment (t + 1)) z -
    var (sparseExperiment (t + 1)).design (ht (sparseExperiment (t + 1)))) -
      1 / (t + 1 : ℕ)| = 2 / (t + 1 : ℕ)
  rw [(sparse_estimators_finite t z).2, (sparse_moments_finite t).2.1]
  have hn : 0 < ((t + 1 : ℕ) : ℝ) := by positivity
  have hf : (t + 1 : ℕ) * (4 * bit (z 0) / (t + 1 : ℕ) ^ 2 -
      1 / (t + 1 : ℕ) ^ 2) - 1 / (t + 1 : ℕ) =
      (4 * bit (z 0) - 2) / (t + 1 : ℕ) := by
    field_simp
    ring
  rw [hf, abs_div, abs_of_pos hn]
  congr 1
  cases z 0 <;> norm_num [bit]

theorem sparseCoverage_inProbability :
    InProbability sparseStudy (fun t z => let E := sparseStudy.experiment t
      size sparseStudy t * (vBER E z - var E.design (ht E)) - msq E) := by
  intro ε hε
  have hlim : Tendsto (fun t => 2 / size sparseStudy t) atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop.comp sparseStudy.grows).const_div_atTop 2
  have he := hlim.eventually_lt tendsto_const_nhds hε
  have hz : ∀ᶠ t in atTop,
      prob (sparseStudy.experiment t).design (fun z => ε <
        |size sparseStudy t * (vBER (sparseStudy.experiment t) z -
          var (sparseStudy.experiment t).design (ht (sparseStudy.experiment t))) -
            msq (sparseStudy.experiment t)|) = 0 := by
    filter_upwards [he] with t hsmall
    have hempty : ∀ z, ¬ ε < |size sparseStudy t *
        (vBER (sparseStudy.experiment t) z - var (sparseStudy.experiment t).design
          (ht (sparseStudy.experiment t))) - msq (sparseStudy.experiment t)| := by
      intro z
      rw [sparseCoverage_equation_error]
      exact not_lt_of_ge hsmall.le
    simp [prob, hempty, mean_const]
  exact (tendsto_congr' hz).2 tendsto_const_nhds

theorem sparseCoverage_covered (t : ℕ) (z : Assignment (t + 1)) :
    Covered (ht (sparseStudy.experiment t) z) (eate (sparseStudy.experiment t))
      (vBER (sparseStudy.experiment t) z) (1 / 20) ↔ z 0 = true := by
  rw [Covered, SparseCompletion.sparse_eate]
  change |ht (sparseExperiment (t + 1)) z - 1 / (t + 1 : ℕ)| ≤
    Real.sqrt (vBER (sparseExperiment (t + 1)) z / (1 / 20)) ↔ z 0 = true
  rw [(sparse_estimators_finite t z).1, (sparse_estimators_finite t z).2]
  have hn : 0 < ((t + 1 : ℕ) : ℝ) := by positivity
  cases hz : z 0
  · simp only [bit, hz, Bool.false_eq_true, ite_false, mul_zero, zero_div,
      zero_sub, abs_neg, Real.sqrt_zero, iff_false]
    exact not_le.mpr (abs_pos.mpr (one_div_ne_zero (ne_of_gt hn)))
  · simp only [bit, hz, ite_true, mul_one, iff_true]
    apply Real.abs_le_sqrt
    have hf : (2 / ((t + 1 : ℕ) : ℝ) - 1 / (t + 1 : ℕ)) ^ 2 =
        1 / (t + 1 : ℕ) ^ 2 := by ring
    rw [hf]
    convert div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 80)
      (sq_nonneg (((t + 1 : ℕ) : ℝ))) using 1 <;> ring

theorem sparseCoverage_coverage (t : ℕ) :
    prob (sparseStudy.experiment t).design (fun z =>
      Covered (ht (sparseStudy.experiment t) z) (eate (sparseStudy.experiment t))
        (vBER (sparseStudy.experiment t) z) (1 / 20)) = 1 / 2 := by
  unfold prob
  simp_rw [sparseCoverage_covered]
  change mean (fairLaw (t + 1))
    (fun z => if z 0 = true then (1 : ℝ) else 0) = 1 / 2
  rw [fair_first_coordinate t (fun b => if b = true then (1 : ℝ) else 0)]
  norm_num

theorem sparse_coverage_counterexample_proof :
    RegularSequence sparseStudy 2 4 1 ∧
    (∀ t, Bernoulli (sparseStudy.experiment t) ∧
      NoInterference (sparseStudy.experiment t) ∧
      dAvg (sparseStudy.experiment t) = 1 ∧ dMax (sparseStudy.experiment t) = 1 ∧
      dRMS (sparseStudy.experiment t) = 1 ∧ lambdaMax (sparseStudy.experiment t) = 1) ∧
    Restricted sparseStudy ∧
    (∀ t, let E := sparseStudy.experiment t
      eate E = 1 / size sparseStudy t ∧ adse E = 1 / size sparseStudy t ∧
      msq E = 1 / size sparseStudy t ∧
      var E.design (ht E) = 1 / size sparseStudy t ^ 2 ∧
      mean E.design (vBER E) = 2 / size sparseStudy t ^ 2 ∧
      var E.design (ht E) < mean E.design (vBER E) ∧
      (∀ z, ht E z = 2 * bit (z ⟨0, by simp [sparseStudy]⟩) / size sparseStudy t ∧
        vBER E z = 4 * bit (z ⟨0, by simp [sparseStudy]⟩) / size sparseStudy t ^ 2 ∧
        vAVG E z = vBER E z ∧ vMAX E z = vBER E z ∧ vSR E z = vBER E z) ∧
      sdSigmaSq E ^ 2 = (size sparseStudy t - 1) / size sparseStudy t ^ 2) ∧
    Conservative sparseStudy (fun t => vBER (sparseStudy.experiment t)) ∧
    Conservative sparseStudy (fun t => vAVG (sparseStudy.experiment t)) ∧
    Conservative sparseStudy (fun t => vMAX (sparseStudy.experiment t)) ∧
    Conservative sparseStudy (fun t => vSR (sparseStudy.experiment t)) ∧
    InProbability sparseStudy (fun t z => let E := sparseStudy.experiment t
      size sparseStudy t * (vBER E z - var E.design (ht E)) - msq E) ∧
    (∀ t, prob (sparseStudy.experiment t).design (fun z =>
      Covered (ht (sparseStudy.experiment t) z) (eate (sparseStudy.experiment t))
        (vBER (sparseStudy.experiment t) z) (1/20)) = 1/2) ∧
    (1/2 : ℝ) < 1 - 1/20 := by
  refine ⟨SparseCompletion.sparse_regular_sequence, ?_,
    SparseCompletion.sparse_restricted, ?_,
    sparseCoverage_conservative _ (fun _ _ => rfl),
    sparseCoverage_conservative _ (fun t z => (sparseCoverage_inflations t z).1),
    sparseCoverage_conservative _ (fun t z => (sparseCoverage_inflations t z).2.1),
    sparseCoverage_conservative _ (fun t z => (sparseCoverage_inflations t z).2.2),
    sparseCoverage_inProbability, sparseCoverage_coverage, by norm_num⟩
  · intro t
    exact ⟨SparseCompletion.sparse_BER_sequence t,
      SparseCompletion.sparse_NoI_sequence t, sparseCoverage_graph t⟩
  · intro t
    have hv : var (sparseStudy.experiment t).design (ht (sparseStudy.experiment t)) =
        1 / size sparseStudy t ^ 2 := (sparse_moments_finite t).2.1
    have hm : mean (sparseStudy.experiment t).design (vBER (sparseStudy.experiment t)) =
        2 / size sparseStudy t ^ 2 := (sparse_moments_finite t).2.2
    refine ⟨SparseCompletion.sparse_eate t, sparseCoverage_adse t,
      sparseCoverage_msq t, hv, hm, ?_, ?_, sparseCoverage_sdSigmaSq t⟩
    · rw [hv, hm]
      apply div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2)
      change 0 < (((t + 1 : ℕ) : ℝ)) ^ 2
      positivity
    · intro z
      exact ⟨(sparse_estimators_finite t z).1, (sparse_estimators_finite t z).2,
        sparseCoverage_inflations t z⟩

end
end AronowAudit.P009.Wave1
