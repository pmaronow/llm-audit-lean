import SAP.P013a.WH.W1.Numerics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013a.WH.W1

open scoped BigOperators Topology NNReal ENNReal
open Filter Finset Bridge
noncomputable section

/-- Two rational standard-normal CDF certificates for the limiting coverage at level
95 percent. Route (under 60 lines): import
`AronowAudit.P010.Wave1.Gap.GLP010P033B5` and apply
`AronowAudit.P010.Wave1.t9_cdf_certificate` at the two displayed rational arguments.
Choose rational inner bounds strictly inside these outer bounds. Prove the finite
polynomial obligations with `norm_num [AronowAudit.P010.Wave1.t9_cdfPoly,
Finset.sum_range_succ]`, with raised heartbeat/recursion limits. The donor controls the
analytic Taylor remainder and the Gaussian normalizer. The quantile and square-root
bracketing, monotonicity and final arithmetic are already proved outside this leaf. -/
def T1_L1 : Prop :=
  95518744722/100000000000 < normalCDF 1.69737860111425 ∧
  normalCDF 1.69737860111427 < 191037489445/200000000000

theorem T1_assembly (h1 : T1_L1) : T1WholeStatement := by
  have hbase : T1Statement := by
    refine ⟨?_, AronowAudit.P013.Wave1.paired_asymptotic_counterexample_proof⟩
    intro r hr
    exact ⟨AronowAudit.P013.paired_finite_hypotheses r hr,
      AronowAudit.P013.Wave1.paired_finite_identities_proof r hr,
      (AronowAudit.P013.pair_variance_score_moments (2*r) (by omega)).1⟩
  refine ⟨hbase, ?_, ?_, ?_⟩
  · intro r _ i
    classical
    let j0 : Fin (2*r) := ⟨2*(i.val/2), by omega⟩
    let j1 : Fin (2*r) := ⟨2*(i.val/2)+1, by omega⟩
    have hne : j0 ≠ j1 := by
      simp only [ne_eq, Fin.ext_iff]
      dsimp [j0, j1]
      omega
    have hindex : ∀ j : Fin (2*r), pairIndex r i = pairIndex r j ↔ j=j0 ∨ j=j1 := by
      intro j
      simp only [pairIndex, Fin.ext_iff]
      dsimp [j0, j1]
      omega
    have hf : univ.filter (fun j : Fin (2*r) => pairIndex r i = pairIndex r j) = {j0,j1} := by
      ext j
      simp [hindex]
    rw [sum_boole, hf]
    simp [hne]
  · dsimp only
    rintro ⟨C, hC, hb⟩
    have hd := hbase.2.2.2.2.2.2.1
    have hg : ∀ᶠ n : ℕ in atTop, C+1 ≤
        variance (pairedDesign (n+2) (by omega))
          (fun z => (2*(n+2) : ℝ)*effectVariance (pairedPopulation (n+2) (by omega)) 1 0 z) :=
      hd.eventually (eventually_ge_atTop (C+1))
    obtain ⟨n, hn, hbig⟩ := (hb.and hg).exists
    have hN : (1 : ℝ) ≤ 2*(n+2) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hpos : (0 : ℝ) < 2*(n+2) := by positivity
    have hdiv : C/(2*(n+2) : ℝ) ≤ C := by
      apply (div_le_iff₀ hpos).mpr
      nlinarith
    linarith
  · have hm : StrictMono normalCDF := AronowAudit.P013.Wave1.CorrectedCoverage.n6_proof.2.1
    have ha := hm.monotone critical_scaled_bracket.1.le
    have hb := hm.monotone critical_scaled_bracket.2.le
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem T2_assembly : T2WholeStatement := by
  refine ⟨whole_coverage, ?_, ?_, ?_, ?_, whole_failure⟩
  · intro S hA
    exact AronowAudit.P013.centered_concentration_implies_lower_tail (toSequence S) hA
  · intro S hv
    exact ⟨vanishes_concentration S hv,
      AronowAudit.P013.vanishing_variance_implies_lower_tail (toSequence S) hv⟩
  · intro S hb h5 b hbp hj
    obtain ⟨hr, hL⟩ := uniform_rate S hb h5 b hbp hj
    obtain ⟨C, hC, hbound⟩ := hr
    have ht : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    exact ⟨⟨C, hC, hbound⟩, vanishes_concentration S (rate_vanishes S _ C hbound ht), hL⟩
  · intro S hb h5 b hm
    obtain ⟨hr, hL⟩ := shrinking_rate S hb h5 b hm
    refine ⟨AronowAudit.P013.Wave1.shrinking_eventual_domain (toSequence S) h5, hr, ?_⟩
    intro ht
    obtain ⟨C, _, hbound⟩ := hr
    exact ⟨vanishes_concentration S (rate_vanishes S _ C hbound ht), hL ht⟩

theorem T8_assembly : T8WholeStatement := by
  intro L _ P estimate Vhat target V hV c hc hv hclt hex hvar
  let Q := fun n => toDesign (P n)
  have hcov := AronowAudit.P013.Wave1.corrected_concentration_coverage_proof
    Q estimate Vhat target V hV c hc hv hclt hex hvar
  refine ⟨hcov.1, ?_, hcov.2, ?_⟩
  · intro ε he _
    exact ⟨fun n => AronowAudit.P013.conservative_relative_lower_tail
      (Q n) (fun z => (n+1 : ℝ)*Vhat n z) ((n+1 : ℝ)*V n) ε
      (mul_pos (by positivity) (hV n).2) he (hex n),
      AronowAudit.P013.relative_lower_tail_tends_zero Q
        (fun (n : ℕ) z => (n+1 : ℝ)*Vhat n z) (fun (n : ℕ) => (n+1 : ℝ)*V n)
        (fun n => mul_pos (by positivity) (hV n).2) c hc hv hex hvar ε he⟩
  · intro s hsc hs
    have hd := AronowAudit.P013.Wave1.corrected_studentized_limit_proof
      Q estimate Vhat target V hV c s hc hsc hv hclt hex hvar hs
    have hspos : 0 < s := hc.trans_le hsc
    have hbad : Tendsto (fun n => probability (P n) (fun z => Vhat n z ≤ 0)) atTop (𝓝 0) := by
      have hh := hd.1 (s/2) (by positivity)
      apply squeeze_zero (fun n => AronowAudit.P013.probability_nonneg (Q n) _)
        (fun n => AronowAudit.P013.probability_mono (Q n) _ _ (fun z hz => ?_)) hh
      have hW : (n+1 : ℝ)*Vhat n z ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hz
      rw [abs_of_nonpos (by linarith : (n+1 : ℝ)*Vhat n z-s ≤ 0)]
      linarith
    have hr : (fun n z => wholeRatioRoot (V n) (Vhat n z)) =
        (fun n z => Real.sqrt (V n/Vhat n z)) := by
      funext n z
      by_cases h : 0 < Vhat n z
      · simp [wholeRatioRoot, h]
      · have hz : V n/Vhat n z ≤ 0 :=
          div_nonpos_of_nonneg_of_nonpos (hV n).2.le (le_of_not_gt h)
        simp [wholeRatioRoot, h, Real.sqrt_eq_zero_of_nonpos hz]
    have ht : (fun n z => wholeStudentized (estimate n z) (target n) (Vhat n z)) =
        (fun n z => (estimate n z-target n)/Real.sqrt (Vhat n z)) := by
      funext n z
      by_cases h : 0 < Vhat n z
      · simp [wholeStudentized, h]
      · simp [wholeStudentized, h, Real.sqrt_eq_zero_of_nonpos (le_of_not_gt h)]
    rw [hr, ht]
    exact ⟨hd.1, hbad, hd.2⟩

theorem T9_assembly : T9WholeStatement := by
  refine ⟨?_, whole_coverage, AronowAudit.P013.studentized_identity, ?_⟩
  · intro S _ h3 h4
    have hm := AronowAudit.P013.both_means_consistent (toSequence S)
      (AronowAudit.P013.condition3_implies_comparison (toSequence S) h3) h4
    refine ⟨hm.1, hm.2, ?_⟩
    have hd := AronowAudit.P013.convergence_difference _ _ _ hm.1 hm.2
    have heq : (fun n z => seqEstimate S n z-seqTarget S n) =
        (fun n z => (htMean (seqPopulation S n) (S.treated n) z-
          potentialMean (seqPopulation S n) (S.treated n))-
          (htMean (seqPopulation S n) (S.control n) z-
            potentialMean (seqPopulation S n) (S.control n))) := by
      funext n z
      unfold seqEstimate seqTarget htEffect causalEffect htMean potentialMean
      ring
    rw [heq]
    exact hd
  · intro Ω _ N K P F hN d hd R hR p0 hm
    have he : expectation (independentProduct P (replicateDesign P R)) (simulatedHTTotal F d R) =
        potentialTotal F d-∑ i, F.outcome i d*(1-pi F i d)^(R+1) :=
      AronowAudit.P013.simulated_expectation (toPopulation F) hN d hd R hR
    have hb := AronowAudit.P013.simulated_bias_repaired (toPopulation F) hN d hd R hR p0 hm
    refine ⟨?_, he, hb.1, ?_⟩
    · simpa only [mul_sub, mul_one, sum_sub_distrib, potentialTotal] using he
    · intro ht
      have h := hb.2 ht
      refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
      intro hs
      have hc := h.2.2.1 hs
      refine ⟨hc.1, hc.2, ?_⟩
      intro b hbp hr
      apply h.2.2.2 b hbp
      simpa only [hc.1, div_one] using hr

theorem T14_assembly : T14WholeStatement := by
  constructor
  · intro Ω _ N K P F _ d hd
    exact ⟨fun hp => AronowAudit.P013.varianceHT_unbiased (toPopulation F) d hp,
      AronowAudit.P013.varianceHT_bias (toPopulation F) d hd,
      AronowAudit.P013.varianceHT_conservative (toPopulation F) d hd⟩
  · intro U Ω _ _ D hp y
    refine ⟨AronowAudit.P027.proposition1 (toSampling D) hp y, ?_,
      AronowAudit.P027.corollary2 (toSampling D) hp y⟩
    intro a b hab
    apply AronowAudit.P027.proposition2 (toSampling D) hp y a b
    intro i j hij
    obtain ⟨ha, hb, he⟩ := hab i j hij
    exact conjugate_of_reciprocal _ _ ha hb he

end
end SAP.P013a.WH.W1
