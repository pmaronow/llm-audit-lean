import SAP.P045b.Bridge.Part1
import AronowAudit.P045.Wave1.BernoulliUnbiasedness
import AronowAudit.P045.Wave1.DirectVariance
import AronowAudit.P045.Wave1.AllControl
import AronowAudit.P045.Wave1.ClusterSampler

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SAP.P045b.Bridge
open SAP.P045b Finset
open scoped BigOperators
noncomputable section

theorem T22_glue : T22Statement := by
  classical
  refine ⟨AronowAudit.P045.mean_se_counterexample, ?_, ?_, ?_⟩
  · intro n
    have hN : (0 : ℝ) < (n+1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    have hr (z : Assignment (n+1)) :
        varianceWitness n z / (1/(n+1 : ℕ)) = (varianceFactor z)^2 := by
      unfold varianceWitness
      field_simp [ne_of_gt hN]
    have atom (a : ℝ) (b : Bool)
        (ha : ∀ z : Assignment (n+1),
          varianceWitness n z / (1/(n+1 : ℕ)) = a ↔ z 0 = b) :
        prob (bernoulli (1/2)) (fun z : Assignment (n+1) =>
          varianceWitness n z / (1/(n+1 : ℕ)) = a) = 1/2 := by
      unfold prob
      simp_rw [ha]
      change AronowAudit.P045.expect (AronowAudit.P045.bernoulli (1/2))
        (fun z : Assignment (n+1) => if z 0 = b then 1 else 0) = _
      rw [AronowAudit.P045.bernoulli_coordinate_expect (1/2) (0 : Fin (n+1))
        (fun c => if c = b then (1 : ℝ) else 0)]
      cases b <;> norm_num
    refine ⟨atom (1/4) false ?_, atom (9/4) true ?_, ?_, by positivity⟩
    · intro z
      rw [hr]
      unfold varianceFactor
      cases hz : z 0 <;> norm_num
    · intro z
      rw [hr]
      unfold varianceFactor
      cases hz : z 0 <;> norm_num
    · intro z
      refine ⟨hr z, ?_⟩
      rw [show varianceWitness n z - 1/(n+1 : ℕ) =
        ((varianceFactor z)^2-1)/(n+1 : ℕ) by unfold varianceWitness; ring]
      rw [abs_div, abs_of_pos hN]
  · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (5/4)
    simpa [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  · intro n
    have hN : (0 : ℝ) < (n+1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    constructor
    · have hs := (AronowAudit.P045.mean_se_finite_obstruction n).2.2.2.1
      have hv := (AronowAudit.P045.sign_mean_finite_moments n).2
      change expect (bernoulli (1/2)) (seWitness n) = _ at hs
      change variance (bernoulli (1/2)) (signMean (n := n+1)) = _ at hv
      rw [hs, hv, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
    · intro z
      have hr : varianceWitness n z / (1/(n+1 : ℕ)) = (varianceFactor z)^2 := by
        unfold varianceWitness
        field_simp [ne_of_gt hN]
      rw [hr]
      unfold varianceFactor
      cases hz : z 0 <;> norm_num

theorem T23_glue : T23Statement := by
  refine ⟨AronowAudit.P045.table_standard_error_comparison, T22_glue, ?_,
    AronowAudit.P045.nonvanishing_variance_counterexample,
    @AronowAudit.P045.mean_square_bound, ?_⟩
  · intro Ω _ p T Vhat hV hhat hv hs
    exact AronowAudit.P045.absolute_variance_consistency (fun n => toDesign (p n))
      T Vhat hV hhat hv hs
  · intro M hM s hs sd hsd
    have hm : (mean s)^2 ≤ mean (fun i => (s i)^2) :=
      AronowAudit.P045.mean_square_bound hM s hs
    simpa only [div_pow] using
      div_le_div_of_nonneg_right hm (le_of_lt (sq_pos_of_pos hsd))

theorem T24_glue : T24Statement := by
  refine ⟨@AronowAudit.P045.dilated_effect_labels,
    @AronowAudit.P045.total_direct_indirect_identity, ?_⟩
  intro G _ n _ b
  have he (own high : Bool) : regimeMean (dilatedMarginal b) own high =
      (if high then (if own then 2 else 5/4) else (if own then 3/2 else 1))*baselineMean b :=
    AronowAudit.P045.dilated_regime_mean b own high
  dsimp only
  rw [he true true, he false true, he true false, he false false]
  simp only [Bool.false_eq_true, if_false, if_true]
  constructor
  · ring
  constructor <;> ring

theorem T25_glue : T25Statement := by
  intro h
  have key := h 4 (by norm_num) (1/2) (by norm_num) (by norm_num) coMembers true
  have hc : condMean (bernoulli (1/2 : ℝ)) (armExists true)
      (armMean (coMembers (n := 4)) true) = 17/15 :=
    AronowAudit.P045.Wave1.BernoulliUnbiasedness.n1_proof
  have hm : mean (fun i : Fin 4 => marginal (bernoulli (1/2 : ℝ)) coMembers i true) = 3/2 :=
    AronowAudit.P045.Wave1.BernoulliUnbiasedness.n2_proof
  rw [hc, hm] at key
  norm_num at key

theorem T26_glue : T26Statement :=
  AronowAudit.P045.Wave1.direct_variance_as_printed_refuted

theorem T27_glue : T27Statement := by
  intro h
  apply AronowAudit.P045.Wave1.all_control_as_documented_refuted
  intro n A z i
  exact h (fromNetwork A) z i

theorem T29_glue : T29Statement :=
  AronowAudit.P045.Wave1.cluster_sampler_as_documented_refuted

theorem T30_glue : T30Statement := by
  intro n hn Δ _ _ p D y k hk
  exact AronowAudit.P045.ht_unbiased_headline hn (toDesign p) D y k hk

theorem T31_glue : T31Statement := @AronowAudit.P045.contagion_decomposition

theorem T33_glue : T33Statement := by
  intro Ω D N _ _ hN P f y a b hab ha hb
  exact ⟨AronowAudit.P045.ExposureVariance.exact_variance_surplus
      hN (toFiniteDesign P) f y a b hab ha hb,
    AronowAudit.P045.ExposureVariance.exact_variance_conservative
      hN (toFiniteDesign P) f y a b hab ha hb,
    (AronowAudit.P045.ExposureVariance.ht_unbiased
      hN (toFiniteDesign P) f y a b hab ha hb).2.2.2⟩

end
end SAP.P045b.Bridge
