import AronowAudit.P013.Wave1.Gap.GP013P012B1
import AronowAudit.P013.Wave1.CorrectedCoverage.N2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.Real.Cardinality

namespace AronowAudit.P013.Wave1

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-!
Finite calculations for the block counterexample. -/

lemma block_finite_end_even (r : ℕ) : blockEnd r % 2 = 0 := by
  by_cases h : r = 0
  · simp [blockEnd, h]
  · simp only [blockEnd, if_neg h]
    exact Nat.dvd_iff_mod_eq_zero.mp
      ((even_iff_two_dvd.mp ((by decide : Even (2 : ℕ)).pow_of_ne_zero
        (by positivity : (2 : ℕ) ^ r ≠ 0))))

lemma block_finite_pair_index (k : ℕ) :
    blockIndex (2*k+1) = blockIndex (2*k+2) := by
  let r := blockIndex (2*k+1)
  have hm : 1 ≤ r ∧ 2*k+1 ≤ blockEnd r :=
    (isLeast_csInf (block_endpoint_bounds_nonempty (2*k+1))).1
  have hi := (block_endpoint_bounds_index_iff (2*k+1) r (by omega) hm.1).1 rfl
  have he := block_finite_end_even r
  have hnext : blockIndex (2*k+2) = r :=
    (block_endpoint_bounds_index_iff _ _ (by omega) hm.1).2 ⟨by omega, by omega⟩
  exact hnext.symm

lemma block_finite_pair_difference (k : ℕ) :
    (blockOutcome (2*k+1) 1 - blockOutcome (2*k+1) 0) +
      (blockOutcome (2*k+2) 1 - blockOutcome (2*k+2) 0) = 0 := by
  have hi := block_finite_pair_index k
  have hm : 1 ≤ blockIndex (2*k+1) ∧ 2*k+1 ≤ blockEnd (blockIndex (2*k+1)) :=
    (isLeast_csInf (block_endpoint_bounds_nonempty (2*k+1))).1
  have hb := ((block_endpoint_bounds_index_iff _ _ (by omega) hm.1).1 rfl).1
  have he := block_finite_end_even (blockIndex (2*k+1)-1)
  have hodd : (2*k+1-blockEnd (blockIndex (2*k+1)-1)-1)%2 = 0 := by omega
  have heven : (2*k+2-blockEnd (blockIndex (2*k+1)-1)-1)%2 ≠ 0 := by omega
  simp only [blockOutcome, ← hi, hodd, heven]
  split_ifs <;> norm_num at *

lemma block_finite_single_difference (i : ℕ) :
    |blockOutcome i 1 - blockOutcome i 0| ≤ 2 := by
  unfold blockOutcome
  split_ifs <;> norm_num

lemma block_finite_even_prefix (k : ℕ) :
    ∑ i ∈ range (2*k), (blockOutcome (i+1) 1 - blockOutcome (i+1) 0) = 0 := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [show 2*(k+1) = (2*k+1)+1 by omega, sum_range_succ, sum_range_succ, hk]
    simpa only [zero_add] using block_finite_pair_difference k

lemma block_finite_target_bound (N : ℕ) :
    |causalEffect (blockPopulation N) 1 0| ≤ 2/(N : ℝ) := by
  have hsum : |∑ i ∈ range N, (blockOutcome (i+1) 1 - blockOutcome (i+1) 0)| ≤ 2 := by
    rcases Nat.mod_two_eq_zero_or_one N with h | h
    · have hn : N = 2*(N/2) := by omega
      rw [hn, block_finite_even_prefix]
      norm_num
    · have hn : N = 2*(N/2)+1 := by omega
      rw [hn, sum_range_succ, block_finite_even_prefix, zero_add]
      exact block_finite_single_difference _
  have hnum : potentialTotal (blockPopulation N) 1 - potentialTotal (blockPopulation N) 0 =
      ∑ i ∈ range N, (blockOutcome (i+1) 1 - blockOutcome (i+1) 0) := by
    simp only [potentialTotal, blockPopulation, ← sum_sub_distrib]
    exact Fin.sum_univ_eq_sum_range (fun i => blockOutcome (i+1) 1 - blockOutcome (i+1) 0) N
  rw [causalEffect, potentialMean, potentialMean, ← sub_div, abs_div,
    show |(N : ℝ)| = (N : ℝ) from abs_of_nonneg (Nat.cast_nonneg N), hnum]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)

lemma block_finite_pairTerm (N : ℕ) (i j : Fin N) (hij : i ≠ j)
    (d e : Fin 2) (z : Fin N → Fin 2) :
    pairTerm (blockPopulation N) i j d e z = 0 := by
  unfold pairTerm
  rw [block_joint N i j hij, block_pi, block_pi]
  norm_num

lemma block_finite_correction (N : ℕ) (d : Fin 2) (z : Fin N → Fin 2) :
    correctionA2 (blockPopulation N) d z = 0 := by
  unfold correctionA2
  apply sum_eq_zero
  intro i _
  apply sum_eq_zero
  intro j hj
  rw [block_joint N i j (ne_of_mem_erase hj).symm]
  norm_num

lemma block_finite_varianceHT (N : ℕ) (d : Fin 2) (z : Fin N → Fin 2) :
    varianceHT (blockPopulation N) d z =
      2 * ∑ i, indicator (blockPopulation N).exposure i d z *
        (blockPopulation N).outcome i d ^ 2 := by
  have hp : (∑ i : Fin N, ∑ j ∈ univ.erase i,
      pairTerm (blockPopulation N) i j d d z) = 0 := by
    apply sum_eq_zero
    intro i _
    apply sum_eq_zero
    intro j hj
    exact block_finite_pairTerm N i j (ne_of_mem_erase hj).symm d d z
  unfold varianceHT
  rw [hp, add_zero, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [block_pi]
  ring

lemma block_finite_observed_square (N : ℕ) (z : Fin N → Fin 2) (i : Fin N) :
    indicator (blockPopulation N).exposure i 1 z * (blockPopulation N).outcome i 1 ^ 2 +
      indicator (blockPopulation N).exposure i 0 z * (blockPopulation N).outcome i 0 ^ 2 =
        observed (blockPopulation N) z i ^ 2 := by
  change (if z i = 1 then (1 : ℝ) else 0) * blockOutcome (i.val+1) 1 ^ 2 +
    (if z i = 0 then 1 else 0) * blockOutcome (i.val+1) 0 ^ 2 =
      blockOutcome (i.val+1) (z i) ^ 2
  generalize z i = t
  fin_cases t <;> norm_num

lemma block_finite_covarianceA (N : ℕ) (z : Fin N → Fin 2) :
    covarianceA (blockPopulation N) 1 0 z = -∑ i, observed (blockPopulation N) z i ^ 2 := by
  have hp : (∑ i : Fin N, ∑ j ∈ univ.erase i,
      if 0 < jointPi (blockPopulation N) i j 1 0 then
        pairTerm (blockPopulation N) i j 1 0 z else 0) = 0 := by
    apply sum_eq_zero
    intro i _
    apply sum_eq_zero
    intro j hj
    rw [block_finite_pairTerm N i j (ne_of_mem_erase hj).symm]
    split_ifs <;> rfl
  have hz (i : Fin N) :
      (∑ j : Fin N, if jointPi (blockPopulation N) i j 1 0 = 0 then
        indicator (blockPopulation N).exposure i 1 z * (blockPopulation N).outcome i 1 ^ 2 /
          (2 * pi (blockPopulation N) i 1) +
        indicator (blockPopulation N).exposure j 0 z * (blockPopulation N).outcome j 0 ^ 2 /
          (2 * pi (blockPopulation N) j 0) else 0) =
        observed (blockPopulation N) z i ^ 2 := by
    rw [sum_eq_single i]
    · rw [jointPi_cross_self _ i 1 0 (by decide), if_pos rfl, block_pi, block_pi]
      norm_num
      exact block_finite_observed_square N z i
    · intro j _ hji
      rw [block_joint N i j hji.symm]
      norm_num
    · simp
  unfold covarianceA
  rw [hp]
  simp_rw [hz]
  ring

lemma block_finite_estimator (N : ℕ) (z : Fin N → Fin 2) :
    effectVariance (blockPopulation N) 1 0 z =
      4/(N : ℝ)^2 * ∑ i, observed (blockPopulation N) z i ^ 2 := by
  have hsum : (∑ i, indicator (blockPopulation N).exposure i 1 z *
      (blockPopulation N).outcome i 1 ^ 2) +
      (∑ i, indicator (blockPopulation N).exposure i 0 z *
      (blockPopulation N).outcome i 0 ^ 2) =
        ∑ i, observed (blockPopulation N) z i ^ 2 := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun i _ => block_finite_observed_square N z i)
  unfold effectVariance
  rw [block_finite_varianceHT, block_finite_varianceHT, block_finite_correction,
    block_finite_correction, block_finite_covarianceA]
  linear_combination (norm := ring_nf) (2/(N : ℝ)^2) * hsum

lemma block_finite_square (N : ℕ) (z : Fin N → Fin 2) (i : Fin N) :
    observed (blockPopulation N) z i ^ 2 =
      1 + if i ∈ blockBUnits N then 1 + 2 * blockSign (i.val+1) * rademacher (z i) else 0 := by
  have hpar := Nat.mod_two_eq_zero_or_one (blockIndex (i.val+1))
  change blockOutcome (i.val+1) (z i) ^ 2 = _
  simp only [blockBUnits, mem_filter, mem_univ, true_and]
  unfold blockOutcome blockSign
  rcases hpar with h | h
  · simp only [h, show ¬ (0 : ℕ) = 1 by decide, if_false, if_true]
    generalize z i = t
    fin_cases t <;> norm_num [rademacher] <;> split_ifs <;> norm_num at *
  · simp [h]

lemma block_finite_scaled (N : ℕ) (hN : 1 ≤ N) (z : Fin N → Fin 2) :
    (N : ℝ)*effectVariance (blockPopulation N) 1 0 z =
      4+4*((blockBUnits N).card : ℝ)/(N : ℝ) +
        8/(N : ℝ)*∑ i ∈ blockBUnits N, blockSign (i.val+1)*rademacher (z i) := by
  classical
  have hsum : (∑ i, observed (blockPopulation N) z i ^ 2) =
      (N : ℝ) + (blockBUnits N).card +
        2 * ∑ i ∈ blockBUnits N, blockSign (i.val+1)*rademacher (z i) := by
    simp_rw [block_finite_square]
    rw [sum_add_distrib]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [← sum_filter, sum_add_distrib]
    simp only [filter_mem_eq_inter, univ_inter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    simp only [mul_assoc]
    rw [← mul_sum]
    ring
  rw [block_finite_estimator, hsum]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp [hn]
  <;> ring

lemma block_finite_sign_square (i : ℕ) : blockSign i ^ 2 = 1 := by
  unfold blockSign
  split_ifs <;> norm_num

lemma block_finite_subset_moments (N : ℕ) :
    expectation (blockDesign N)
      (fun z => ∑ i ∈ blockBUnits N, blockSign (i.val+1)*rademacher (z i)) = 0 ∧
    variance (blockDesign N)
      (fun z => ∑ i ∈ blockBUnits N, blockSign (i.val+1)*rademacher (z i)) =
        ((blockBUnits N).card : ℝ) := by
  classical
  let a : Fin N → ℝ := fun i => if i ∈ blockBUnits N then blockSign (i.val+1) else 0
  have he (z : Fin N → Fin 2) :
      (∑ i ∈ blockBUnits N, blockSign (i.val+1)*rademacher (z i)) =
        ∑ i, rademacher (z i) * a i := by
    simp [a, mul_comm, ite_mul, ← sum_filter]
  simp_rw [he]
  constructor
  · rw [expectation_sum]
    simp only [expectation_mul_const, blockDesign, rademacher_coordinate_mean, zero_mul,
      sum_const_zero]
  · rw [variance, covariance_sum_sum]
    simp_rw [covariance_mul_const, blockDesign, rademacher_coordinate_covariance]
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
    have ha (i : Fin N) : a i * a i = if i ∈ blockBUnits N then 1 else 0 := by
      dsimp [a]
      split_ifs <;> simp_all [← pow_two, block_finite_sign_square]
    simp_rw [ha]
    simp

lemma block_finite_moments (N : ℕ) (hN : 1 ≤ N) :
    expectation (blockDesign N) (fun z => (N : ℝ)*effectVariance (blockPopulation N) 1 0 z) =
      4+4*((blockBUnits N).card : ℝ)/(N : ℝ) ∧
    variance (blockDesign N) (fun z => (N : ℝ)*effectVariance (blockPopulation N) 1 0 z) =
      64*((blockBUnits N).card : ℝ)/(N : ℝ)^2 ∧
    variance (blockDesign N) (fun z => (N : ℝ)*effectVariance (blockPopulation N) 1 0 z) ≤
      64/(N : ℝ) := by
  have hm := block_finite_subset_moments N
  have he : (fun z => (N : ℝ)*effectVariance (blockPopulation N) 1 0 z) =
      fun z => 4+4*((blockBUnits N).card : ℝ)/(N : ℝ) +
        (∑ i ∈ blockBUnits N, blockSign (i.val+1)*rademacher (z i)) * (8/(N : ℝ)) := by
    funext z
    simpa only [mul_comm (8/(N : ℝ))] using block_finite_scaled N hN z
  rw [he]
  have hv : variance (blockDesign N)
      (fun z => 4+4*((blockBUnits N).card : ℝ)/(N : ℝ) +
        (∑ i ∈ blockBUnits N, blockSign (i.val+1)*rademacher (z i)) * (8/(N : ℝ))) =
      64*((blockBUnits N).card : ℝ)/(N : ℝ)^2 := by
    rw [← variance_sub_const (blockDesign N) _
      (4+4*((blockBUnits N).card : ℝ)/(N : ℝ))]
    simp only [add_sub_cancel_left, variance, covariance_mul_const]
    change variance (blockDesign N) _ * _ * _ = _
    rw [hm.2]
    ring
  refine ⟨?_, hv, ?_⟩
  · rw [expectation_add, expectation_const, expectation_mul_const, hm.1]
    ring
  · rw [hv]
    have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hb : ((blockBUnits N).card : ℝ) ≤ N := by
      exact_mod_cast ((card_le_univ (blockBUnits N)).trans_eq (Fintype.card_fin N))
    apply (div_le_iff₀ (sq_pos_of_pos hn)).2
    have hid : (64/(N : ℝ))*(N : ℝ)^2 = 64*(N : ℝ) := by
      field_simp
      <;> ring
    rw [hid]
    linarith

/-!
Changing finite laws and endpoint subsequences. -/

set_option maxHeartbeats 2000000 in
lemma block_asymptotic_sign_clt (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) :
    TendsNormal (fun n => blockDesign (M n))
      (fun n z => (∑ i, rademacher (z i)) / Real.sqrt (M n)) 0 1 := by
  classical
  letI blockAsymptoticMeasurable (n : ℕ) : MeasurableSpace (Fin (M n) → Fin 2) := ⊤
  let μ := fun n => designMeasure (blockDesign (M n))
  letI blockAsymptoticProbability (n : ℕ) : MeasureTheory.IsProbabilityMeasure (μ n) :=
    (CorrectedCoverage.n1_proof (blockDesign (M n))).1
  let X := fun n (i : Fin (M n)) (z : Fin (M n) → Fin 2) => rademacher (z i)
  have hindep (n : ℕ) (A B : Finset (Fin (M n)))
      (hsep : ∀ a ∈ A, ∀ b ∈ B, ¬ a = b) :
      ProbabilityTheory.IndepFun (fun z (i : A) => X n i.1 z)
        (fun z (j : B) => X n j.1 z) (μ n) := by
    have hd : Disjoint A B := disjoint_left.mpr (by
      intro i hi hj
      exact hsep i hi i hj rfl)
    have hn : CorrectedNoEdge (fun i j : Fin (M n) => decide (i=j)) A B := by
      rintro ⟨i, j, hij, hmem⟩
      have heq : i = j := of_decide_eq_true hij
      subst j
      rcases hmem with h | h | h | h
      all_goals exact hsep i h.1 i h.2 rfl
    have hv := CorrectedCoverage.n2_proof (by norm_num : 0 < 2)
      (blockDesign (M n)) (blockPopulation (M n)).exposure A B
      ((block_genuine_dependency (M n)).1 A B hd hn)
    exact hv.comp (measurable_of_finite (fun v (i : A) => rademacher (v i)))
      (measurable_of_finite (fun v (j : B) => rademacher (v j)))
  let D (n : ℕ) : Causalean.Mathlib.Probability.SteinMethod.DepGraph (X n) (μ n) := {
    G := fun i j => i = j
    decG := inferInstance
    refl := fun _ => rfl
    symm := fun _ _ h => h.symm
    meas := fun _ => measurable_of_finite _
    indep := hindep n }
  have hdeg (n : ℕ) (i : Fin (M n)) : ((D n).nbhd i).card ≤ 1 := by
    change (univ.filter (fun j => i = j)).card ≤ 1
    have he : (univ.filter (fun j : Fin (M n) => i = j)) = {i} := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact eq_comm
    rw [he]
    simp
  have hb (n : ℕ) (i : Fin (M n)) (z : Fin (M n) → Fin 2) : |X n i z| ≤ 1 := by
    dsimp [X]
    generalize z i = t
    fin_cases t <;> norm_num [rademacher]
  have hmean (n : ℕ) (i : Fin (M n)) : (∫ z, X n i z ∂μ n) = 0 := by
    rw [integral_designMeasure]
    exact rademacher_coordinate_mean (M n) i
  have hsecond (n : ℕ) :
      (∫ z, (Causalean.Mathlib.Probability.SteinMethod.depSum (X n) z)^2 ∂μ n) = M n := by
    rw [integral_designMeasure]
    have hm : expectation (blockDesign (M n)) (fun z => ∑ i, rademacher (z i)) = 0 := by
      rw [expectation_sum]
      simp only [blockDesign, rademacher_coordinate_mean, sum_const_zero]
    have hv := rademacher_sum_variance (M n)
    change variance (blockDesign (M n)) (fun z => ∑ i, rademacher (z i)) = M n at hv
    unfold variance covariance at hv
    rw [hm] at hv
    simpa only [Causalean.Mathlib.Probability.SteinMethod.depSum, X, pow_two, zero_mul, sub_zero] using hv
  intro x
  have hc := Causalean.Mathlib.Probability.SteinMethod.bounded_degree_dependency_clt
    μ X D 1 hdeg 1 (by norm_num) hb hmean (fun n => (M n : ℝ)) hsecond 1
    (by norm_num) (Eventually.of_forall (by simp)) (by simpa using hM) x
  rw [← ProbabilityTheory.cdf_eq_real] at hc
  apply hc.congr
  intro n
  rw [MeasureTheory.map_measureReal_apply (measurable_of_finite _) measurableSet_Iic]
  exact (CorrectedCoverage.n1_proof (blockDesign (M n))).2 _

lemma block_asymptotic_normalization (N : ℕ) (hN : 1 ≤ N) (z : Fin N → Fin 2) :
    (htEffect (blockPopulation N) 1 0 z - causalEffect (blockPopulation N) 1 0) /
      Real.sqrt (variance (blockDesign N) (htEffect (blockPopulation N) 1 0)) =
        (∑ i, rademacher (z i)) / Real.sqrt (N : ℝ) := by
  rw [block_effect_error, block_true_variance N (by omega), Real.sqrt_div (by norm_num)]
  norm_num
  have hp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs : (Real.sqrt (N : ℝ))^2 = N := Real.sq_sqrt hp.le
  have hn := ne_of_gt hp
  have hr := ne_of_gt (Real.sqrt_pos.mpr hp)
  field_simp [hn, hr]
  rw [hs]
  ring

lemma block_asymptotic_variance_zero (M : ℕ → ℕ) (hp : ∀ n, 1 ≤ M n)
    (hM : Tendsto M atTop atTop) :
    Tendsto (fun n => variance (blockDesign (M n))
      (fun z => (M n : ℝ)*effectVariance (blockPopulation (M n)) 1 0 z)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => variance_nonneg _ _)
    (fun n => (block_finite_moments (M n) (hp n)).2.2)
    ((tendsto_const_div_atTop_nhds_zero_nat (64 : ℝ)).comp hM)

lemma block_asymptotic_endpoint_size (a : ℕ) (ha : 1 ≤ a) :
    Tendsto (fun n => blockEnd (2*n+a)) atTop atTop := by
  apply tendsto_atTop_mono (fun n => ?_) tendsto_id
  exact (by omega : n ≤ 2*n+a) |>.trans
    ((block_endpoint_bounds_nat_le_pow (2*n+a)).trans
      (by simpa only [blockEnd, if_neg (by omega : 2*n+a ≠ 0)] using
        block_endpoint_bounds_nat_le_pow (2^(2*n+a))))

lemma block_asymptotic_endpoint_fraction (a : ℕ) (ha : a = 1 ∨ a = 2) :
    Tendsto (fun n => ((blockBUnits (blockEnd (2*n+a))).card : ℝ) /
      (blockEnd (2*n+a) : ℝ)) atTop (𝓝 (if a = 1 then 0 else 1)) := by
  have hap : 1 ≤ a := by omega
  have hprev : Tendsto (fun n => blockEnd (2*n+a-1)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) tendsto_id
    have hm : n ≤ 2*n+a-1 := by omega
    by_cases hn : n = 0
    · simp [hn]
    · exact hm.trans ((block_endpoint_bounds_nat_le_pow _).trans
        (by simpa [blockEnd, if_neg (by omega : 2*n+a-1 ≠ 0)] using
          block_endpoint_bounds_nat_le_pow (2^(2*n+a-1))))
  have hratio : Tendsto (fun n => (blockEnd (2*n+a-1) : ℝ) /
      (blockEnd (2*n+a) : ℝ)) atTop (𝓝 0) := by
    have hi := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hprev
    apply hi.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [block_endpoint_bounds_ratio _ (by omega)]
    simp only [Function.comp_def, blockEnd, if_neg (by omega : 2*n+a-1 ≠ 0), Nat.cast_pow, Nat.cast_ofNat]
  rcases ha with rfl | rfl
  · simp only [if_pos rfl]
    apply squeeze_zero (fun n => ((block_endpoint_bounds_proof _ (by omega)).1
      (by omega)).1) (fun n => ((block_endpoint_bounds_proof _ (by omega)).1
      (by omega)).2) hratio
  · simp only [show ¬ (2 : ℕ) = 1 by decide, if_false]
    have hh : Tendsto (fun n => 1 - ((blockBUnits (blockEnd (2*n+2))).card : ℝ) /
        (blockEnd (2*n+2) : ℝ)) atTop (𝓝 0) :=
      squeeze_zero (fun n => ((block_endpoint_bounds_proof _ (by omega)).2.1
        (by omega)).1) (fun n => ((block_endpoint_bounds_proof _ (by omega)).2.1
        (by omega)).2) hratio
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub hh using 1 <;> simp

lemma block_asymptotic_endpoint_W (a : ℕ) (ha : a = 1 ∨ a = 2) :
    ConvergesInProbability (fun n => blockDesign (blockEnd (2*n+a)))
      (fun n z => (blockEnd (2*n+a) : ℝ)*effectVariance (blockPopulation (blockEnd (2*n+a))) 1 0 z)
      (if a = 1 then 4 else 8) := by
  have hp (n : ℕ) : 1 ≤ blockEnd (2*n+a) :=
    block_endpoint_bounds_pos _ (by omega)
  apply corrected_studentized_limit_moving_center _ _
    (fun n => expectation (blockDesign (blockEnd (2*n+a)))
      (fun z => (blockEnd (2*n+a) : ℝ)*effectVariance (blockPopulation (blockEnd (2*n+a))) 1 0 z)) _
    (variance_concentration _ _ (block_asymptotic_variance_zero _ hp
      (block_asymptotic_endpoint_size a (by omega))))
  have hh := (tendsto_const_nhds (x := (4 : ℝ))).add ((block_asymptotic_endpoint_fraction a ha).const_mul 4)
  simp only [← mul_div_assoc] at hh
  simp_rw [(block_finite_moments _ (hp _)).1]
  convert hh using 1 <;> rcases ha with rfl | rfl <;> norm_num

lemma block_asymptotic_positive_estimator (N : ℕ) (hN : 1 ≤ N) (z : Fin N → Fin 2) :
    0 < effectVariance (blockPopulation N) 1 0 z := by
  have hfirst : blockIndex 1 = 1 :=
    (block_endpoint_bounds_index_iff 1 1 (by omega) (by omega)).2
      (by norm_num [blockEnd])
  have hone : observed (blockPopulation N) z ⟨0, by omega⟩ ^ 2 = 1 := by
    simp [observed, blockPopulation, blockOutcome, hfirst]
  have hsum : 0 < ∑ i, observed (blockPopulation N) z i ^ 2 := by
    have hh := single_le_sum (s := univ)
      (f := fun i : Fin N => observed (blockPopulation N) z i ^ 2)
      (fun i _ => sq_nonneg _) (mem_univ ⟨0, by omega⟩)
    rw [hone] at hh
    linarith
  rw [block_finite_estimator]
  exact mul_pos (div_pos (by norm_num) (sq_pos_of_pos (by exact_mod_cast (by omega : 0 < N)))) hsum

lemma block_asymptotic_studentize (M : ℕ → ℕ) (hp : ∀ n, 1 ≤ M n)
    (hM : Tendsto M atTop atTop) (s : ℝ) (hs : 0 < s)
    (hW : ConvergesInProbability (fun n => blockDesign (M n))
      (fun n z => (M n : ℝ)*effectVariance (blockPopulation (M n)) 1 0 z) s) :
    ConvergesInProbability (fun n => blockDesign (M n))
      (fun n z => Real.sqrt (variance (blockDesign (M n))
        (htEffect (blockPopulation (M n)) 1 0)/effectVariance (blockPopulation (M n)) 1 0 z))
      (Real.sqrt (4/s)) ∧
    TendsNormal (fun n => blockDesign (M n))
      (fun n z => (htEffect (blockPopulation (M n)) 1 0 z-causalEffect (blockPopulation (M n)) 1 0)/
        Real.sqrt (effectVariance (blockPopulation (M n)) 1 0 z)) 0 ⟨4/s, by positivity⟩ := by
  let P := fun n => blockDesign (M n)
  let W := fun n z => (M n : ℝ)*effectVariance (blockPopulation (M n)) 1 0 z
  let V := fun n => variance (P n) (htEffect (blockPopulation (M n)) 1 0)
  have h4 : ConvergesInProbability P (fun _ _ => (4 : ℝ)) 4 :=
    corrected_studentized_limit_det P (fun _ => 4) 4 tendsto_const_nhds
  have hnorm : TendsNormal P (fun n z =>
      (htEffect (blockPopulation (M n)) 1 0 z - causalEffect (blockPopulation (M n)) 1 0) /
        Real.sqrt (V n)) 0 1 := by
    simpa only [V, P, block_asymptotic_normalization _ (hp _)] using block_asymptotic_sign_clt M hM
  have hvpos (n : ℕ) : 0 < V n := by
    have hn : (0 : ℝ) < M n := by exact_mod_cast (hp n)
    dsimp [V, P]
    rw [block_true_variance _ (by have := hp n; omega)]
    positivity
  have hr (n : ℕ) (z : Fin (M n) → Fin 2) :
      4 / W n z = V n / effectVariance (blockPopulation (M n)) 1 0 z := by
    dsimp [W, V, P]
    rw [block_true_variance _ (by have := hp n; omega), div_div]
  have hd (n : ℕ) (z : Fin (M n) → Fin 2) :
      W n z / 4 = effectVariance (blockPopulation (M n)) 1 0 z / V n := by
    dsimp [W, V, P]
    rw [block_true_variance _ (by have := hp n; omega)]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  have hrconv := corrected_studentized_limit_continuous_pair P
    (fun _ _ => (4 : ℝ)) W 4 s h4 hW (fun p => Real.sqrt (p.1 / p.2))
      (Real.continuous_sqrt.continuousAt.comp
        (continuousAt_fst.div continuousAt_snd (ne_of_gt hs)))
  have hdconv := corrected_studentized_limit_continuous_pair P
    W (fun _ _ => (4 : ℝ)) s 4 hW h4 (fun p => Real.sqrt (p.1 / p.2))
      (Real.continuous_sqrt.continuousAt.comp
        (continuousAt_fst.div continuousAt_snd (by norm_num)))
  refine ⟨by simpa only [hr] using hrconv, ?_⟩
  intro x
  have hx : ConvergesInProbability P (fun _ _ => x) x :=
    corrected_studentized_limit_det P (fun _ => x) x tendsto_const_nhds
  have hth := corrected_studentized_limit_continuous_pair P
    (fun _ _ => x) (fun n z => Real.sqrt (W n z / 4)) x (Real.sqrt (s/4))
    hx hdconv (fun p => p.1*p.2) (continuousAt_fst.mul continuousAt_snd)
  have hc := corrected_studentized_limit_threshold P _
    (fun n z => x*Real.sqrt (W n z / 4)) (x*Real.sqrt (s/4)) hnorm hth
  rw [corrected_studentized_limit_gaussian_cdf 4 s (by norm_num) hs]
  apply hc.congr
  intro n
  unfold probability
  apply sum_congr rfl
  intro z _
  dsimp only
  simp only [hd]
  exact if_congr (corrected_studentized_limit_threshold_identity _ _ _ _ _ (hvpos n)
    (block_asymptotic_positive_estimator _ (hp n) z)).symm rfl rfl

lemma block_asymptotic_probability_unique {L : ℕ → Type*} [∀ n, Fintype (L n)]
    (P : ∀ n, Design (L n)) (X : ∀ n, L n → ℝ) (a b : ℝ)
    (ha : ConvergesInProbability P X a) (hb : ConvergesInProbability P X b) : a = b := by
  by_contra hn
  have hpos : 0 < |a-b| := abs_pos.mpr (sub_ne_zero.mpr hn)
  let ε := |a-b|/3
  have he : 0 < ε := by dsimp [ε]; positivity
  have hl := (ha ε he).add (hb ε he)
  have hall (n : ℕ) : (1 : ℝ) ≤ probability (P n) (fun z => ε < |X n z-a|) +
      probability (P n) (fun z => ε < |X n z-b|) := by
    have hu := corrected_concentration_coverage_union_bound (P n) (fun _ => True)
      (fun z => ε < |X n z-a|) (fun z => ε < |X n z-b|) (by
        intro z _
        by_contra hh
        simp only [not_or, not_lt] at hh
        have ht : |a-b| ≤ |X n z-a| + |X n z-b| := by
          calc
            |a-b| = |(a-X n z)+(X n z-b)| := by congr 1; ring
            _ ≤ |a-X n z|+|X n z-b| := abs_add_le _ _
            _ = _ := by rw [abs_sub_comm a]
        dsimp [ε] at hh
        linarith)
    simpa [probability, (P n).total] using hu
  have hh := ge_of_tendsto hl (Eventually.of_forall hall)
  norm_num at hh


lemma block_asymptotic_index_cofinal (a : ℕ) (ha : 1 ≤ a) :
    Tendsto (fun n => blockEnd (2*n+a)-1) atTop atTop := by
  exact (tendsto_sub_atTop_nat 1).comp (block_asymptotic_endpoint_size a ha)

lemma block_asymptotic_endpoint_transport
    (X : ∀ N : ℕ, (Fin N → Fin 2) → ℝ) (s : ℝ) (a : ℕ) (ha : 1 ≤ a)
    (h : ConvergesInProbability (fun n => blockDesign (n+1)) (fun n => X (n+1)) s) :
    ConvergesInProbability (fun n => blockDesign (blockEnd (2*n+a)))
      (fun n => X (blockEnd (2*n+a))) s := by
  have hrew (n : ℕ) : blockEnd (2*n+a)-1+1 = blockEnd (2*n+a) :=
    Nat.sub_add_cancel (block_endpoint_bounds_pos _ (by omega))
  intro ε hε
  have ht := (h ε hε).comp (block_asymptotic_index_cofinal a ha)
  apply ht.congr
  intro n
  dsimp only [Function.comp_def]
  exact congrArg (fun N => probability (blockDesign N) (fun z => ε < |X N z-s|)) (hrew n)

lemma block_asymptotic_no_distribution
    (X : ∀ N : ℕ, (Fin N → Fin 2) → ℝ)
    (ho : TendsNormal (fun n => blockDesign (blockEnd (2*n+1)))
      (fun n => X (blockEnd (2*n+1))) 0 1)
    (he : TendsNormal (fun n => blockDesign (blockEnd (2*n+2)))
      (fun n => X (blockEnd (2*n+2))) 0 (1/2)) :
    ¬ (∃ μ : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure μ ∧
      TendsDistribution (fun n => blockDesign (n+1)) (fun n => X (n+1)) μ) := by
  rintro ⟨μ, hμ, hfull⟩
  have hc := (ProbabilityTheory.monotone_cdf μ).countable_not_continuousAt
  have hex : ∃ x ∈ Set.Ioo (1 : ℝ) 2, ContinuousAt (ProbabilityTheory.cdf μ) x := by
    by_contra hh
    have hsub : Set.Ioo (1 : ℝ) 2 ⊆ {x | ¬ ContinuousAt (ProbabilityTheory.cdf μ) x} := by
      intro x hx hcont
      exact hh ⟨x, hx, hcont⟩
    have hbad := Cardinal.Real.Ioo_countable_iff.mp (hc.mono hsub)
    norm_num at hbad
  obtain ⟨x, hx, hcx⟩ := hex
  have hrew (a : ℕ) (ha : 1 ≤ a) (n : ℕ) : blockEnd (2*n+a)-1+1 = blockEnd (2*n+a) :=
    Nat.sub_add_cancel (block_endpoint_bounds_pos _ (by omega))
  have hxo : Tendsto (fun n => probability (blockDesign (blockEnd (2*n+1)))
      (fun z => X (blockEnd (2*n+1)) z ≤ x)) atTop (𝓝 (ProbabilityTheory.cdf μ x)) := by
    have ht := (hfull x hcx).comp (block_asymptotic_index_cofinal 1 (by omega))
    apply ht.congr
    intro n
    dsimp only [Function.comp_def]
    exact congrArg (fun N => probability (blockDesign N) (fun z => X N z ≤ x)) (hrew 1 (by omega) n)
  have hxe : Tendsto (fun n => probability (blockDesign (blockEnd (2*n+2)))
      (fun z => X (blockEnd (2*n+2)) z ≤ x)) atTop (𝓝 (ProbabilityTheory.cdf μ x)) := by
    have ht := (hfull x hcx).comp (block_asymptotic_index_cofinal 2 (by omega))
    apply ht.congr
    intro n
    dsimp only [Function.comp_def]
    exact congrArg (fun N => probability (blockDesign N) (fun z => X N z ≤ x)) (hrew 2 (by omega) n)
  have h1 := tendsto_nhds_unique hxo (ho x)
  have h2 := tendsto_nhds_unique hxe (he x)
  have hgauss := corrected_studentized_limit_gaussian_cdf 1 2 (by norm_num) (by norm_num) x
  have hn : (⟨(1 : ℝ)/2, by positivity⟩ : ℝ≥0) = 1/2 := by
    apply Subtype.ext
    change (1 : ℝ)/2 = (1 : ℝ)/2
    rfl
  simp only [div_one, hn] at hgauss
  have h2' : ProbabilityTheory.cdf μ x = normalCDF (x*Real.sqrt 2) := h2.trans hgauss
  have hs : 1 < Real.sqrt 2 := by
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hp := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hlt : x < x * Real.sqrt 2 := by nlinarith [hx.1]
  have hstrict := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf hlt
  change normalCDF x < normalCDF (x*Real.sqrt 2) at hstrict
  exact (ne_of_lt hstrict) (h1.symm.trans h2')

theorem block_asymptotic_counterexample_proof :
    let P := fun n : ℕ => blockDesign (n+1)
    let F := fun n : ℕ => blockPopulation (n+1)
    let W := fun (n : ℕ) z => (n+1 : ℝ)*effectVariance (F n) 1 0 z
    let V := fun n : ℕ => variance (P n) (htEffect (F n) 1 0)
    let T := fun (n : ℕ) z => (htEffect (F n) 1 0 z-causalEffect (F n) 1 0)/
      Real.sqrt (effectVariance (F n) 1 0 z)
    (∀ n : ℕ, (n+1 : ℝ)*V n = 4 ∧ 4 ≤ expectation (P n) (W n)) ∧
    Tendsto (fun n : ℕ => variance (P n) (W n)) atTop (𝓝 0) ∧
    TendsNormal P (fun (n : ℕ) z => (htEffect (F n) 1 0 z-causalEffect (F n) 1 0)/Real.sqrt (V n)) 0 1 ∧
    ¬ (∃ s : ℝ, ConvergesInProbability P W s) ∧
    ¬ (∃ s : ℝ, ConvergesInProbability P
      (fun (n : ℕ) z => Real.sqrt (V n/effectVariance (F n) 1 0 z)) s) ∧
    ¬ (∃ μ : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure μ ∧ TendsDistribution P T μ) ∧
    (let Po := fun n : ℕ => blockDesign (blockEnd (2*n+1))
     let Fo := fun n : ℕ => blockPopulation (blockEnd (2*n+1))
     let Pe := fun n : ℕ => blockDesign (blockEnd (2*n+2))
     let Fe := fun n : ℕ => blockPopulation (blockEnd (2*n+2))
     ConvergesInProbability Po (fun (n : ℕ) z => (blockEnd (2*n+1) : ℝ)*effectVariance (Fo n) 1 0 z) 4 ∧
     ConvergesInProbability Pe (fun (n : ℕ) z => (blockEnd (2*n+2) : ℝ)*effectVariance (Fe n) 1 0 z) 8 ∧
     ConvergesInProbability Po (fun (n : ℕ) z => Real.sqrt
       (variance (Po n) (htEffect (Fo n) 1 0)/effectVariance (Fo n) 1 0 z)) 1 ∧
     ConvergesInProbability Pe (fun (n : ℕ) z => Real.sqrt
       (variance (Pe n) (htEffect (Fe n) 1 0)/effectVariance (Fe n) 1 0 z)) (1/Real.sqrt 2) ∧
     TendsNormal Po (fun (n : ℕ) z => (htEffect (Fo n) 1 0 z-causalEffect (Fo n) 1 0)/
       Real.sqrt (effectVariance (Fo n) 1 0 z)) 0 1 ∧
     TendsNormal Pe (fun (n : ℕ) z => (htEffect (Fe n) 1 0 z-causalEffect (Fe n) 1 0)/
       Real.sqrt (effectVariance (Fe n) 1 0 z)) 0 (1/2)) := by
  dsimp only
  have hoW := block_asymptotic_endpoint_W 1 (Or.inl rfl)
  have heW := block_asymptotic_endpoint_W 2 (Or.inr rfl)
  norm_num only [show (1 : ℕ) = 1 from rfl, ↓reduceIte] at hoW
  simp only [show ¬ (2 : ℕ) = 1 by decide, if_false] at heW
  have hpo (n : ℕ) : 1 ≤ blockEnd (2*n+1) := block_endpoint_bounds_pos _ (by omega)
  have hpe (n : ℕ) : 1 ≤ blockEnd (2*n+2) := block_endpoint_bounds_pos _ (by omega)
  have ho := block_asymptotic_studentize _ hpo
    (block_asymptotic_endpoint_size 1 (by omega)) 4 (by norm_num) hoW
  have he := block_asymptotic_studentize _ hpe
    (block_asymptotic_endpoint_size 2 (by omega)) 8 (by norm_num) heW
  have hor : ConvergesInProbability (fun n => blockDesign (blockEnd (2*n+1)))
      (fun n z => Real.sqrt (variance (blockDesign (blockEnd (2*n+1)))
        (htEffect (blockPopulation (blockEnd (2*n+1))) 1 0) /
          effectVariance (blockPopulation (blockEnd (2*n+1))) 1 0 z)) 1 := by
    convert ho.1 using 1 <;> norm_num
  have her : ConvergesInProbability (fun n => blockDesign (blockEnd (2*n+2)))
      (fun n z => Real.sqrt (variance (blockDesign (blockEnd (2*n+2)))
        (htEffect (blockPopulation (blockEnd (2*n+2))) 1 0) /
          effectVariance (blockPopulation (blockEnd (2*n+2))) 1 0 z)) (1/Real.sqrt 2) := by
    convert he.1 using 1
    norm_num [show (4 : ℝ)/8 = 1/2 by norm_num, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
  have hot : TendsNormal (fun n => blockDesign (blockEnd (2*n+1)))
      (fun n z => (htEffect (blockPopulation (blockEnd (2*n+1))) 1 0 z -
        causalEffect (blockPopulation (blockEnd (2*n+1))) 1 0) /
          Real.sqrt (effectVariance (blockPopulation (blockEnd (2*n+1))) 1 0 z)) 0 1 := by
    have hv : (⟨(4 : ℝ)/4, by positivity⟩ : ℝ≥0) = 1 := by
      apply Subtype.ext
      change (4 : ℝ)/4 = 1
      norm_num
    have hh := ho.2
    rw [hv] at hh
    exact hh
  have het : TendsNormal (fun n => blockDesign (blockEnd (2*n+2)))
      (fun n z => (htEffect (blockPopulation (blockEnd (2*n+2))) 1 0 z -
        causalEffect (blockPopulation (blockEnd (2*n+2))) 1 0) /
          Real.sqrt (effectVariance (blockPopulation (blockEnd (2*n+2))) 1 0 z)) 0 (1/2) := by
    have hv : (⟨(4 : ℝ)/8, by positivity⟩ : ℝ≥0) = 1/2 := by
      apply Subtype.ext
      change (4 : ℝ)/8 = (1 : ℝ)/2
      norm_num
    have hh := he.2
    rw [hv] at hh
    exact hh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hoW, heW, hor, her, hot, het⟩
  · intro n
    constructor
    · rw [block_true_variance _ (by omega)]
      push_cast
      have hn : (n+1 : ℝ) ≠ 0 := by positivity
      field_simp
    · have heq : (fun z => (n+1 : ℝ)*effectVariance (blockPopulation (n+1)) 1 0 z) =
          (fun z => ((n+1 : ℕ) : ℝ)*effectVariance (blockPopulation (n+1)) 1 0 z) := by
        simp only [Nat.cast_add, Nat.cast_one]
      rw [heq, (block_finite_moments (n+1) (by omega)).1]
      have hb : 0 ≤ 4*((blockBUnits (n+1)).card : ℝ)/(n+1 : ℝ) := by positivity
      simpa only [Nat.cast_add, Nat.cast_one] using (le_add_of_nonneg_right hb :
        (4 : ℝ) ≤ 4 + 4*((blockBUnits (n+1)).card : ℝ)/(n+1 : ℝ))
  · simpa only [Nat.cast_add, Nat.cast_one] using
      block_asymptotic_variance_zero (fun n => n+1) (fun n => by omega) (tendsto_add_atTop_nat 1)
  · have heq (n : ℕ) (z : Fin (n+1) → Fin 2) :=
      block_asymptotic_normalization (n+1) (by omega) z
    intro x
    simpa only [heq] using
      (block_asymptotic_sign_clt (fun n => n+1) (tendsto_add_atTop_nat 1) x)
  · rintro ⟨s, hs⟩
    have hs' : ConvergesInProbability (fun n => blockDesign (n+1))
        (fun n z => ((n+1 : ℕ) : ℝ)*effectVariance (blockPopulation (n+1)) 1 0 z) s := by
      simpa only [Nat.cast_add, Nat.cast_one] using hs
    have hso := block_asymptotic_endpoint_transport
      (fun N z => (N : ℝ)*effectVariance (blockPopulation N) 1 0 z) s 1 (by omega) hs'
    have hse := block_asymptotic_endpoint_transport
      (fun N z => (N : ℝ)*effectVariance (blockPopulation N) 1 0 z) s 2 (by omega) hs'
    have h1 := block_asymptotic_probability_unique _ _ _ _ hso hoW
    have h2 := block_asymptotic_probability_unique _ _ _ _ hse heW
    linarith
  · rintro ⟨s, hs⟩
    have hso := block_asymptotic_endpoint_transport
      (fun N z => Real.sqrt (variance (blockDesign N) (htEffect (blockPopulation N) 1 0) /
        effectVariance (blockPopulation N) 1 0 z)) s 1 (by omega) hs
    have hse := block_asymptotic_endpoint_transport
      (fun N z => Real.sqrt (variance (blockDesign N) (htEffect (blockPopulation N) 1 0) /
        effectVariance (blockPopulation N) 1 0 z)) s 2 (by omega) hs
    have h1 := block_asymptotic_probability_unique _ _ _ _ hso hor
    have h2 := block_asymptotic_probability_unique _ _ _ _ hse her
    have hsqrt : 1 < Real.sqrt 2 := by
      have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hp := Real.sqrt_nonneg (2 : ℝ)
      nlinarith
    have hlt : (1 : ℝ)/Real.sqrt 2 < 1 :=
      (div_lt_one (by positivity : (0 : ℝ) < Real.sqrt 2)).2 hsqrt
    linarith
  · exact block_asymptotic_no_distribution
      (fun N z => (htEffect (blockPopulation N) 1 0 z-causalEffect (blockPopulation N) 1 0) /
        Real.sqrt (effectVariance (blockPopulation N) 1 0 z)) hot het

theorem block_finite_identities_proof (N : ℕ) (hN : 1 ≤ N) :
    let F := blockPopulation N
    let P := blockDesign N
    let b := (blockBUnits N).card
    (∀ i d, pi F i d = 1/2 ∧ |F.outcome i d| ≤ 2) ∧
    (∀ i j d e, i ≠ j → jointPi F i j d e = 1/4) ∧
    GenuineDependency P F.exposure (fun i j => decide (i=j)) ∧
    RowBound (fun i j : Fin N => decide (i=j)) 1 ∧
    |causalEffect F 1 0| ≤ 2/(N : ℝ) ∧
    (∀ z, htEffect F 1 0 z-causalEffect F 1 0 =
      (2/(N : ℝ))*∑ i, rademacher (z i)) ∧
    variance P (htEffect F 1 0) = 4/(N : ℝ) ∧
    (∀ z, effectVariance F 1 0 z = 4/(N : ℝ)^2*∑ i, observed F z i ^ 2) ∧
    (∀ z, (N : ℝ)*effectVariance F 1 0 z = 4+4*(b : ℝ)/(N : ℝ) +
      8/(N : ℝ)*∑ i ∈ blockBUnits N, blockSign (i.val+1)*rademacher (z i)) ∧
    expectation P (fun z => (N : ℝ)*effectVariance F 1 0 z) = 4+4*(b : ℝ)/(N : ℝ) ∧
    variance P (fun z => (N : ℝ)*effectVariance F 1 0 z) = 64*(b : ℝ)/(N : ℝ)^2 ∧
    variance P (fun z => (N : ℝ)*effectVariance F 1 0 z) ≤ 64/(N : ℝ) := by
  refine ⟨?_, ?_, (block_genuine_dependency N).1, (block_genuine_dependency N).2.2,
    block_finite_target_bound N, block_effect_error N, block_true_variance N (by omega),
    block_finite_estimator N, block_finite_scaled N hN, block_finite_moments N hN⟩
  · intro i d
    exact ⟨block_pi N i d, (block_outcome_properties (i.val+1)).1 d⟩
  · intro i j d e hij
    exact block_joint N i j hij d e

end

end AronowAudit.P013.Wave1
