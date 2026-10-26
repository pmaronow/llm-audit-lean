import AronowAudit.P004.Wave1.Gap.TailBIpwThreeType
import AronowAudit.P004.Wave1.Gap.GLP0042B1

/-! The cyclic three-type IPW witness with the remainder computed in the natural numbers. -/
namespace AronowAudit.P004.Wave1

open scoped BigOperators Matrix Topology
open MeasureTheory Filter
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
local instance instDecidableP004T1 (p : Prop) : Decidable p := Classical.propDecidable p

/-- Compute the cyclic type in the natural numbers before coercing to the reals. -/
def threeTypeONat (N : ℕ) (i : Fin N) : Fin 2 → ℝ :=
  ![1, (((i.val % 3 : ℕ) : ℝ) - 1)]

def DecideP004T1_p (t : ℕ) : ℝ := if t = 0 then 1/3 else if t = 1 then 1/2 else 2/3
def DecideP004T1_q (t : ℕ) : ℝ := if t = 1 then 21/20 else 1
def DecideP004T1_o (t : ℕ) : Fin 2 → ℝ := ![1, (t : ℝ)-1]

lemma DecideP004T1_propensities (N : ℕ) :
    propensities (threeTypeONat N) threeTypeTheta = fun i => DecideP004T1_p (i.val%3) := by
  funext i
  have ht : i.val%3 < 3 := Nat.mod_lt _ (by omega)
  unfold propensities threeTypeONat threeTypeTheta dot logistic DecideP004T1_p
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_zero, zero_add]
  interval_cases h : i.val%3 <;>
    norm_num [h, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

lemma DecideP004T1_prob (t : ℕ) : 0 < DecideP004T1_p t ∧ DecideP004T1_p t < 1 := by
  unfold DecideP004T1_p
  split_ifs <;> norm_num

lemma DecideP004T1_overlap : Overlap (fun N => propensities (threeTypeONat N) threeTypeTheta) := by
  refine ⟨1/10, by norm_num, by norm_num, ?_⟩
  intro N i
  dsimp only
  rw [DecideP004T1_propensities]
  unfold DecideP004T1_p
  dsimp only
  split_ifs <;> norm_num

lemma DecideP004T1_bound (N : ℕ) (i : Fin N) (j : Fin 2) : |threeTypeONat N i j| ≤ 1 := by
  have ht : i.val%3 < 3 := Nat.mod_lt _ (by omega)
  fin_cases j <;> simp only [threeTypeONat, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  · norm_num
  · interval_cases h : i.val%3 <;> norm_num [h]

lemma DecideP004T1_gram : ∀ᶠ N : ℕ in atTop, ∀ v : Fin 2 → ℝ,
    (1/3 : ℝ)*(∑ j, (v j)^2) ≤ (∑ i, (dot (threeTypeONat N i) v)^2)/N := by
  filter_upwards [eventually_ge_atTop 6] with N hN v
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hblocks := TailBIpw_blocks_lower N hN
  have hs := TailBIpw_sum_cycle_lower N
    (fun t => (dot (DecideP004T1_o t) v)^2) (fun _ => sq_nonneg _)
  change (N/3 : ℕ)*_ ≤ ∑ i, (dot (threeTypeONat N i) v)^2 at hs
  norm_num [DecideP004T1_o, dot, Fin.sum_univ_two] at hs
  apply (le_div_iff₀ hn).mpr
  simp only [dot, Fin.sum_univ_two]
  have he : 0 ≤ (v 0)^2+(v 1)^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith [mul_nonneg (sub_nonneg.mpr hblocks) he,
    mul_nonneg (Nat.cast_nonneg (N/3) : (0 : ℝ) ≤ (N/3 : ℕ)) (sq_nonneg (v 0))]

lemma DecideP004T1_compact : IsCompact threeTypeParameterSet := by
  have he : threeTypeParameterSet = Set.Icc (fun _ : Fin 2 => (-2 : ℝ)) (fun _ => 2) := by
    ext θ
    simp only [threeTypeParameterSet, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
    exact forall_and
  rw [he]
  exact isCompact_Icc

lemma DecideP004T1_interior : threeTypeTheta ∈ interior threeTypeParameterSet := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hu : Real.log (2 : ℝ) < 2 := (Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    (by norm_num)).trans (by norm_num)
  let S : Set (Fin 2 → ℝ) := {θ | ∀ j, -2 < θ j ∧ θ j < 2}
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (show S ∈ nhds threeTypeTheta from ?_) (show S ⊆ threeTypeParameterSet from ?_)
  · have hopen : IsOpen S := by
      change IsOpen {θ : Fin 2 → ℝ | ∀ j, -2 < θ j ∧ θ j < 2}
      simpa only [Set.setOf_forall, Set.setOf_and] using
        (isOpen_iInter_of_finite fun j : Fin 2 =>
          ((isOpen_lt continuous_const (continuous_apply j)).inter
            (isOpen_lt (continuous_apply j) continuous_const)))
    apply hopen.mem_nhds
    intro j
    fin_cases j <;> norm_num [threeTypeTheta] <;> constructor <;> linarith
  · intro θ hθ j
    exact ⟨(hθ j).1.le, (hθ j).2.le⟩

lemma DecideP004T1_mle_exists : ∃ θhat : ∀ N, Assignment N → Fin 2 → ℝ,
    LogisticConditions threeTypeONat threeTypeTheta threeTypeParameterSet θhat := by
  have hm (N : ℕ) (z : Assignment N) : ∃ θ ∈ threeTypeParameterSet,
      ∀ η ∈ threeTypeParameterSet,
      (∑ i, (bit (z i)*dot (threeTypeONat N i) η - Real.log (1+Real.exp (dot (threeTypeONat N i) η)))) ≤
      (∑ i, (bit (z i)*dot (threeTypeONat N i) θ - Real.log (1+Real.exp (dot (threeTypeONat N i) θ)))) := by
    apply DecideP004T1_compact.exists_isMaxOn (f := fun θ =>
      ∑ i, (bit (z i)*dot (threeTypeONat N i) θ - Real.log (1+Real.exp (dot (threeTypeONat N i) θ))))
      ⟨threeTypeTheta, interior_subset DecideP004T1_interior⟩
    apply Continuous.continuousOn
    apply continuous_finset_sum
    intro i _
    have hd : Continuous (fun θ : Fin 2 → ℝ => dot (threeTypeONat N i) θ) := by
      unfold dot
      fun_prop
    exact (continuous_const.mul hd).sub ((continuous_const.add hd.rexp).log
      (fun θ => ne_of_gt (add_pos (by norm_num) (Real.exp_pos _))))
  choose θhat hθ hmax using hm
  refine ⟨θhat, DecideP004T1_compact, interior_subset DecideP004T1_interior,
    ⟨1, DecideP004T1_bound⟩, ⟨1/3, by norm_num, DecideP004T1_gram⟩, ?_⟩
  exact fun N z => ⟨hθ N z, hmax N z⟩

lemma DecideP004T1_marginal (N : ℕ) (i : Fin N) (a : Bool) :
    marginal (propensities (threeTypeONat N) threeTypeTheta) (threeTypeTable N) i a =
      DecideP004T1_q (i.val%3) := by
  rw [marginal_is_marginalization _ _ _ _ (fun i => by
    rw [DecideP004T1_propensities]; exact DecideP004T1_prob _)]
  exact expect_const _ _

lemma DecideP004T1_beta_arms (N : ℕ) (a : Bool) :
    beta (propensities (threeTypeONat N) threeTypeTheta) (threeTypeTable N) (threeTypeONat N) a =
    beta (propensities (threeTypeONat N) threeTypeTheta) (threeTypeTable N) (threeTypeONat N) true := by
  simp only [beta, DecideP004T1_marginal]

lemma DecideP004T1_homophily (N : ℕ) :
    homophilyQ (propensities (threeTypeONat N) threeTypeTheta)
      (circleAverage (threeTypePopulation N) 0) (fun i => {i})
      (printedFits (propensities (threeTypeONat N) threeTypeTheta)
        (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)) = 0 := by
  rw [TailBIpw_circle]
  simp only [homophilyQ, residualEffect, nodeEffect, printedFits,
    DecideP004T1_marginal, DecideP004T1_beta_arms, sub_self, zero_mul,
    Finset.sum_const_zero, zero_div]

def DecideP004T1_residual (v : Fin 2 → ℝ) (t : ℕ) : ℝ :=
  (DecideP004T1_q t-dot (DecideP004T1_o t) v)/(DecideP004T1_p t*(1-DecideP004T1_p t))

lemma DecideP004T1_augmented (N : ℕ) (z : Assignment N) :
    augmented (propensities (threeTypeONat N) threeTypeTheta) (threeTypeTable N)
      (printedFits (propensities (threeTypeONat N) threeTypeTheta) (threeTypeTable N)
        (threeTypeONat N)) z =
    (∑ i, DecideP004T1_residual
      (beta (propensities (threeTypeONat N) threeTypeTheta) (threeTypeTable N) (threeTypeONat N) true)
      (i.val%3)*(bit (z i)-DecideP004T1_p (i.val%3)))/N := by
  unfold augmented printedFits
  simp only [DecideP004T1_beta_arms, sub_self, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [DecideP004T1_propensities]
  change bit (z i)*(DecideP004T1_q (i.val%3)-dot (DecideP004T1_o (i.val%3)) _)/DecideP004T1_p (i.val%3) -
    (1-bit (z i))*(DecideP004T1_q (i.val%3)-dot (DecideP004T1_o (i.val%3)) _)/(1-DecideP004T1_p (i.val%3)) = _
  unfold DecideP004T1_residual
  have hp := DecideP004T1_prob (i.val%3)
  field_simp [ne_of_gt hp.1, ne_of_gt (sub_pos.mpr hp.2)]
  <;> ring

lemma DecideP004T1_sum_variance {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (a : Fin N → ℝ) (c : ℝ) :
    variance p (fun z => (∑ i, a i*(bit (z i)-p i))/c) =
      (∑ i, p i*(1-p i)*(a i)^2)/c^2 := by
  rw [variance_div]
  have hm : expect p (fun z => ∑ i, a i*(bit (z i)-p i)) = 0 := by
    rw [expect_sum]
    simp only [TailBIpw_centered_mean p hp a, Finset.sum_const_zero]
  unfold variance cov
  rw [hm, zero_mul, sub_zero]
  congr 1
  simpa only [pow_two] using (TailBIpw_centered_moments p hp a Finset.univ).1

/-- Every affine fit leaves a positive residual across the three outcome types.
This bound is independent of the sample-size-dependent projection coefficient. -/
lemma DecideP004T1_residual_lower (v : Fin 2 → ℝ) :
    (9/1300 : ℝ) ≤
      DecideP004T1_p 0*(1-DecideP004T1_p 0)*(DecideP004T1_residual v 0)^2+
      DecideP004T1_p 1*(1-DecideP004T1_p 1)*(DecideP004T1_residual v 1)^2+
      DecideP004T1_p 2*(1-DecideP004T1_p 2)*(DecideP004T1_residual v 2)^2 := by
  norm_num [DecideP004T1_residual, DecideP004T1_p, DecideP004T1_q, DecideP004T1_o,
    dot, Fin.sum_univ_two]
  nlinarith [sq_nonneg (v 0-66/65), sq_nonneg (v 1)]

/-- Complete blocks give the variance lower bound for every sufficiently large
sample size, including rows with one or two leftover types. -/
lemma DecideP004T1_nondegenerate :
    Nondegenerate (fun N => variance (propensities (threeTypeONat N) threeTypeTheta)
      (augmented (propensities (threeTypeONat N) threeTypeTheta)
        (circleAverage (threeTypePopulation N) 0)
        (printedFits (propensities (threeTypeONat N) threeTypeTheta)
          (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)))) := by
  refine ⟨1/1000, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 6] with N hN
  rw [TailBIpw_circle]
  rw [show augmented (propensities (threeTypeONat N) threeTypeTheta) (threeTypeTable N)
    (printedFits (propensities (threeTypeONat N) threeTypeTheta) (threeTypeTable N) (threeTypeONat N)) =
    (fun z => (∑ i, DecideP004T1_residual
      (beta (propensities (threeTypeONat N) threeTypeTheta) (threeTypeTable N) (threeTypeONat N) true)
      (i.val%3)*(bit (z i)-DecideP004T1_p (i.val%3)))/N) from funext (DecideP004T1_augmented N)]
  rw [DecideP004T1_propensities, DecideP004T1_sum_variance _
    (fun i => DecideP004T1_prob _)]
  let v := beta (fun i : Fin N => DecideP004T1_p (i.val%3)) (threeTypeTable N) (threeTypeONat N) true
  let f : ℕ → ℝ := fun t => DecideP004T1_p t*(1-DecideP004T1_p t)*(DecideP004T1_residual v t)^2
  have hf (t : ℕ) : 0 ≤ f t := by
    dsimp [f]
    exact mul_nonneg
      (mul_nonneg (DecideP004T1_prob t).1.le (sub_pos.mpr (DecideP004T1_prob t).2).le) (sq_nonneg _)
  have hs := TailBIpw_sum_cycle_lower N f hf
  have hl := mul_le_mul_of_nonneg_left (DecideP004T1_residual_lower v)
    (Nat.cast_nonneg (N/3) : (0 : ℝ) ≤ (N/3 : ℕ))
  have hb := TailBIpw_blocks_lower N hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsum : (N : ℝ)/1000 ≤ ∑ i : Fin N, f (i.val%3) := by
    change (N/3 : ℕ)*(9/1300 : ℝ) ≤ (N/3 : ℕ)*(f 0+f 1+f 2) at hl
    linarith
  change (1/1000 : ℝ) ≤ (N : ℝ)*((∑ i : Fin N, f (i.val%3))/(N : ℝ)^2)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsum hn.le]

lemma DecideP004T1_cycle_average (K : ℕ) (hK : 0 < K) (f : ℕ → ℝ) :
    (∑ i : Fin (3*K), f (i.val%3))/(3*K : ℕ) = (f 0+f 1+f 2)/3 := by
  rw [TailBIpw_sum_cycle]
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  push_cast
  field_simp
  <;> ring

lemma DecideP004T1_information (K : ℕ) (hK : 0 < K) :
    information (propensities (threeTypeONat (3*K)) threeTypeTheta) (threeTypeONat (3*K)) =
      !![25/108, 0; 0, 4/27] := by
  rw [DecideP004T1_propensities]
  ext a b
  change (∑ i : Fin (3*K), DecideP004T1_p (i.val%3)*(1-DecideP004T1_p (i.val%3))*
    DecideP004T1_o (i.val%3) a*DecideP004T1_o (i.val%3) b)/(3*K : ℕ) = _
  rw [DecideP004T1_cycle_average K hK (fun t =>
    DecideP004T1_p t*(1-DecideP004T1_p t)*DecideP004T1_o t a*DecideP004T1_o t b)]
  fin_cases a <;> fin_cases b <;> norm_num [DecideP004T1_p, DecideP004T1_o]

lemma DecideP004T1_matrix_inverse :
    (!![25/108, 0; 0, 4/27] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![108/25, 0; 0, 27/4] := by
  apply Matrix.inv_eq_right_inv
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

lemma DecideP004T1_beta (K : ℕ) (hK : 0 < K) (a : Bool) :
    beta (propensities (threeTypeONat (3*K)) threeTypeTheta) (threeTypeTable (3*K))
      (threeTypeONat (3*K)) a = ![509/500, 0] := by
  unfold beta
  rw [DecideP004T1_information K hK, DecideP004T1_matrix_inverse]
  simp only [DecideP004T1_marginal]
  rw [DecideP004T1_propensities]
  have hv : (fun j => (∑ i : Fin (3*K), DecideP004T1_q (i.val%3)*DecideP004T1_p (i.val%3)*
      (1-DecideP004T1_p (i.val%3))*threeTypeONat (3*K) i j)/(3*K : ℕ)) = ![509/2160, 0] := by
    funext j
    change (∑ i : Fin (3*K), DecideP004T1_q (i.val%3)*DecideP004T1_p (i.val%3)*
      (1-DecideP004T1_p (i.val%3))*DecideP004T1_o (i.val%3) j)/(3*K : ℕ) = _
    rw [DecideP004T1_cycle_average K hK (fun t =>
      DecideP004T1_q t*DecideP004T1_p t*(1-DecideP004T1_p t)*DecideP004T1_o t j)]
    fin_cases j <;> norm_num [DecideP004T1_p, DecideP004T1_o, DecideP004T1_q]
  rw [hv]
  ext j
  fin_cases j <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma DecideP004T1_gamma (K : ℕ) (hK : 0 < K) :
    scoreGamma (propensities (threeTypeONat (3*K)) threeTypeTheta) (threeTypeTable (3*K))
      (threeTypeONat (3*K)) = ![549/125, 0] := by
  unfold scoreGamma
  rw [DecideP004T1_information K hK, DecideP004T1_matrix_inverse]
  simp only [DecideP004T1_marginal]
  rw [DecideP004T1_propensities]
  have hv : (fun j => (∑ i : Fin (3*K),
      ((1-DecideP004T1_p (i.val%3))*DecideP004T1_q (i.val%3)+
      DecideP004T1_p (i.val%3)*DecideP004T1_q (i.val%3))*threeTypeONat (3*K) i j)/(3*K : ℕ)) = ![61/60, 0] := by
    funext j
    change (∑ i : Fin (3*K),
      ((1-DecideP004T1_p (i.val%3))*DecideP004T1_q (i.val%3)+
      DecideP004T1_p (i.val%3)*DecideP004T1_q (i.val%3))*DecideP004T1_o (i.val%3) j)/(3*K : ℕ) = _
    rw [DecideP004T1_cycle_average K hK (fun t =>
      ((1-DecideP004T1_p t)*DecideP004T1_q t+DecideP004T1_p t*DecideP004T1_q t)*DecideP004T1_o t j)]
    fin_cases j <;> norm_num [DecideP004T1_p, DecideP004T1_o, DecideP004T1_q]
  rw [hv]
  ext j
  fin_cases j <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def DecideP004T1_d (t : ℕ) : ℝ := if t = 1 then 8/25 else -189/1000

lemma DecideP004T1_difference (K : ℕ) (hK : 0 < K) (z : Assignment (3*K)) :
    augmented (propensities (threeTypeONat (3*K)) threeTypeTheta) (threeTypeTable (3*K))
      (printedFits (propensities (threeTypeONat (3*K)) threeTypeTheta)
        (threeTypeTable (3*K)) (threeTypeONat (3*K))) z -
    augmented (propensities (threeTypeONat (3*K)) threeTypeTheta) (threeTypeTable (3*K))
      (scoreFits (propensities (threeTypeONat (3*K)) threeTypeTheta)
        (threeTypeTable (3*K)) (threeTypeONat (3*K))) z =
    (∑ i, DecideP004T1_d (i.val%3)*(bit (z i)-DecideP004T1_p (i.val%3)))/(3*K : ℕ) := by
  unfold augmented
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [scoreFits, printedFits, DecideP004T1_beta K hK, DecideP004T1_gamma K hK,
    sub_self, mul_zero, neg_zero, zero_add]
  rw [DecideP004T1_propensities]
  have ht : i.val%3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases h : i.val%3 <;> cases hz : z i <;>
    norm_num [threeTypeONat, threeTypeTable, dot, Fin.sum_univ_two,
      DecideP004T1_p, DecideP004T1_d, bit, hz, h]

lemma DecideP004T1_normalized_difference (K : ℕ) (hK : 0 < K) (z : Assignment (3*K)) :
    (augmented (propensities (threeTypeONat (3*K)) threeTypeTheta)
      (circleAverage (threeTypePopulation (3*K)) 0)
      (printedFits (propensities (threeTypeONat (3*K)) threeTypeTheta)
        (circleAverage (threeTypePopulation (3*K)) 0) (threeTypeONat (3*K))) z -
    augmented (propensities (threeTypeONat (3*K)) threeTypeTheta)
      (circleAverage (threeTypePopulation (3*K)) 0)
      (scoreFits (propensities (threeTypeONat (3*K)) threeTypeTheta)
        (circleAverage (threeTypePopulation (3*K)) 0) (threeTypeONat (3*K))) z) /
      (Real.sqrt (3*K : ℕ))⁻¹ =
    (∑ i, DecideP004T1_d (i.val%3)*(bit (z i)-DecideP004T1_p (i.val%3)))/Real.sqrt (3*K : ℕ) := by
  rw [TailBIpw_circle, DecideP004T1_difference K hK]
  have hn : 0 < ((3*K : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 3*K)
  have hr := Real.sqrt_pos.mpr hn
  have hs := Real.sq_sqrt hn.le
  field_simp
  <;> rw [hs]

lemma DecideP004T1_normalized_moments (K : ℕ) (hK : 0 < K) :
    let π : Fin (3*K) → ℝ := fun i => DecideP004T1_p (i.val%3)
    let X : Assignment (3*K) → ℝ := fun z =>
      (∑ i, DecideP004T1_d (i.val%3)*(bit (z i)-π i))/Real.sqrt (3*K : ℕ)
    expect π (fun z => (X z)^2) = 10369/750000 ∧
    expect π (fun z => (X z)^4) ≤ 11/1000 := by
  let π : Fin (3*K) → ℝ := fun i => DecideP004T1_p (i.val%3)
  let S : Assignment (3*K) → ℝ := fun z => ∑ i, DecideP004T1_d (i.val%3)*(bit (z i)-π i)
  have hm := TailBIpw_cyclic_moments K DecideP004T1_p DecideP004T1_d DecideP004T1_prob
  have hc2 : DecideP004T1_p 0*(1-DecideP004T1_p 0)*(DecideP004T1_d 0)^2+
      DecideP004T1_p 1*(1-DecideP004T1_p 1)*(DecideP004T1_d 1)^2+
      DecideP004T1_p 2*(1-DecideP004T1_p 2)*(DecideP004T1_d 2)^2 = (10369/250000 : ℝ) := by
    norm_num [DecideP004T1_p, DecideP004T1_d]
  have hc4 : (DecideP004T1_d 0)^2+(DecideP004T1_d 1)^2+(DecideP004T1_d 2)^2 = (86921/500000 : ℝ) := by
    norm_num [DecideP004T1_d]
  dsimp only at hm
  rw [hc2, hc4] at hm
  have hn : 0 < ((3*K : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 3*K)
  have hk : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  have hr := Real.sqrt_pos.mpr hn
  have hs := Real.sq_sqrt hn.le
  have hs4 : (Real.sqrt (3*K : ℕ))^4 = ((3*K : ℕ) : ℝ)^2 := by nlinarith [sq_nonneg (Real.sqrt (3*K : ℕ))]
  constructor
  · change expect π (fun z => (S z/Real.sqrt (3*K : ℕ))^2) = _
    simp_rw [div_pow]
    rw [expect_div, hm.1, hs]
    push_cast
    field_simp
    <;> ring
  · change expect π (fun z => (S z/Real.sqrt (3*K : ℕ))^4) ≤ _
    simp_rw [div_pow]
    rw [expect_div]
    apply (div_le_iff₀ (pow_pos hr 4)).mpr
    rw [hs4]
    calc
      _ ≤ 3*((K : ℝ)*(86921/500000))^2 := hm.2
      _ ≤ (11/1000 : ℝ)*((3*K : ℕ) : ℝ)^2 := by
        push_cast
        nlinarith [sq_nonneg (K : ℝ)]

/-- A second/fourth-moment argument supplies a uniform positive tail.
The pointwise inequality below avoids any distributional approximation. -/
lemma DecideP004T1_tail (K : ℕ) (hK : 0 < K) :
    (1/1000 : ℝ) ≤ prob (fun i : Fin (3*K) => DecideP004T1_p (i.val%3)) (fun z =>
      1/100 < |(∑ i, DecideP004T1_d (i.val%3)*(bit (z i)-DecideP004T1_p (i.val%3)))/
        Real.sqrt (3*K : ℕ)|) := by
  let π : Fin (3*K) → ℝ := fun i => DecideP004T1_p (i.val%3)
  let X : Assignment (3*K) → ℝ := fun z =>
    (∑ i, DecideP004T1_d (i.val%3)*(bit (z i)-π i))/Real.sqrt (3*K : ℕ)
  have hpoint (z : Assignment (3*K)) : (X z)^2 ≤ 1/10000+(X z)^4+
      (if 1/100 < |X z| then 1 else 0) := by
    split_ifs with hz
    · nlinarith [sq_nonneg ((X z)^2-1/2)]
    · have hx := abs_le.mp (le_of_not_gt hz)
      nlinarith [sq_nonneg ((X z)^2)]
  have he := expect_mono π (fun i => DecideP004T1_prob _) _ _ hpoint
  rw [expect_add, expect_add, expect_const] at he
  have hm := DecideP004T1_normalized_moments K hK
  change expect π (fun z => (X z)^2) = _ ∧ expect π (fun z => (X z)^4) ≤ _ at hm
  change (1/1000 : ℝ) ≤ prob π (fun z => 1/100 < |X z|)
  change expect π (fun z => (X z)^2) ≤
    1/10000+expect π (fun z => (X z)^4)+prob π (fun z => 1/100 < |X z|) at he
  rw [hm.1] at he
  linarith [hm.2]

lemma DecideP004T1_difference_not_little :
    ¬ LittleOp (fun N => propensities (threeTypeONat N) threeTypeTheta)
      (fun N z => augmented (propensities (threeTypeONat N) threeTypeTheta)
        (circleAverage (threeTypePopulation N) 0)
        (printedFits (propensities (threeTypeONat N) threeTypeTheta)
          (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)) z -
      augmented (propensities (threeTypeONat N) threeTypeTheta)
        (circleAverage (threeTypePopulation N) 0)
        (scoreFits (propensities (threeTypeONat N) threeTypeTheta)
          (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)) z)
      (fun N => (Real.sqrt N)⁻¹) := by
  intro h
  have hcofinal : Tendsto (fun K : ℕ => 3*K) atTop atTop :=
    tendsto_atTop_mono (fun K => by change K ≤ 3*K; omega) tendsto_id
  have ht := (h (1/100) (by norm_num)).comp hcofinal
  have hsmall := ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/1000))
  obtain ⟨K, hK, hsmall⟩ := ((eventually_gt_atTop 0).and hsmall).exists
  dsimp only [Function.comp_def] at hsmall
  simp only [DecideP004T1_normalized_difference K hK] at hsmall
  rw [DecideP004T1_propensities] at hsmall
  linarith [DecideP004T1_tail K hK]

lemma DecideP004T1_not_little
    (θhat : ∀ N, Assignment N → Fin 2 → ℝ)
    (hlog : LogisticConditions threeTypeONat threeTypeTheta threeTypeParameterSet θhat) :
    ¬ LittleOp (fun N => propensities (threeTypeONat N) threeTypeTheta)
      (fun N z => augmented (propensities (threeTypeONat N) threeTypeTheta)
        (circleAverage (threeTypePopulation N) 0)
        (printedFits (propensities (threeTypeONat N) threeTypeTheta)
          (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)) z -
      fittedIPW (circleAverage (threeTypePopulation N) 0) (threeTypeONat N) (θhat N) z)
      (fun N => (Real.sqrt N)⁻¹) := by
  intro hbad
  let p := fun N => propensities (threeTypeONat N) threeTypeTheta
  let R := fun N => circleAverage (threeTypePopulation N) 0
  let P := fun N => augmented (p N) (R N) (printedFits (p N) (R N) (threeTypeONat N))
  let A := fun N => augmented (p N) (R N) (scoreFits (p N) (R N) (threeTypeONat N))
  let F := fun N => fittedIPW (R N) (threeTypeONat N) (θhat N)
  have hp (N : ℕ) (i : Fin N) : 0 < p N i ∧ p N i < 1 := by
    dsimp [p]
    rw [DecideP004T1_propensities]
    exact DecideP004T1_prob _
  have hcorr : LittleOp p (fun N z => A N z-F N z) (fun N => (Real.sqrt N)⁻¹) :=
    T2_ipw_little threeTypePopulation threeTypeONat threeTypeTheta threeTypeParameterSet θhat
      0 0 le_rfl TailBIpw_spatial (Eventually.of_forall TailBIpw_wellDefined)
      (Eventually.of_forall TailBIpw_local) hlog DecideP004T1_interior DecideP004T1_overlap
  have hneg : InProb p (fun N z => -(A N z-F N z)/(Real.sqrt N)⁻¹) := by
    intro ε hε
    simpa only [neg_div, abs_neg] using hcorr ε hε
  have hsum := T2_inprob_add p hp
    (fun N z => (P N z-F N z)/(Real.sqrt N)⁻¹)
    (fun N z => -(A N z-F N z)/(Real.sqrt N)⁻¹) hbad hneg
  apply DecideP004T1_difference_not_little
  change InProb p (fun N z => (P N z-A N z)/(Real.sqrt N)⁻¹)
  convert hsum using 1
  funext N z
  ring

/-- The cyclic design meets the printed guards, but its printed
linearization differs from the actual compact-set likelihood fit at root-N order. -/
theorem ipw_linearization_counterexample_nat :
    ∃ θhat : ∀ N, Assignment N → Fin 2 → ℝ,
      LogisticConditions threeTypeONat threeTypeTheta threeTypeParameterSet θhat ∧
      threeTypeTheta ∈ interior threeTypeParameterSet ∧
      SpatialLocalConditions threeTypePopulation ∧
      Overlap (fun N => propensities (threeTypeONat N) threeTypeTheta) ∧
      (∀ N : ℕ, 0 < N → WellDefined (threeTypePopulation N) 0) ∧
      (∀ N, homophilyQ (propensities (threeTypeONat N) threeTypeTheta)
        (circleAverage (threeTypePopulation N) 0) (fun i => {i})
        (printedFits (propensities (threeTypeONat N) threeTypeTheta)
          (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)) = 0) ∧
      Nondegenerate (fun N => variance (propensities (threeTypeONat N) threeTypeTheta)
        (augmented (propensities (threeTypeONat N) threeTypeTheta)
          (circleAverage (threeTypePopulation N) 0)
          (printedFits (propensities (threeTypeONat N) threeTypeTheta)
            (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)))) ∧
      ¬ LittleOp (fun N => propensities (threeTypeONat N) threeTypeTheta)
        (fun N z => augmented (propensities (threeTypeONat N) threeTypeTheta)
          (circleAverage (threeTypePopulation N) 0)
          (printedFits (propensities (threeTypeONat N) threeTypeTheta)
            (circleAverage (threeTypePopulation N) 0) (threeTypeONat N)) z -
          fittedIPW (circleAverage (threeTypePopulation N) 0)
            (threeTypeONat N) (θhat N) z)
        (fun N => (Real.sqrt N)⁻¹) := by
  obtain ⟨θhat, hlog⟩ := DecideP004T1_mle_exists
  exact ⟨θhat, hlog, DecideP004T1_interior, TailBIpw_spatial, DecideP004T1_overlap,
    (fun N _ => TailBIpw_wellDefined N), DecideP004T1_homophily,
    DecideP004T1_nondegenerate, DecideP004T1_not_little θhat hlog⟩

end
end AronowAudit.P004.Wave1
