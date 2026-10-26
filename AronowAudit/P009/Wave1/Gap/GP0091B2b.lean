import AronowAudit.P009.P009_BernoulliCompletion
import AronowAudit.P009.P009_CompleteConditional
import Mathlib.Analysis.Real.Sqrt

/-!
P009-T43: bounded average dependence gives the root-n rate for either design.

Finite permutation averaging supplies the disjoint-mask second-moment bound.
-/

namespace AronowAudit.P009.Wave1

open scoped BigOperators
open Filter

noncomputable section

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000

/-- The average outgoing interference count is nonnegative for every size. -/
theorem GP0091B2b_C1_nonneg {n : ℕ} (E : Experiment n) :
    0 ≤ C1 E := by
  unfold C1
  apply div_nonneg _ (Nat.cast_nonneg n)
  apply Finset.sum_nonneg
  intro i _
  unfold outgoing
  apply Finset.sum_nonneg
  intro j _
  unfold I
  split_ifs <;> norm_num

/-- The first component of the proved finite graph-count inequality. -/
theorem GP0091B2b_C1_le_dAvg {n : ℕ} (hn : 0 < n)
    (E : Experiment n) : C1 E ≤ dAvg E := by
  exact (le_max_left _ _).trans (interference_count_bounds hn E).1

/-- Extract one eventual bound that controls both graph quantities. -/
theorem GP0091B2b_degree_bound (S : Study)
    (hBound : BigO (fun t => dAvg (S.experiment t)) (fun _ => 1)) :
    ∃ B > 0, ∀ᶠ t in atTop,
      dAvg (S.experiment t) ≤ B ∧ C1 (S.experiment t) ≤ B := by
  obtain ⟨B, hB, hbound⟩ := hBound
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound] with t ht
  have hD : dAvg (S.experiment t) ≤ B := by
    simpa only [abs_one, mul_one] using
      (le_abs_self (dAvg (S.experiment t))).trans ht
  have hC : C1 (S.experiment t) ≤ dAvg (S.experiment t) :=
    GP0091B2b_C1_le_dAvg (S.positive t) (S.experiment t)
  exact ⟨hD, hC.trans hD⟩

/-- Bounded degree supplies both premises of the complete-design theorem. -/
theorem GP0091B2b_complete_restrictions (S : Study)
    (hBound : BigO (fun t => dAvg (S.experiment t)) (fun _ => 1)) :
    Restricted S ∧
      LittleO (fun t => C1 (S.experiment t))
        (fun t => Real.sqrt (size S t)) := by
  refine ⟨BernoulliCompletion.restricted_of_bounded_degree S hBound, ?_⟩
  obtain ⟨B, _hB, hbound⟩ := GP0091B2b_degree_bound S hBound
  have hN : Tendsto (size S) atTop atTop := by
    change Tendsto (fun t => (S.N t : ℝ)) atTop atTop
    exact tendsto_natCast_atTop_iff.mpr S.grows
  have hSqrt : Tendsto (fun t => Real.sqrt (size S t)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hN
  have hUpper : Tendsto (fun t => B / Real.sqrt (size S t))
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using
      hSqrt.inv_tendsto_atTop.const_mul B
  change Tendsto (fun t => C1 (S.experiment t) / Real.sqrt (size S t))
    atTop (nhds 0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hUpper
  · exact Eventually.of_forall (fun t => div_nonneg
      (GP0091B2b_C1_nonneg (S.experiment t))
      (Real.sqrt_nonneg (size S t)))
  · filter_upwards [hbound] with t ht
    exact div_le_div_of_nonneg_right ht.2 (Real.sqrt_nonneg (size S t))

/-- The complete-design rate is eventually a fixed multiple of n^(-1/2). -/
theorem GP0091B2b_complete_rate_root_n (S : Study)
    (hBound : BigO (fun t => dAvg (S.experiment t)) (fun _ => 1)) :
    ∃ C > 0, ∀ᶠ t in atTop,
      bernoulliRate S t + C1 (S.experiment t) / Real.sqrt (size S t) ≤
        C * (1 / Real.sqrt (size S t)) := by
  obtain ⟨B, hB, hbound⟩ := GP0091B2b_degree_bound S hBound
  have hC : 0 < Real.sqrt B + B :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg B) hB
  refine ⟨Real.sqrt B + B, hC, ?_⟩
  filter_upwards [hbound] with t ht
  have hSqrt : Real.sqrt (dAvg (S.experiment t)) ≤ Real.sqrt B :=
    Real.sqrt_le_sqrt ht.1
  have hDen : 0 ≤ Real.sqrt (size S t) := Real.sqrt_nonneg (size S t)
  calc
    bernoulliRate S t + C1 (S.experiment t) / Real.sqrt (size S t) =
        Real.sqrt (dAvg (S.experiment t)) / Real.sqrt (size S t) +
          C1 (S.experiment t) / Real.sqrt (size S t) := rfl
    _ ≤ Real.sqrt B / Real.sqrt (size S t) +
        B / Real.sqrt (size S t) :=
      add_le_add (div_le_div_of_nonneg_right hSqrt hDen)
        (div_le_div_of_nonneg_right ht.2 hDen)
    _ = (Real.sqrt B + B) * (1 / Real.sqrt (size S t)) := by ring


/-- Under nondegenerate complete randomization, each inverse-probability-weighted
arm population-size estimate equals the full population size n. -/
theorem GP0091B2b_complete_counts {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (z : Assignment n) (hz : 0 < E.design.mass z)
    (b : Bool) : nHat E b z = n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_trans hCR.1 hCR.2.1)
  have hm : (0 : ℝ) < m := by exact_mod_cast hCR.1
  have hnm : (0 : ℝ) < (n : ℝ) - m := sub_pos.mpr (by exact_mod_cast hCR.2.1)
  have hc := CompleteConditional.supported_treated_count E m hCR z hz
  unfold nHat
  cases b
  · simp_rw [CompleteConditional.complete_marginal_false E m hCR]
    rw [← Finset.sum_div]
    have hf (i : Fin n) : (if z i = false then (1 : ℝ) else 0) = 1 - bit (z i) := by
      cases h : z i <;> simp [h, bit]
    simp_rw [hf]
    rw [Finset.sum_sub_distrib, hc]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hp : 1 - (m : ℝ) / n ≠ 0 := ne_of_gt (sub_pos.mpr
      ((div_lt_one hn).mpr (by exact_mod_cast hCR.2.1)))
    apply (div_eq_iff hp).mpr
    field_simp
    <;> ring
  · simp_rw [CompleteConditional.complete_marginal_true E m hCR]
    rw [← Finset.sum_div]
    change (∑ i, bit (z i)) / ((m : ℝ) / n) = n
    rw [hc]
    field_simp

/-- The declared empty-arm extension agrees with HT on complete-design support. -/
theorem GP0091B2b_complete_ht_hajek {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (z : Assignment n) (hz : 0 < E.design.mass z) :
    ht E z = hajek E z := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (lt_trans hCR.1 hCR.2.1).ne'
  have htrue := GP0091B2b_complete_counts E m hCR z hz true
  have hf := GP0091B2b_complete_counts E m hCR z hz false
  have ha : ArmsNonempty E z := ⟨by rw [htrue]; exact hn, by rw [hf]; exact hn⟩
  rw [hajek, if_pos ha, htrue, hf]
  unfold ht
  field_simp

/-- A fixed-own-arm potential outcome depends on the other incoming parents. -/
theorem GP0091B2b_potential_depends {n : ℕ} (E : Experiment n) (i : Fin n) (b : Bool) :
    DependsOn (potential E i b)
      ((Finset.univ.filter (fun j => Interferes E j i)).erase i : Set (Fin n)) := by
  intro z z' hagree
  apply BernoulliCompletion.outcome_dependsOn E i
  intro j hj
  by_cases hji : j = i
  · subst j
    simp [Function.update_self]
  · simp only [Function.update_of_ne hji]
    apply hagree j
    simp [hji, hj]

/-- Complete conditional means plus regular potential first moments give bias. -/
theorem GP0091B2b_complete_bias {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (m : ℕ) (hCR : Complete E m) (k q s : ℝ) (hReg : Regular E k q s) :
    |adse E - eate E| ≤ 4 * k^3 * C1 E / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk := hReg.1
  have hk2 := BernoulliCompletion.regular_k_ge_two hn E k q s hReg
  have hunit (i : Fin n) (b : Bool) :
      |cmean E.design (fun z => z i = b) (E.outcome i) -
          mean E.design (potential E i b)| ≤
        2 * (incoming E i : ℝ) / (n : ℝ) * k^2 := by
    let H := (Finset.univ.filter (fun j => Interferes E j i)).erase i
    have hH : (H.card : ℝ) ≤ incoming E i := by
      exact_mod_cast (Finset.card_erase_le : H.card ≤ _)
    have hmean := BernoulliCompletion.mean_abs_of_moment E.design (potential E i b)
      k s hk hReg.2.2.1 (hReg.2.2.2.2.2 i b)
    have hp := BernoulliCompletion.regular_marginal_bounds E k q s hReg i b
    have hbound := CompleteConditional.complete_conditional_mean_bound E m hCR H i
      (Finset.notMem_erase i _) (potential E i b)
      (GP0091B2b_potential_depends E i b) b hp.2.2.1
    rw [BernoulliCompletion.conditional_potential_eq_observed] at hbound
    calc
      _ ≤ (2 * (H.card : ℝ) / (n : ℝ)) * (marginal E i b)⁻¹ *
          mean E.design (fun z => |potential E i b z|) := hbound
      _ ≤ (2 * (incoming E i : ℝ) / (n : ℝ)) * k * k := by
        have hM : 0 ≤ mean E.design (fun z => |potential E i b z|) :=
          Finset.sum_nonneg (fun z _ => mul_nonneg (E.design.nonneg z) (abs_nonneg _))
        have hcoeff : 2 * (H.card : ℝ) / (n : ℝ) ≤ 2 * (incoming E i : ℝ) / n :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hH (by norm_num)) hnR.le
        exact mul_le_mul (mul_le_mul hcoeff hp.2.2.2
          (inv_nonneg.mpr hp.2.2.1.le) (by positivity)) hmean hM (by positivity)
      _ = _ := by ring
  have he : adse E - eate E = (∑ i, (
      (cmean E.design (fun z => z i = true) (E.outcome i) - mean E.design (potential E i true)) -
      (cmean E.design (fun z => z i = false) (E.outcome i) - mean E.design (potential E i false)))) / n := by
    change (∑ i, _) / (n : ℝ) -
      mean E.design (fun z => (∑ i, (potential E i true z - potential E i false z)) / (n : ℝ)) = _
    rw [mean_div, mean_sum]
    simp_rw [mean_sub]
    rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, abs_div, abs_of_pos hnR]
  calc
    _ ≤ (∑ i, |(cmean E.design (fun z => z i = true) (E.outcome i) - mean E.design (potential E i true)) -
        (cmean E.design (fun z => z i = false) (E.outcome i) - mean E.design (potential E i false))|) / n :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hnR.le
    _ ≤ (∑ i, 4 * (incoming E i : ℝ) / (n : ℝ) * k^2) / n := by
      apply div_le_div_of_nonneg_right _ hnR.le
      apply Finset.sum_le_sum
      intro i _
      apply (abs_sub _ _).trans
      calc
        _ ≤ (2 * (incoming E i : ℝ) / (n : ℝ) * k^2) +
            (2 * (incoming E i : ℝ) / (n : ℝ) * k^2) := add_le_add (hunit i true) (hunit i false)
        _ = _ := by ring
    _ = 4 * k^2 * C1 E / n := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum,
        MixingBasics.sum_incoming hn E]
      field_simp
      <;> ring
    _ ≤ 4 * k^3 * C1 E / n := by
      have hC := GP0091B2b_C1_nonneg E
      gcongr
      · linarith
      · norm_num

/-- Generic finite assembly: the nonedge covariance estimate is explicit here. -/
theorem GP0091B2b_arm_variance_from_nonedge {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (k q s : ℝ) (hReg : Regular E k q s) (b : Bool)
    (hNonedge : ∀ i j, ¬ Dependent E i j →
      |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤
        4 * k^3 * (incoming E i : ℝ) * (incoming E j : ℝ) / (n : ℝ)) :
    var E.design (muHat E b) ≤
      k^4 * dAvg E / (n : ℝ) + 4 * k^5 * C1 E^2 / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hk := hReg.1
  have hc (i j : Fin n) :
      |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤
        d E i j * k^2 +
          4 * k^3 * (incoming E i : ℝ) * (incoming E j : ℝ) / (n : ℝ) := by
    by_cases hij : Dependent E i j
    · have ht := (corrected_moment_covariance E k q hReg.1 hReg.2.1
        hReg.2.2.2.2.1 1 (by simpa using hReg.2.1) i j b).2.2.2.2.2.2
      have hbase : |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤ k^2 := by
        simpa only [show 2*1=2 by norm_num] using ht
      simp only [d, hij, if_true, one_mul]
      exact hbase.trans (le_add_of_nonneg_right (by positivity))
    · simpa only [d, hij, if_false, zero_mul, zero_add] using hNonedge i j hij
  have he : muHat E b = fun z =>
      (∑ i, (marginal E i b)⁻¹ * armVariable E b 1 i z) / (n : ℝ) := by
    funext z
    simp only [muHat, armVariable, pow_one, div_eq_mul_inv]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, BernoulliCompletion.variance_div]
  have hw := weighted_variance_absolute E.design (armVariable E b 1)
    (fun i => (marginal E i b)⁻¹) k (fun i =>
      ⟨inv_pos.mpr (BernoulliCompletion.regular_marginal_bounds E k q s hReg i b).2.2.1,
        (BernoulliCompletion.regular_marginal_bounds E k q s hReg i b).2.2.2⟩)
  calc
    _ ≤ (k^2 * (∑ i, ∑ j,
        |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)|)) / (n : ℝ)^2 :=
      div_le_div_of_nonneg_right hw.2 (sq_nonneg _)
    _ ≤ (k^2 * (∑ i, ∑ j, (d E i j * k^2 +
        4 * k^3 * (incoming E i : ℝ) * (incoming E j : ℝ) / (n : ℝ)))) / (n : ℝ)^2 := by
      gcongr with i j
      exact hc i j
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        ← Finset.sum_div, MixingBasics.sum_incoming hn E, dAvg, degree]
      field_simp
      <;> ring

/-- Uniform averaging on a finite nonempty type. -/
def GP0091B2b_uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : Law Ω where
  mass := fun _ => 1 / (Fintype.card Ω : ℝ)
  nonneg := fun _ => by positivity
  total := by simp [Fintype.card_ne_zero]

/-- Uniform averaging is unchanged by a bijection. -/
theorem GP0091B2b_uniform_equiv {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (e : Ω ≃ Ω) (F : Ω → ℝ) :
    mean (GP0091B2b_uniform Ω) (fun w => F (e w)) =
      mean (GP0091B2b_uniform Ω) F := by
  exact e.sum_comp (fun w => (1 / (Fintype.card Ω : ℝ)) * F w)

/-- A coordinate of a uniform permutation is uniform. -/
theorem GP0091B2b_perm_coordinate {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    prob (GP0091B2b_uniform (Equiv.Perm (Fin n))) (fun σ => σ i = j) = 1 / (n : ℝ) := by
  let U := GP0091B2b_uniform (Equiv.Perm (Fin n))
  have he (j l : Fin n) : prob U (fun σ => σ i = j) = prob U (fun σ => σ i = l) := by
    have h := GP0091B2b_uniform_equiv (Equiv.mulLeft (Equiv.swap j l))
      (fun σ : Equiv.Perm (Fin n) => if σ i = l then (1 : ℝ) else 0)
    unfold prob
    convert h using 1 <;>
      (apply congrArg (mean U); funext σ
       simp only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply, Equiv.swap_apply_eq_iff,
         Equiv.swap_apply_right]
       split_ifs <;> rfl)
  have hs : (∑ l : Fin n, prob U (fun σ => σ i = l)) = 1 := by
    simp only [prob, mean]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, U, (GP0091B2b_uniform (Equiv.Perm (Fin n))).total]
  have hj : (n : ℝ) * prob U (fun σ => σ i = j) = 1 := by
    calc
      _ = ∑ l : Fin n, prob U (fun σ => σ i = j) := by simp
      _ = ∑ l : Fin n, prob U (fun σ => σ i = l) :=
        Finset.sum_congr rfl (fun l _ => he j l)
      _ = 1 := hs
  exact (eq_div_iff (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)).mpr (by nlinarith [hj])

/-- Equal treatment counts put two assignments in the same permutation orbit. -/
theorem GP0091B2b_assignment_orbit {n : ℕ} (z w : Assignment n)
    (hcount : (∑ i, bit (z i)) = ∑ i, bit (w i)) :
    ∃ σ : Equiv.Perm (Fin n), CompleteMixing.relabel σ z = w := by
  let S := Finset.univ.filter (fun i => z i = true)
  let T := Finset.univ.filter (fun i => w i = true)
  have hc : T.card = S.card := by
    have hz : (S.card : ℝ) = ∑ i, bit (z i) := by
      simp only [S, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      apply Finset.sum_congr rfl
      intro i _
      cases hi : z i <;> simp [bit, hi]
    have hw : (T.card : ℝ) = ∑ i, bit (w i) := by
      simp only [T, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      apply Finset.sum_congr rfl
      intro i _
      cases hi : w i <;> simp [bit, hi]
    exact_mod_cast (hw.trans (hcount.symm.trans hz.symm))
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq T S hc
  refine ⟨σ, ?_⟩
  funext i
  have hm : σ i ∈ S ↔ i ∈ T := by rw [← hσ]; simp
  have ht : z (σ i) = true ↔ w i = true := by simpa [S, T] using hm
  change z (σ i) = w i
  cases hz : z (σ i) <;> cases hw : w i <;> simp_all

/-- Averaging relabelings of any supported assignment equals design expectation. -/
theorem GP0091B2b_orbit_mean {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (F : Assignment n → ℝ) (z : Assignment n)
    (hz : 0 < E.design.mass z) :
    mean (GP0091B2b_uniform (Equiv.Perm (Fin n)))
      (fun σ => F (CompleteMixing.relabel σ z)) = mean E.design F := by
  let U := GP0091B2b_uniform (Equiv.Perm (Fin n))
  have hc (w : Assignment n) (hw : 0 < E.design.mass w) :
      mean U (fun σ => F (CompleteMixing.relabel σ w)) =
        mean U (fun σ => F (CompleteMixing.relabel σ z)) := by
    obtain ⟨θ, rfl⟩ := GP0091B2b_assignment_orbit z w
      ((CompleteConditional.supported_treated_count E m hCR z hz).trans
        (CompleteConditional.supported_treated_count E m hCR w hw).symm)
    have he (σ : Equiv.Perm (Fin n)) :
        CompleteMixing.relabel σ (CompleteMixing.relabel θ z) =
          CompleteMixing.relabel (θ * σ) z := rfl
    simp only [he]
    exact GP0091B2b_uniform_equiv (Equiv.mulLeft θ)
      (fun σ => F (CompleteMixing.relabel σ z))
  have hh := CompleteConditional.mean_support_congr E.design
    (fun w => mean U (fun σ => F (CompleteMixing.relabel σ w)))
    (fun _ => mean U (fun σ => F (CompleteMixing.relabel σ z))) hc
  rw [mean_const, CompleteMixing.mean_comm] at hh
  simpa only [CompleteMixing.complete_mean_relabel E m hCR, mean_const] using hh.symm

/-- Covariance is invariant under a simultaneous coordinate permutation. -/
theorem GP0091B2b_cov_relabel {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (σ : Equiv.Perm (Fin n)) (F G : Assignment n → ℝ) :
    cov E.design (fun z => F (CompleteMixing.relabel σ z))
      (fun z => G (CompleteMixing.relabel σ z)) = cov E.design F G := by
  simp only [BernoulliCompletion.covariance_product_formula,
    CompleteMixing.complete_mean_relabel E m hCR]
  congr 1
  exact CompleteMixing.complete_mean_relabel E m hCR σ (fun z => F z * G z)


/-- Product of two finite probability laws. -/
def GP0091B2b_product {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : Law Ω) (Q : Law Λ) : Law (Ω × Λ) where
  mass := fun w => P.mass w.1 * Q.mass w.2
  nonneg := fun w => mul_nonneg (P.nonneg _) (Q.nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, Q.total, mul_one, P.total]

/-- Iterated finite expectation under the product law. -/
theorem GP0091B2b_product_mean {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : Law Ω) (Q : Law Λ) (F : Ω × Λ → ℝ) :
    mean (GP0091B2b_product P Q) F = mean P (fun x => mean Q (fun y => F (x,y))) := by
  simp only [mean, GP0091B2b_product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- A zero-mean bounded test, constant off a small event, has a small constant. -/
theorem GP0091B2b_mixture_bound {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (T : Ω → ℝ) (D : Ω → Prop) (c K δ : ℝ) (hK : 0 ≤ K)
    (hT : ∀ w, |T w| ≤ K) (hc : ∀ w, D w → T w = c)
    (hzero : mean P T = 0) (hδ : prob P (fun w => ¬ D w) ≤ δ)
    (hhalf : δ ≤ 1/2) : |c| ≤ 2 * δ * K := by
  let p := prob P D
  let B := mean P (fun w => if ¬ D w then T w else 0)
  have hg : mean P (fun w => if D w then T w else 0) = p * c := by
    change _ = prob P D * c
    rw [mul_comm (prob P D) c]
    unfold prob
    rw [← mean_const_mul P c]
    congr 1
    funext w
    by_cases hw : D w <;> simp [hw, hc w]
  have hs : 0 = p * c + B := by
    calc
      0 = mean P T := hzero.symm
      _ = p*c+B := by
        dsimp only [B]
        rw [← hg, ← mean_add]
        congr 1
        funext w
        by_cases hw : D w <;> simp [hw]
  have hb : |B| ≤ prob P (fun w => ¬ D w) * K := by
    apply (BernoulliCompletion.mean_abs_le P _).trans
    change _ ≤ prob P (fun w => ¬ D w) * K
    rw [mul_comm (prob P (fun w => ¬ D w)) K]
    unfold prob
    rw [← mean_const_mul P K]
    apply CompleteConditional.mean_mono
    intro w
    by_cases hw : D w
    · simp [hw]
    · simpa [hw] using hT w
  have hp : 1 - δ ≤ p := by
    rw [probability_complement] at hδ
    dsimp [p]
    linarith
  have hp0 : 0 ≤ p := probability_nonnegative P D
  have he : p * |c| = |B| := by
    rw [← abs_of_nonneg hp0, ← abs_mul]
    have hh : p*c = -B := by linarith [hs]
    rw [hh, abs_neg]
  have hpc : (1 - δ) * |c| ≤ δ * K := by
    calc
      _ ≤ p * |c| := mul_le_mul_of_nonneg_right hp (abs_nonneg c)
      _ = |B| := he
      _ ≤ prob P (fun w => ¬ D w) * K := hb
      _ ≤ δ*K := mul_le_mul_of_nonneg_right hδ hK
  nlinarith [mul_nonneg (sub_nonneg.mpr hhalf) (abs_nonneg c)]

/-- Two independently relabeled parent sets have no coordinate in common. -/
def GP0091B2b_separated {n : ℕ} (A B : Finset (Fin n))
    (σ τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i ∈ A, ∀ j ∈ B, σ i ≠ τ j

/-- A union bound for collisions between the two relabeled sets. -/
theorem GP0091B2b_collision_bound {n : ℕ} (hn : 0 < n)
    (A B : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) :
    prob (GP0091B2b_uniform (Equiv.Perm (Fin n)))
      (fun τ => ¬ GP0091B2b_separated A B σ τ) ≤
      (A.card : ℝ) * (B.card : ℝ) / (n : ℝ) := by
  let U := GP0091B2b_uniform (Equiv.Perm (Fin n))
  have hpoint (τ : Equiv.Perm (Fin n)) :
      (if ¬ GP0091B2b_separated A B σ τ then (1 : ℝ) else 0) ≤
        ∑ i ∈ A, ∑ j ∈ B, if τ j = σ i then (1 : ℝ) else 0 := by
    by_cases h : GP0091B2b_separated A B σ τ
    · simp only [h, not_true_eq_false, ite_false]
      exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))
    · simp only [h, not_false_eq_true, ite_true]
      unfold GP0091B2b_separated at h
      push_neg at h
      obtain ⟨i, hi, j, hj, he⟩ := h
      calc
        (1 : ℝ) ≤ ∑ j ∈ B, if τ j = σ i then (1 : ℝ) else 0 := by
          simpa [he] using Finset.single_le_sum
            (f := fun j => if τ j = σ i then (1 : ℝ) else 0)
            (fun j _ => by positivity) hj
        _ ≤ ∑ i ∈ A, ∑ j ∈ B, if τ j = σ i then (1 : ℝ) else 0 :=
          Finset.single_le_sum
            (f := fun i => ∑ j ∈ B, if τ j = σ i then (1 : ℝ) else 0)
            (fun i _ => Finset.sum_nonneg (fun j _ => by positivity)) hi
  have hb := CompleteConditional.mean_mono U _ _ hpoint
  have hp : prob U (fun τ => ¬ GP0091B2b_separated A B σ τ) =
      mean U (fun τ => if ¬ GP0091B2b_separated A B σ τ then (1 : ℝ) else 0) := by
    unfold prob
    congr 1
    funext τ
    split_ifs <;> rfl
  rw [hp]
  calc
    _ ≤ mean U (fun τ => ∑ i ∈ A, ∑ j ∈ B,
        if τ j = σ i then (1 : ℝ) else 0) := hb
    _ = ∑ i ∈ A, ∑ j ∈ B, prob U (fun τ => τ j = σ i) := by
      simp only [mean, prob, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro τ hτ
      congr 1
      split_ifs <;> rfl
    _ = _ := by
      simp only [U, GP0091B2b_perm_coordinate hn, Finset.sum_const, nsmul_eq_mul]
      ring

/-- Disjoint relabeled blocks extend simultaneously to one permutation. -/
theorem GP0091B2b_merge_permutations {n : ℕ} (A B : Finset (Fin n))
    (hAB : Disjoint A B) (σ τ : Equiv.Perm (Fin n))
    (hsep : GP0091B2b_separated A B σ τ) :
    ∃ θ : Equiv.Perm (Fin n), (∀ i ∈ A, θ i = σ i) ∧ (∀ j ∈ B, θ j = τ j) := by
  let S := A ∪ B
  let f : S → Fin n := fun i => if (i : Fin n) ∈ A then σ i else τ i
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_cases hi : (i : Fin n) ∈ A <;> by_cases hj : (j : Fin n) ∈ A
    · exact σ.injective (by simpa [f, hi, hj] using hij)
    · have hjB : (j : Fin n) ∈ B := (Finset.mem_union.mp j.property).resolve_left hj
      exact False.elim (hsep i hi j hjB (by simpa [f, hi, hj] using hij))
    · have hiB : (i : Fin n) ∈ B := (Finset.mem_union.mp i.property).resolve_left hi
      exact False.elim (hsep j hj i hiB (by simpa [f, hi, hj] using hij.symm))
    · exact τ.injective (by simpa [f, hi, hj] using hij)
  obtain ⟨θ, hθ⟩ := Equiv.Perm.exists_extending_pair (fun i : S => (i : Fin n)) f
    Subtype.val_injective hf
  refine ⟨θ, ?_, ?_⟩
  · intro i hi
    have hh := hθ ⟨i, Finset.mem_union_left B hi⟩
    simpa [f, hi] using hh
  · intro j hj
    have hjA : j ∉ A := fun hjA => Finset.disjoint_left.mp hAB hjA hj
    have hh := hθ ⟨j, Finset.mem_union_right A hj⟩
    simpa [f, hjA] using hh


/-- L2 covariance control for arbitrary functions of two disjoint parent sets.
The probability of a collision is the only approximation used here. -/
theorem GP0091B2b_disjoint_covariance {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (m : ℕ) (hCR : Complete E m) (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (F G : Assignment n → ℝ) (hF : DependsOn F (A : Set (Fin n)))
    (hG : DependsOn G (B : Set (Fin n))) (K : ℝ) (hK : 0 ≤ K)
    (hVF : var E.design F ≤ K) (hVG : var E.design G ≤ K) :
    |cov E.design F G| ≤ 2 * ((A.card : ℝ) * (B.card : ℝ) / (n : ℝ)) * K := by
  let U := GP0091B2b_uniform (Equiv.Perm (Fin n))
  let Q := GP0091B2b_product U U
  let T := fun p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) =>
    cov E.design (fun z => F (CompleteMixing.relabel p.1 z))
      (fun z => G (CompleteMixing.relabel p.2 z))
  let D := fun p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) =>
    GP0091B2b_separated A B p.1 p.2
  let δ : ℝ := (A.card : ℝ) * (B.card : ℝ) / (n : ℝ)
  have hvar (σ : Equiv.Perm (Fin n)) (H : Assignment n → ℝ) :
      var E.design (fun z => H (CompleteMixing.relabel σ z)) = var E.design H :=
    GP0091B2b_cov_relabel E m hCR σ H H
  have hT (p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) : |T p| ≤ K := by
    apply (covariance_cauchy_schwarz E.design _ _).trans
    rw [hvar, hvar]
    apply (Real.sqrt_le_iff).mpr
    refine ⟨hK, ?_⟩
    simpa only [pow_two] using mul_le_mul hVF hVG (variance_nonnegative E.design G) hK
  by_cases hsmall : δ ≤ 1/2
  · apply GP0091B2b_mixture_bound Q T D (cov E.design F G) K δ hK hT
    · rintro ⟨σ,τ⟩ hsep
      obtain ⟨θ, hθA, hθB⟩ := GP0091B2b_merge_permutations A B hAB σ τ hsep
      have hf : (fun z => F (CompleteMixing.relabel σ z)) =
          (fun z => F (CompleteMixing.relabel θ z)) := by
        funext z
        apply hF
        intro i hi
        change z (σ i) = z (θ i)
        rw [hθA i hi]
      have hg : (fun z => G (CompleteMixing.relabel τ z)) =
          (fun z => G (CompleteMixing.relabel θ z)) := by
        funext z
        apply hG
        intro i hi
        change z (τ i) = z (θ i)
        rw [hθB i hi]
      change cov E.design _ _ = _
      rw [hf, hg, GP0091B2b_cov_relabel E m hCR]
    · have hz (σ : Equiv.Perm (Fin n)) : mean U (fun τ => T (σ,τ)) = 0 := by
        have hm : mean U (fun τ => mean E.design (fun z =>
            F (CompleteMixing.relabel σ z) * G (CompleteMixing.relabel τ z))) =
            mean E.design F * mean E.design G := by
          rw [CompleteMixing.mean_comm]
          calc
            _ = mean E.design (fun z => F (CompleteMixing.relabel σ z) * mean E.design G) := by
              apply CompleteConditional.mean_support_congr
              intro z hz
              rw [mean_const_mul, GP0091B2b_orbit_mean E m hCR G z hz]
            _ = mean E.design G * mean E.design F := by
              simp_rw [mul_comm _ (mean E.design G)]
              rw [mean_const_mul, CompleteMixing.complete_mean_relabel E m hCR]
            _ = _ := mul_comm _ _
        change mean U (fun τ => cov E.design _ _) = 0
        simp only [BernoulliCompletion.covariance_product_formula,
          CompleteMixing.complete_mean_relabel E m hCR]
        rw [mean_sub, mean_const, hm, sub_self]
      rw [GP0091B2b_product_mean]
      change mean U (fun σ => mean U (fun τ => T (σ,τ))) = 0
      simp_rw [hz]
      exact mean_const U 0
    · change prob (GP0091B2b_product U U) (fun p => ¬ D p) ≤ δ
      unfold prob
      rw [GP0091B2b_product_mean]
      have hb : mean U (fun σ => prob U (fun τ => ¬ GP0091B2b_separated A B σ τ)) ≤ δ := by
        calc
          _ ≤ mean U (fun _ => δ) := CompleteConditional.mean_mono U _ _
            (fun σ => GP0091B2b_collision_bound hn A B σ)
          _ = _ := mean_const U δ
      convert hb using 1
      apply congrArg (mean U)
      funext σ
      unfold prob
      congr 1
    · exact hsmall
  · have hb : |cov E.design F G| ≤ K := by
      simpa [T, CompleteMixing.relabel] using hT (1,1)
    have hδ : 0 ≤ δ := by dsimp [δ]; positivity
    change |cov E.design F G| ≤ 2*δ*K
    exact hb.trans (by nlinarith [mul_nonneg (by linarith : 0 ≤ 2*δ-1) hK])


/-- Complete-design covariance of two units with disjoint incoming parent sets. -/
theorem GP0091B2b_complete_nonedge_covariance {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (m : ℕ) (hCR : Complete E m) (k q s : ℝ)
    (hReg : Regular E k q s) (b : Bool) (i j : Fin n) (hij : ¬ Dependent E i j) :
    |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤
      4 * k^3 * (incoming E i : ℝ) * (incoming E j : ℝ) / (n : ℝ) := by
  let A := Finset.univ.filter (fun l => Interferes E l i)
  let B := Finset.univ.filter (fun l => Interferes E l j)
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro l hlA hlB
    exact hij ⟨l, (Finset.mem_filter.mp hlA).2, (Finset.mem_filter.mp hlB).2⟩
  have hF : DependsOn (armVariable E b 1 i) (A : Set (Fin n)) := by
    intro z w hw
    apply BernoulliCompletion.arm_dependsOn E i b 1
    intro l hl
    exact hw l (by simp [A, hl])
  have hG : DependsOn (armVariable E b 1 j) (B : Set (Fin n)) := by
    intro z w hw
    apply BernoulliCompletion.arm_dependsOn E j b 1
    intro l hl
    exact hw l (by simp [B, hl])
  have hv (l : Fin n) : var E.design (armVariable E b 1 l) ≤ k^2 := by
    have hh := (corrected_moment_covariance E k q hReg.1 hReg.2.1
      hReg.2.2.2.2.1 1 (by simpa using hReg.2.1) l l b).2.2.2.2.2.2
    exact (le_abs_self _).trans (by simpa only [var, show 2*1=2 by norm_num] using hh)
  have hcov : |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤
      2 * ((incoming E i : ℝ) * (incoming E j : ℝ) / (n : ℝ)) * k^2 :=
    GP0091B2b_disjoint_covariance hn E m hCR A B hAB
      (armVariable E b 1 i) (armVariable E b 1 j) hF hG (k^2) (sq_nonneg k) (hv i) (hv j)
  have hk := BernoulliCompletion.regular_k_ge_two hn E k q s hReg
  have hpow : 2*k^2 ≤ 4*k^3 := by
    nlinarith [mul_nonneg (sq_nonneg k) (show 0 ≤ 2*k-1 by linarith)]
  have hδ : 0 ≤ (incoming E i : ℝ) * (incoming E j : ℝ) / (n : ℝ) := by positivity
  calc
    _ ≤ 2 * ((incoming E i : ℝ) * (incoming E j : ℝ) / (n : ℝ)) * k^2 := hcov
    _ = ((incoming E i : ℝ) * (incoming E j : ℝ) / (n : ℝ)) * (2*k^2) := by ring
    _ ≤ ((incoming E i : ℝ) * (incoming E j : ℝ) / (n : ℝ)) * (4*k^3) :=
      mul_le_mul_of_nonneg_left hpow hδ
    _ = _ := by ring

/-- Finite complete-design bias and variance bounds, exact inverse-probability-weighted
arm population-size estimates, and equality of the HT and Hajek estimators on support. -/
theorem GP0091B2b_complete_finite_input {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (m : ℕ) (hCR : Complete E m) (k q s : ℝ) (hReg : Regular E k q s) :
    (∑ i, (incoming E i:ℝ))/(n:ℝ) = C1 E ∧
    |adse E-eate E| ≤ 4*k^3*C1 E/(n:ℝ) ∧
    (∀ b, var E.design (muHat E b) ≤ k^4*dAvg E/(n:ℝ)+4*k^5*C1 E^2/(n:ℝ)) ∧
    (∀ z, 0 < E.design.mass z → nHat E true z = n ∧ nHat E false z = n ∧
      ht E z = hajek E z) := by
  refine ⟨?_, GP0091B2b_complete_bias hn E m hCR k q s hReg, ?_, ?_⟩
  · rw [MixingBasics.sum_incoming hn E]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    exact mul_div_cancel_left₀ _ hn0
  · intro b
    exact GP0091B2b_arm_variance_from_nonedge hn E k q s hReg b
      (fun i j hij => GP0091B2b_complete_nonedge_covariance hn E m hCR k q s hReg b i j hij)
  · intro z hz
    exact ⟨GP0091B2b_complete_counts E m hCR z hz true,
      GP0091B2b_complete_counts E m hCR z hz false,
      GP0091B2b_complete_ht_hajek E m hCR z hz⟩
/-- Finite bias/variance decomposition, valid without any design restriction. -/
private theorem GP0091B2b_mse_identity {Ω : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → ℝ) (a : ℝ) :
    mean P (fun z => (X z-a)^2) = var P X+(mean P X-a)^2 := by
  have he : (fun z => (X z-a)^2) = fun z => X z^2-(2*a)*X z+a^2 := by
    funext z
    ring
  rw [he, mean_add, mean_sub, mean_const_mul, mean_const, variance_second_moment]
  ring

private theorem GP0091B2b_rate_square (S : Study) (t : ℕ) :
    dAvg (S.experiment t)/size S t ≤
      (bernoulliRate S t+C1 (S.experiment t)/Real.sqrt (size S t))^2 ∧
    C1 (S.experiment t)^2/size S t ≤
      (bernoulliRate S t+C1 (S.experiment t)/Real.sqrt (size S t))^2 := by
  have hn : 0 < size S t := by dsimp [size]; exact_mod_cast S.positive t
  have hC : 0 ≤ C1 (S.experiment t) :=
    GP0091B2b_C1_nonneg (S.experiment t)
  have hr := BernoulliCompletion.bernoulli_rate_pos S t
  have hs := BernoulliCompletion.bernoulli_rate_square S t
  have hc : (C1 (S.experiment t)/Real.sqrt (size S t))^2 =
      C1 (S.experiment t)^2/size S t := by
    rw [div_pow, Real.sq_sqrt hn.le]
  have hcr : 0 ≤ C1 (S.experiment t)/Real.sqrt (size S t) := by positivity
  constructor <;> nlinarith [mul_nonneg hr.le hcr]

private theorem GP0091B2b_HT_mse_bound (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hCR : CompleteSequence S) (t : ℕ) :
    mean (S.experiment t).design (fun z =>
      (ht (S.experiment t) z-eate (S.experiment t))^2) ≤
      (4*k^4+16*k^5+16*k^6+1)*
        (bernoulliRate S t+C1 (S.experiment t)/Real.sqrt (size S t))^2 := by
  obtain ⟨p, hp, hp1, hcomplete⟩ := hCR
  let E := S.experiment t
  let n := size S t
  let C := C1 E
  let D := dAvg E
  let a := bernoulliRate S t+C/Real.sqrt n
  have hn : 0 < n := by dsimp [n, size]; exact_mod_cast S.positive t
  have hn1 : 1 ≤ n := by
    dsimp [n, size]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (S.positive t).ne')
  have hC : 0 ≤ C := GP0091B2b_C1_nonneg E
  have hk : 0 < k := (hReg t).1
  have hfinite := GP0091B2b_complete_finite_input (S.positive t) E
    ⌊p*size S t⌋₊ (hcomplete t) k q s (hReg t)
  have hbias : |adse E-eate E| ≤ 4*k^3*C/n := hfinite.2.1
  have hv1 : var E.design (muHat E true) ≤ k^4*D/n+4*k^5*C^2/n :=
    hfinite.2.2.1 true
  have hv0 : var E.design (muHat E false) ≤ k^4*D/n+4*k^5*C^2/n :=
    hfinite.2.2.1 false
  have hv : var E.design (ht E) ≤ 4*k^4*D/n+16*k^5*C^2/n := by
    have hh := BernoulliCompletion.variance_sub_le E.design (muHat E true) (muHat E false)
    change var E.design (fun z => muHat E true z-muHat E false z) ≤ _
    ring_nf at hv1 hv0 hh ⊢
    linarith only [hv1, hv0, hh]
  have hm : mean E.design (ht E) = adse E := by
    apply ht_unbiased_ADSE E
    intro i
    exact ⟨(BernoulliCompletion.regular_marginal_bounds E k q s (hReg t) i true).2.2.1,
      (BernoulliCompletion.regular_marginal_bounds E k q s (hReg t) i false).2.2.1⟩
  have hbias2 : (adse E-eate E)^2 ≤ 16*k^6*C^2/n := by
    have hh : (adse E-eate E)^2 ≤ (4*k^3*C/n)^2 := by
      have h := (sq_le_sq₀ (abs_nonneg (adse E-eate E))
        (show 0 ≤ 4*k^3*C/n by positivity)).mpr hbias
      simpa only [sq_abs] using h
    calc
      _ ≤ (4*k^3*C/n)^2 := hh
      _ = 16*k^6*C^2/n^2 := by ring
      _ ≤ 16*k^6*C^2/n := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hn) hn).mpr
        have hN : 0 ≤ 16*k^6*C^2 := by positivity
        exact mul_le_mul_of_nonneg_left (by nlinarith : n ≤ n^2) hN
  have hparts := GP0091B2b_rate_square S t
  have hDsq : D/n ≤ a^2 := hparts.1
  have hCsq : C^2/n ≤ a^2 := hparts.2
  have hDmul := mul_le_mul_of_nonneg_left hDsq (show 0 ≤ 4*k^4 by positivity)
  have hCmul := mul_le_mul_of_nonneg_left hCsq (show 0 ≤ 16*k^5+16*k^6 by positivity)
  rw [GP0091B2b_mse_identity, hm]
  change var E.design (ht E)+(adse E-eate E)^2 ≤ _
  have hrate : 0 ≤ a^2 := sq_nonneg _
  dsimp [a, C, D, n, E] at hv hbias2 hDmul hCmul hrate ⊢
  ring_nf at hv hbias2 hDmul hCmul hrate ⊢
  linarith only [hv, hbias2, hDmul, hCmul, hrate]

-- P009-T42.
theorem GP0091B2b_complete_consistency (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hCR : CompleteSequence S)
    (hRestricted : Restricted S)
    (hC1 : LittleO (fun t => C1 (S.experiment t)) (fun t => Real.sqrt (size S t))) :
    EstimatorClaims S (fun t => eate (S.experiment t))
      (fun t => bernoulliRate S t + C1 (S.experiment t)/Real.sqrt (size S t)) := by
  let a := fun t => bernoulliRate S t+C1 (S.experiment t)/Real.sqrt (size S t)
  let C0 := 4*k^4+16*k^5+16*k^6+1
  have hk : 0 < k := (hReg 0).1
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have ha (t : ℕ) : 0 < a t := by
    have hC : 0 ≤ C1 (S.experiment t) :=
      GP0091B2b_C1_nonneg (S.experiment t)
    have hc : 0 ≤ C1 (S.experiment t)/Real.sqrt (size S t) := by positivity
    exact add_pos_of_pos_of_nonneg (BernoulliCompletion.bernoulli_rate_pos S t) hc
  have hM (t : ℕ) : mean (S.experiment t).design (fun z =>
      (ht (S.experiment t) z-eate (S.experiment t))^2) ≤ C0*(a t)^2 :=
    GP0091B2b_HT_mse_bound S k q s hReg hCR t
  have hHT : Op S (fun t z => ht (S.experiment t) z-eate (S.experiment t)) a :=
    BernoulliCompletion.op_of_second_moment S _ a C0 hC0 ha hM
  have hHJmom (t : ℕ) : mean (S.experiment t).design (fun z =>
      (hajek (S.experiment t) z-eate (S.experiment t))^2) =
      mean (S.experiment t).design (fun z =>
        (ht (S.experiment t) z-eate (S.experiment t))^2) := by
    obtain ⟨p, hp, hp1, hcomplete⟩ := hCR
    have hf := GP0091B2b_complete_finite_input (S.positive t) (S.experiment t)
      ⌊p*size S t⌋₊ (hcomplete t) k q s (hReg t)
    apply CompleteConditional.mean_support_congr
    intro z hz
    rw [(hf.2.2.2 z hz).2.2]
  have hHJ : Op S (fun t z => hajek (S.experiment t) z-eate (S.experiment t)) a := by
    apply BernoulliCompletion.op_of_second_moment S _ a C0 hC0 ha
    intro t
    rw [hHJmom t]
    exact hM t
  have hazero : Tendsto a atTop (nhds 0) := by
    have hr := BernoulliCompletion.bernoulli_rate_zero S hRestricted
    have hc : Tendsto (fun t => C1 (S.experiment t)/Real.sqrt (size S t))
        atTop (nhds 0) := hC1
    simpa only [add_zero] using hr.add hc
  exact ⟨BernoulliCompletion.probability_of_op_zero S _ a hazero hHT,
    BernoulliCompletion.probability_of_op_zero S _ a hazero hHJ, hHT, hHJ⟩

/-- T43, Corollary 1: both consistency conclusions and both root-n orders. -/
theorem root_n_consistency_proof (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s)
    (hDesign : (∀ t, Bernoulli (S.experiment t)) ∨ CompleteSequence S)
    (hBound : BigO (fun t => dAvg (S.experiment t)) (fun _ => 1)) :
    EstimatorClaims S (fun t => eate (S.experiment t))
      (fun t => 1/Real.sqrt (size S t)) := by
  rcases hDesign with hBER | hCR
  · exact bernoulli_root_n_consistency S k q s hReg hBER hBound
  · obtain ⟨hRestricted, hC1⟩ :=
      GP0091B2b_complete_restrictions S hBound
    have hClaims : EstimatorClaims S (fun t => eate (S.experiment t))
        (fun t => bernoulliRate S t +
          C1 (S.experiment t) / Real.sqrt (size S t)) :=
      GP0091B2b_complete_consistency S k q s hReg hCR hRestricted hC1
    obtain ⟨C, hC, hRate⟩ := GP0091B2b_complete_rate_root_n S hBound
    have hHT : Op S
        (fun t z => ht (S.experiment t) z - eate (S.experiment t))
        (fun t => 1 / Real.sqrt (size S t)) :=
      BernoulliCompletion.op_change_rate S _ _ _ C hC hRate hClaims.2.2.1
    have hHajek : Op S
        (fun t z => hajek (S.experiment t) z - eate (S.experiment t))
        (fun t => 1 / Real.sqrt (size S t)) :=
      BernoulliCompletion.op_change_rate S _ _ _ C hC hRate hClaims.2.2.2
    exact ⟨hClaims.1, hClaims.2.1, hHT, hHajek⟩

end

end AronowAudit.P009.Wave1
