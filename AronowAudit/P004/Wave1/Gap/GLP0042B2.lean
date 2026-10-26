import AronowAudit.P004.Wave1.LinePopulation.N1
import AronowAudit.P004.Wave1.FiniteConditioning.FC4
import AronowAudit.P004.Wave1.DesignLimits.DL1
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Probability.Moments.Variance

/-! The sparse NED coverage counterexample, P004-T27. -/
namespace AronowAudit.P004.Wave1

open scoped BigOperators Matrix Classical Topology
open MeasureTheory Filter
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

private lemma T27_half {N : ℕ} : ∀ _i : Fin N, 0 < (1/2 : ℝ) ∧ (1/2 : ℝ) < 1 :=
  fun _ => by norm_num

lemma T27_separation {N : ℕ} (i j : Fin N) :
    nodeSeparation (sparsePopulation N) i j = (N : ℝ)^2 * |(i : ℝ) - j| := by
  have hd : nodeSeparation (sparsePopulation N) i j =
      dist (planePoint (((i : ℝ)+1)*N^2) 0) (planePoint (((j : ℝ)+1)*N^2) 0) := by
    simp [nodeSeparation, sparsePopulation]
  rw [hd]
  rw [LinePopulation.line_point_dist]
  have he : (((i : ℝ)+1)*N^2 - ((j : ℝ)+1)*N^2) =
      (N : ℝ)^2*((i : ℝ)-j) := by ring
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg _)]

lemma T27_separation_self {N : ℕ} (i : Fin N) :
    nodeSeparation (sparsePopulation N) i i = 0 := by simp [T27_separation]

lemma T27_separation_gap {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    (N : ℝ)^2 ≤ nodeSeparation (sparsePopulation N) i j := by
  rw [T27_separation]
  have hdiff : (1 : ℝ) ≤ |(i : ℝ)-j| := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · have hh : (i.val : ℝ)+1 ≤ j.val := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : (j.val : ℝ)+1 ≤ i.val := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  nlinarith [mul_le_mul_of_nonneg_left hdiff (sq_nonneg (N : ℝ))]

lemma T27_point_injective {N : ℕ} (hN : 0 < N) :
    Function.Injective (fun i : Fin N => planePoint (((i : ℝ)+1)*N^2) 0) := by
  intro i j hij
  have hx := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hij
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hh : ((i : ℝ)+1)*N^2 = ((j : ℝ)+1)*N^2 := by simpa [planePoint] using hx
  have hv : (i : ℝ) = (j : ℝ) := by nlinarith [sq_pos_of_ne_zero hn]
  exact Fin.val_injective (by exact_mod_cast hv)

lemma T27_ball_small {N : ℕ} (i : Fin N) (s : ℝ) (hs : 0 ≤ s)
    (hsmall : s < (N : ℝ)^2) : ball (nodeSeparation (sparsePopulation N)) i s = {i} := by
  ext j
  simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hji
    exact (not_le_of_gt hsmall) ((T27_separation_gap i j (Ne.symm hji)).trans h)
  · rintro rfl
    simpa only [T27_separation_self] using hs

lemma T27_spacing : QuadraticSpacing sparsePopulation := by
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN i s hs
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases hsmall : s < (N : ℝ)^2
  · rw [T27_ball_small i s hs hsmall]
    simp only [Finset.card_singleton, Nat.cast_one, one_mul]
    nlinarith [sq_nonneg s]
  · have hc : ((ball (nodeSeparation (sparsePopulation N)) i s).card : ℝ) ≤ N := by
      have hc := Finset.card_le_card
        (Finset.subset_univ (ball (nodeSeparation (sparsePopulation N)) i s))
      simpa using (Nat.cast_le (α := ℝ)).mpr hc
    have hlarge : (N : ℝ)^2 ≤ s := le_of_not_gt hsmall
    have hns : (N : ℝ) ≤ s := by nlinarith
    simp only [one_mul]
    nlinarith [sq_nonneg (s-1)]

lemma T27_atom_region {N : ℕ} (i j : Fin N) :
    planePoint (((j : ℝ)+1)*N^2) 0 ∈ region (sparsePopulation N) i 1 ↔ j = i := by
  change Metric.infDist (planePoint (((j : ℝ)+1)*N^2) 0)
    {planePoint (((i : ℝ)+1)*N^2) 0} ∈ Set.Icc 0 1 ↔ j = i
  rw [Metric.infDist_singleton]
  constructor
  · intro h
    by_contra hji
    have hN : 2 ≤ N := by
      have hi := i.isLt
      have hj := j.isLt
      have hne := Fin.val_ne_of_ne hji
      omega
    have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hg := T27_separation_gap i j (Ne.symm hji)
    have hd : nodeSeparation (sparsePopulation N) i j ≤ 1 := by
      simpa [nodeSeparation, sparsePopulation, dist_comm] using h.2
    nlinarith
  · rintro rfl
    simp

lemma T27_region_measurable {N : ℕ} (i : Fin N) :
    MeasurableSet (region (sparsePopulation N) i 1) := by
  simp only [region, nodeDistance, sparsePopulation, Metric.infDist_singleton]
  exact measurableSet_Icc.preimage (measurable_id.dist measurable_const)

lemma T27_outcome_atom {N : ℕ} (j : Fin N) (z : Assignment N) :
    (sparsePopulation N).outcome (planePoint (((j : ℝ)+1)*N^2) 0) z = sparseTable N j z := by
  have hN : 0 < N := Nat.zero_lt_of_lt j.isLt
  change (∑ k : Fin N, if planePoint (((j : ℝ)+1)*N^2) 0 =
    planePoint (((k : ℝ)+1)*N^2) 0 then sparseTable N k z else 0) = _
  simp only [(T27_point_injective hN).eq_iff]
  simp

lemma T27_mass {N : ℕ} (i : Fin N) :
    (sparsePopulation N).zeta (region (sparsePopulation N) i 1) = 1 := by
  change (∑ j : Fin N, Measure.dirac (planePoint (((j : ℝ)+1)*N^2) 0))
    (region (sparsePopulation N) i 1) = 1
  rw [Measure.finsetSum_apply]
  calc
    _ = ∑ j : Fin N, if j = i then (1 : ENNReal) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Measure.dirac_apply]
      change (if _ ∈ region (sparsePopulation N) i 1 then (1 : ENNReal) else 0) = _
      rw [T27_atom_region]
      split_ifs <;> rfl
    _ = 1 := by simp

lemma T27_restrict {N : ℕ} (i : Fin N) :
    (sparsePopulation N).zeta.restrict (region (sparsePopulation N) i 1) =
      Measure.dirac (planePoint (((i : ℝ)+1)*N^2) 0) := by
  have hr : ((∑ j : Fin N, Measure.dirac (planePoint (((j : ℝ)+1)*N^2) 0)).restrict
      (region (sparsePopulation N) i 1)) =
      ∑ j : Fin N, (Measure.dirac (planePoint (((j : ℝ)+1)*N^2) 0)).restrict
        (region (sparsePopulation N) i 1) := by
    simpa only [Measure.restrictₗ_apply] using
      map_sum (Measure.restrictₗ (region (sparsePopulation N) i 1))
        (fun j : Fin N => Measure.dirac (planePoint (((j : ℝ)+1)*N^2) 0)) Finset.univ
  change ((∑ j : Fin N, Measure.dirac (planePoint (((j : ℝ)+1)*N^2) 0)).restrict _) = _
  rw [hr]
  simp_rw [restrict_dirac' (T27_region_measurable i), T27_atom_region]
  simp

lemma T27_circle (N : ℕ) : circleAverage (sparsePopulation N) 1 = sparseTable N := by
  funext i z
  simp only [circleAverage, T27_mass, ENNReal.toReal_one, div_one]
  rw [T27_restrict]
  simpa only [integral_dirac] using T27_outcome_atom i z

lemma T27_wellDefined (N : ℕ) : WellDefined (sparsePopulation N) 1 := by
  intro i
  refine ⟨T27_region_measurable i, ?_, ?_, ?_⟩
  · rw [T27_mass]; norm_num
  · rw [T27_mass]; norm_num
  · intro z
    change Integrable (fun x => (sparsePopulation N).outcome x z)
      ((sparsePopulation N).zeta.restrict (region (sparsePopulation N) i 1))
    rw [T27_restrict]
    exact integrable_dirac (by simp)

lemma T27_outcome_bound {N : ℕ} (hN : 0 < N)
    (x : EuclideanSpace ℝ (Fin 2)) (z : Assignment N) :
    |(sparsePopulation N).outcome x z| < 2 := by
  let o : Fin N := ⟨0, hN⟩
  have he : (sparsePopulation N).outcome x z =
      if x = planePoint (((o : ℝ)+1)*N^2) 0 then (1/4+3/4*bit (z o)) else 0 := by
    change (∑ i : Fin N, if x = planePoint (((i : ℝ)+1)*N^2) 0
      then sparseTable N i z else 0) = _
    rw [Finset.sum_eq_single o]
    · simp [sparseTable, o]
    · intro b _ hbo
      have hb : b.val ≠ 0 := by intro h; apply hbo; exact Fin.ext h
      simp [sparseTable, hb]
    · simp
  rw [he]
  split_ifs <;> cases z o <;> norm_num [bit]

lemma T27_bounded : BoundedOutcomes sparsePopulation := by
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN x z
  exact T27_outcome_bound (by omega) x z

lemma T27_ned : NEDConditions sparsePopulation (1/2) 1 := by
  refine ⟨fun _ => 0, fun _ _ => 1, 1, ?_, ?_, tendsto_const_nhds, ?_, ?_, ?_⟩
  · exact fun _ _ => le_rfl
  · exact fun _ _ _ _ _ => le_rfl
  · exact ⟨5, by norm_num, 0, 1, by norm_num, fun _ _ => by simp⟩
  · exact fun _ _ => ⟨by norm_num, le_rfl⟩
  · intro N i s hs
    rw [T27_circle]
    have hc : conditionOn (fun _ => 1/2) (ball (nodeSeparation (sparsePopulation N)) i s)
        (sparseTable N i) = sparseTable N i := by
      apply FiniteConditioning.conditionOn_of_depends _ T27_half
      intro z z' hzz'
      have hi : i ∈ ball (nodeSeparation (sparsePopulation N)) i s := by
        simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and, T27_separation_self]
        exact hs
      simp only [sparseTable, hzz' i hi]
    simp only [hc, sub_self, l2Norm, expect_const, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Real.sqrt_zero, mul_zero, le_refl]

lemma T27_kernel : KernelConditions uniformKernel := by
  refine ⟨by norm_num [uniformKernel], ?_, ⟨2, ?_⟩, 1/2, 1, by norm_num,
    by norm_num, by norm_num, ?_⟩
  · intro t ht
    simp [uniformKernel, not_le.mpr ht]
  · intro t ht
    unfold uniformKernel
    split_ifs <;> norm_num
  · intro t ht hsmall
    have ht1 : t ≤ 1 := by linarith
    simp [uniformKernel, ht, ht1, abs_nonneg]

lemma T27_bandwidth_diverges : Tendsto sparseBandwidth atTop atTop := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^(1/12 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1/12 : ℝ))).comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono (f := fun N : ℕ => (N : ℝ)^(1/12 : ℝ)-1)
  · intro N
    have h := Nat.lt_floor_add_one ((N : ℝ)^(1/12 : ℝ))
    dsimp [sparseBandwidth]
    linarith
  · simpa only [sub_eq_add_neg] using (tendsto_atTop_add_const_right _ (-1) hp)

lemma T27_bandwidth_rate :
    Asymptotics.IsLittleO atTop sparseBandwidth (fun N => (N : ℝ)^(1/6 : ℝ)) := by
  have hr : Asymptotics.IsLittleO atTop (fun N : ℕ => (N : ℝ)^(1/12 : ℝ))
      (fun N : ℕ => (N : ℝ)^(1/6 : ℝ)) := by
    apply Asymptotics.isLittleO_of_tendsto'
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hn : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
      intro hz
      exact ((Real.rpow_pos_of_pos hn _).ne' hz).elim
    · have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/12)).comp
        tendsto_natCast_atTop_atTop
      apply hh.congr'
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hn : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
      rw [← Real.rpow_sub hn]
      norm_num
  apply Asymptotics.IsBigO.trans_isLittleO (g := fun N : ℕ => (N : ℝ)^(1/12 : ℝ)) _ hr
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [] with N
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [sparseBandwidth]; positivity),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _), one_mul]
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)

lemma T27_bandwidth_bounds {N : ℕ} (hN : 2 ≤ N) :
    0 < sparseBandwidth N ∧ sparseBandwidth N < (N : ℝ)^2 := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by linarith
  have hp : (1 : ℝ) ≤ (N : ℝ)^(1/12 : ℝ) :=
    Real.one_le_rpow hn1 (by norm_num)
  have hf : 1 ≤ ⌊(N : ℝ)^(1/12 : ℝ)⌋₊ :=
    (Nat.le_floor_iff (by positivity)).mpr (by simpa only [Nat.cast_one] using hp)
  have hlu : sparseBandwidth N ≤ (N : ℝ)^(1/12 : ℝ) := Nat.floor_le (by positivity)
  have hr : (N : ℝ)^(1/12 : ℝ) < (N : ℝ)^(2 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
  rw [Real.rpow_two] at hr
  have hb1 : (1 : ℝ) ≤ sparseBandwidth N := by
    dsimp only [sparseBandwidth]
    exact_mod_cast hf
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hb1, hlu.trans_lt hr⟩

lemma T27_kernel_eq {N : ℕ} (hN : 2 ≤ N) (i j : Fin N) :
    uniformKernel (nodeSeparation (sparsePopulation N) i j / sparseBandwidth N) =
      if i = j then 1 else 0 := by
  have hb := T27_bandwidth_bounds hN
  by_cases hij : i = j
  · subst j
    simp [T27_separation_self, uniformKernel]
  · have hgt : 1 < nodeSeparation (sparsePopulation N) i j / sparseBandwidth N := by
      apply (lt_div_iff₀ hb.1).mpr
      simpa using hb.2.trans_le (T27_separation_gap i j hij)
    simp [uniformKernel, hij, not_le.mpr hgt]

lemma T27_sum_zero {N : ℕ} (hN : 0 < N) (c : ℝ) :
    (∑ i : Fin N, if i.val = 0 then c else 0) = c := by
  have hi (i : Fin N) : i.val = 0 ↔ i = ⟨0, hN⟩ := by simp [Fin.ext_iff]
  simp_rw [hi]
  simp

lemma T27_marginal {N : ℕ} (i : Fin N) (a : Bool) :
    marginal (fun _ => 1/2) (sparseTable N) i a =
      if i.val = 0 then 1/4+3/4*bit a else 0 := by
  rw [marginal_is_marginalization _ _ _ _ T27_half]
  simp only [sparseTable, Function.update_self, expect_const]

lemma T27_effect {N : ℕ} (i : Fin N) :
    nodeEffect (fun _ => 1/2) (sparseTable N) i = if i.val = 0 then 3/4 else 0 := by
  simp only [nodeEffect, T27_marginal]
  split_ifs <;> norm_num [bit]

lemma T27_ame {N : ℕ} (hN : 0 < N) :
    ame (fun _ => 1/2) (sparseTable N) = (3/4 : ℝ)/N := by
  simp only [ame, T27_effect, T27_sum_zero hN]

lemma T27_barMu {N : ℕ} (hN : 0 < N) (a : Bool) :
    barMu (fun _ => 1/2) (sparseTable N) a = (1/4+3/4*bit a)/N := by
  simp only [barMu, T27_marginal, T27_sum_zero hN]

lemma T27_homophily :
    LiminfAtLeast (kernelHomophily sparsePopulation (1/2) 1 uniformKernel sparseBandwidth) 0 := by
  intro ε hε
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hh : 0 ≤ kernelHomophily sparsePopulation (1/2) 1 uniformKernel sparseBandwidth N := by
    unfold kernelHomophily
    apply div_nonneg _ hn
    apply Finset.sum_nonneg
    intro i _
    simp only [T27_kernel_eq hN]
    rw [Finset.sum_eq_single i]
    · simp only [ite_true, one_mul]
      exact mul_self_nonneg _
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  linarith

lemma T27_count_bounds {N : ℕ} (z : Assignment N) (a : Bool) :
    0 ≤ armCount z a ∧ armCount z a ≤ (N : ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  · calc
      armCount z a ≤ ∑ _i : Fin N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs <;> norm_num
      _ = _ := by simp

lemma T27_count_complement {N : ℕ} (z : Assignment N) :
    armCount z true + armCount z false = (N : ℝ) := by
  rw [armCount, armCount, ← Finset.sum_add_distrib]
  have hi (i : Fin N) : (if z i = true then (1 : ℝ) else 0) +
      (if z i = false then (1 : ℝ) else 0) = 1 := by cases z i <;> norm_num
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma T27_arm_numerator {N : ℕ} (hN : 0 < N) (z : Assignment N) (a : Bool) :
    (∑ i : Fin N, if z i = a then sparseTable N i z else 0) =
      if z ⟨0, hN⟩ = a then 1/4+3/4*bit (z ⟨0, hN⟩) else 0 := by
  let o : Fin N := ⟨0, hN⟩
  rw [Finset.sum_eq_single o]
  · simp [sparseTable, o]
  · intro b _ hbo
    have hb : b.val ≠ 0 := by intro h; apply hbo; exact Fin.ext h
    simp [sparseTable, hb]
  · simp

lemma T27_ht_abs {N : ℕ} (hN : 0 < N) (z : Assignment N) :
    |ht (fun _ => 1/2) (sparseTable N) z| ≤ 2/(N : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  unfold ht
  rw [abs_div, abs_of_pos hn]
  apply (div_le_div_iff_of_pos_right hn).mpr
  let o : Fin N := ⟨0,hN⟩
  have hs : (∑ i : Fin N, (bit (z i)*sparseTable N i z/(1/2) -
      (1-bit (z i))*sparseTable N i z/(1-1/2))) =
      bit (z o)*sparseTable N o z/(1/2) -
      (1-bit (z o))*sparseTable N o z/(1-1/2) := by
    apply Finset.sum_eq_single o
    · intro b _ hbo
      have hb : b.val ≠ 0 := by intro h; apply hbo; exact Fin.ext h
      simp [sparseTable, hb]
    · simp
  rw [hs]
  cases hz : z o <;> norm_num [sparseTable, show o.val = 0 from rfl, bit, hz]

lemma T27_linear_identity {N : ℕ} (hN : 0 < N) (z : Assignment N) :
    linearHajek (fun _ => 1/2) (sparseTable N) z =
      ht (fun _ => 1/2) (sparseTable N) z -
        (5/(4*(N : ℝ))) * (2*armCount z true/N-1) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hcnt : (∑ i : Fin N, bit (z i)) = armCount z true := by
    apply Finset.sum_congr rfl
    intro i _
    cases z i <;> norm_num [bit]
  unfold linearHajek augmented ht
  simp only [T27_barMu hN]
  have hr (i : Fin N) :
      ((1/4+3/4*bit true)/N - (1/4+3/4*bit false)/N +
        bit (z i)*(sparseTable N i z-(1/4+3/4*bit true)/N)/(1/2) -
        (1-bit (z i))*(sparseTable N i z-(1/4+3/4*bit false)/N)/(1-1/2)) =
      (bit (z i)*sparseTable N i z/(1/2) -
        (1-bit (z i))*sparseTable N i z/(1-1/2)) +
        (5/4 : ℝ)/N - (5/2 : ℝ)/N*bit (z i) := by
    simp only [show bit true = 1 from rfl, show bit false = 0 from rfl]
    ring
  simp_rw [hr]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcnt]
  field_simp
  <;> ring

lemma T27_linear_bound {N : ℕ} (hN : 0 < N) (z : Assignment N) :
    |linearHajek (fun _ => 1/2) (sparseTable N) z| ≤ 4/(N : ℝ) := by
  rw [T27_linear_identity hN]
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hc := T27_count_bounds z true
  have hfrac : |2*armCount z true/N-1| ≤ 1 := by
    apply abs_le.mpr
    have hlow : 0 ≤ 2*armCount z true/N := div_nonneg (by linarith [hc.1]) hn.le
    have hhigh : 2*armCount z true/N ≤ 2 := (div_le_iff₀ hn).mpr (by linarith [hc.2])
    constructor <;> linarith
  have hprod : |(5/(4*(N : ℝ))) * (2*armCount z true/N-1)| ≤ 5/(4*(N : ℝ)) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hfrac (show 0 ≤ 5/(4*(N : ℝ)) by positivity)]
  have hh := T27_ht_abs hN z
  have hb := abs_sub (ht (fun _ => 1/2) (sparseTable N) z)
    ((5/(4*(N : ℝ))) * (2*armCount z true/N-1))
  have he : 2/(N : ℝ)+5/(4*(N : ℝ)) ≤ 4/(N : ℝ) := by
    convert (div_le_div_iff_of_pos_right hn).mpr
      (show (13/4 : ℝ) ≤ 4 by norm_num) using 1 <;> ring
  linarith

lemma T27_variance_limit :
    Tendsto (fun N : ℕ => (N : ℝ)*variance (fun _ => 1/2)
      (linearHajek (fun _ => 1/2) (circleAverage (sparsePopulation N) 1))) atTop (nhds 0) := by
  have hlim : Tendsto (fun N : ℕ => (16 : ℝ)/N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [] with N
    exact mul_nonneg (Nat.cast_nonneg N) (variance_nonneg _ T27_half _)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    rw [T27_circle]
    have hn : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hb : variance (fun _ => 1/2) (linearHajek (fun _ => 1/2) (sparseTable N)) ≤
        (4/(N : ℝ))^2 := by
      apply (variance_le_second _ _).trans
      have hh := expect_mono (fun _ : Fin N => (1/2 : ℝ)) T27_half
        (fun z => (linearHajek (fun _ => 1/2) (sparseTable N) z)^2)
        (fun _ => (4/(N : ℝ))^2) (fun z => by
          have h := T27_linear_bound (by omega) z
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _)
            (show 0 ≤ 4/(N : ℝ) by positivity)).mpr h)
      simpa only [expect_const] using hh
    have he : (N : ℝ)*(4/N)^2 = 16/N := by field_simp; ring
    calc
      _ ≤ (N : ℝ)*(4/N)^2 := mul_le_mul_of_nonneg_left hb hn.le
      _ = _ := he

lemma T27_table_spike {N : ℕ} (hN : 0 < N) (z : Assignment N) (i : Fin N) :
    sparseTable N i z = if i = ⟨0,hN⟩ then 1/4+3/4*bit (z ⟨0,hN⟩) else 0 := by
  by_cases hi : i = ⟨0,hN⟩
  · subst i; simp [sparseTable]
  · have hv : i.val ≠ 0 := by intro h; apply hi; exact Fin.ext h
    simp [sparseTable, hi, hv]

lemma T27_armMean {N : ℕ} (hN : 0 < N) (z : Assignment N) (a : Bool) :
    armMean (sparseTable N) z a =
      if z ⟨0,hN⟩ = a then (1/4+3/4*bit (z ⟨0,hN⟩))/armCount z a else 0 := by
  unfold armMean
  rw [T27_arm_numerator hN]
  split_ifs <;> simp

lemma T27_diagonal_variance {N : ℕ} (hN : 2 ≤ N) (z : Assignment N) (e : Fin N → ℝ) :
    kernelVariance z e (distanceKernel (nodeSeparation (sparsePopulation N))
      uniformKernel (sparseBandwidth N)) = ∑ i, (lambda z i * e i)^2 := by
  unfold kernelVariance distanceKernel
  simp only [T27_kernel_eq hN]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, mul_one]
    ring
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

lemma T27_spike_variance {N : ℕ} (hN : 2 ≤ N) (z : Assignment N)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false) :
    let o : Fin N := ⟨0, by omega⟩
    let y := 1/4+3/4*bit (z o)
    let q := armCount z (z o)
    kernelVariance z (residual (sparseTable N) z)
      (distanceKernel (nodeSeparation (sparsePopulation N)) uniformKernel (sparseBandwidth N)) =
      y^2*(q-1)/q^3 := by
  dsimp only
  let o : Fin N := ⟨0, by omega⟩
  let y := (1/4 : ℝ)+3/4*bit (z o)
  let q := armCount z (z o)
  have hq : 0 < q := by dsimp [q]; cases z o <;> assumption
  have hr (i : Fin N) :
      (lambda z i * residual (sparseTable N) z i)^2 =
        (if i = o then y^2-2*y^2/q else 0)/q^2 +
          (if z i = z o then (1 : ℝ) else 0)*y^2/q^4 := by
    rw [residual, T27_table_spike (show 0 < N by omega), T27_armMean (show 0 < N by omega)]
    by_cases hi : i = o
    · subst i
      have ho' : o = (⟨0, by omega⟩ : Fin N) := rfl
      simp only [if_pos ho', ite_true]
      cases ha : z o <;>
        simp [lambda, bit, ha, y, q] <;>
        field_simp [h1.ne', h0.ne'] <;> ring
    · have hio : i ≠ (⟨0, by omega⟩ : Fin N) := hi
      cases ha : z o <;> cases hb : z i <;>
        simp [lambda, bit, ha, hb, hio, hi, y, q] <;>
        field_simp [h1.ne', h0.ne'] <;> ring
  rw [T27_diagonal_variance hN]
  simp_rw [hr]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.sum_div, ← Finset.sum_mul]
  have hs : (∑ i : Fin N, if i = o then y^2-2*y^2/q else 0) = y^2-2*y^2/q := by simp
  rw [hs]
  change (y^2-2*y^2/q)/q^2 + q*y^2/q^4 = y^2*(q-1)/q^3
  field_simp [hq.ne']
  <;> ring

lemma T27_true_interval (n q : ℝ) (hn : 0 < n) (hq : 2 ≤ q) (hqn : q ≤ n) :
    (-2 : ℝ) ≤ (1/q-3/(4*n))/Real.sqrt ((q-1)/q^3) ∧
      (1/q-3/(4*n))/Real.sqrt ((q-1)/q^3) ≤ 2 := by
  have hqp : 0 < q := by linarith
  have hv : 0 < (q-1)/q^3 := div_pos (by linarith) (by positivity)
  have hs : 0 < Real.sqrt ((q-1)/q^3) := Real.sqrt_pos.mpr hv
  have hc : 0 ≤ 1/q-3/(4*n) := by
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (by positivity : 0 < 4*n) hqp).mpr
    nlinarith
  have hsq : (1/(2*q))^2 ≤ (q-1)/q^3 := by
    field_simp
    nlinarith
  have hlower : 1/(2*q) ≤ Real.sqrt ((q-1)/q^3) := by
    nlinarith [Real.sq_sqrt hv.le, Real.sqrt_nonneg ((q-1)/q^3),
      show 0 < 1/(2*q) by positivity]
  constructor
  · exact (show (-2 : ℝ) ≤ 0 by norm_num).trans (div_nonneg hc hs.le)
  · apply (div_le_iff₀ hs).mpr
    have he : 1/q = 2*(1/(2*q)) := by ring
    have hcn : 1/q-3/(4*n) ≤ 1/q := sub_le_self _ (by positivity)
    linarith

lemma T27_false_interval (n q : ℝ) (hn : 0 < n) (hq : 2 ≤ q) (hqn : n < 3*q) :
    (-1/(4*q)-3/(4*n))/Real.sqrt (((1/4 : ℝ)^2)*(q-1)/q^3) < -2 := by
  have hqp : 0 < q := by linarith
  have hv : 0 < ((1/4 : ℝ)^2)*(q-1)/q^3 :=
    div_pos (mul_pos (by norm_num) (by linarith)) (by positivity)
  have hs : 0 < Real.sqrt (((1/4 : ℝ)^2)*(q-1)/q^3) := Real.sqrt_pos.mpr hv
  have hsq : ((1/4 : ℝ)^2)*(q-1)/q^3 ≤ (1/(4*q))^2 := by
    field_simp
    nlinarith
  have hupper : Real.sqrt (((1/4 : ℝ)^2)*(q-1)/q^3) ≤ 1/(4*q) := by
    nlinarith [Real.sq_sqrt hv.le, Real.sqrt_nonneg (((1/4 : ℝ)^2)*(q-1)/q^3),
      show 0 < 1/(4*q) by positivity]
  apply (div_lt_iff₀ hs).mpr
  have hcmp : 1/(4*q) < 3/(4*n) := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 4*q) (by positivity : 0 < 4*n)).mpr
    nlinarith
  rw [neg_div]
  linarith

lemma T27_selected_update {N : ℕ} (F : Assignment N → ℝ) (i : Fin N) (a : Bool) :
    expect (fun _ => 1/2) (fun z => if z i = a then F z else 0) =
      (1/2 : ℝ)*expect (fun _ => 1/2) (fun z => F (Function.update z i a)) := by
  rw [bernoulli_selection _ (fun _ z => F z) i a (by cases a <;> norm_num [coin]),
    marginal_is_marginalization _ (fun _ z => F z) i a T27_half]
  cases a <;> norm_num [coin]

/-- The first two moments of the fair arm count, proved by finite product marginalization. -/
lemma T27_count_moments {N : ℕ} (a : Bool) :
    expect (fun _ : Fin N => 1/2) (fun z => armCount z a) = (N : ℝ)/2 ∧
    variance (fun _ : Fin N => 1/2) (fun z => armCount z a) = (N : ℝ)/4 := by
  let I := fun (i : Fin N) (z : Assignment N) => if z i = a then (1 : ℝ) else 0
  have hI (i : Fin N) : expect (fun _ => 1/2) (I i) = 1/2 := by
    simpa only [I, expect_const, mul_one] using T27_selected_update (fun _ => (1 : ℝ)) i a
  have hpair (i j : Fin N) (hij : i ≠ j) :
      expect (fun _ => 1/2) (fun z => I i z * I j z) = (1/4 : ℝ) := by
    have he : (fun z => I i z * I j z) = fun z => if z i = a then I j z else 0 := by
      funext z
      dsimp [I]
      split_ifs <;> simp_all
    rw [he, T27_selected_update]
    have hu : (fun z => I j (Function.update z i a)) = I j := by
      funext z
      simp only [I, Function.update_of_ne (Ne.symm hij)]
    rw [hu, hI]
    norm_num
  have hdiag (i : Fin N) : cov (fun _ => 1/2) (I i) (I i) = (1/4 : ℝ) := by
    have he : (fun z => I i z * I i z) = I i := by
      funext z
      dsimp [I]
      split_ifs <;> norm_num
    simp only [cov, he, hI]
    norm_num
  have hoff (i j : Fin N) (hij : i ≠ j) : cov (fun _ => 1/2) (I i) (I j) = 0 := by
    simp only [cov, hpair i j hij, hI]
    norm_num
  constructor
  · change expect (fun _ => 1/2) (fun z => ∑ i, I i z) = _
    rw [expect_sum]
    simp only [hI, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · change variance (fun _ => 1/2) (fun z => ∑ i, I i z) = _
    rw [variance_sum]
    have hi (i : Fin N) : (∑ j, cov (fun _ => 1/2) (I i) (I j)) = (1/4 : ℝ) := by
      rw [Finset.sum_eq_single i]
      · exact hdiag i
      · intro j _ hji
        exact hoff i j (Ne.symm hji)
      · simp
    simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

lemma T27_fraction_moment {N : ℕ} (hN : 0 < N) :
    expect (fun _ : Fin N => 1/2) (fun z => (armCount z true/N-1/2)^2) =
      1/(4*(N : ℝ)) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hcnt := T27_count_moments (N := N) true
  have hm : expect (fun _ : Fin N => 1/2) (fun z => armCount z true/N) = 1/2 := by
    rw [expect_div, hcnt.1]
    field_simp
  have hv := variance_div (fun _ : Fin N => (1/2 : ℝ)) (fun z => armCount z true) (N : ℝ)
  rw [hcnt.2] at hv
  have hc := cov_centered (fun _ : Fin N => (1/2 : ℝ))
    (fun z => armCount z true/N) (fun z => armCount z true/N)
  simp only [hm] at hc
  change variance _ _ = _ at hc
  rw [hc] at hv
  simpa only [pow_two] using hv.trans (by field_simp <;> ring)

def T27_good {N : ℕ} (z : Assignment N) : Prop :=
    2*(N : ℝ)/5 ≤ armCount z true ∧ armCount z true ≤ 3*(N : ℝ)/5

lemma T27_bad_limit :
    Tendsto (fun N : ℕ => prob (fun _ : Fin N => 1/2) (fun z => ¬ T27_good z))
      atTop (nhds 0) := by
  have hlim : Tendsto (fun N : ℕ => (100 : ℝ)/N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall (fun _ => DesignLimits.prob_nonneg_finite _ T27_half _)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hbad : ∀ z : Assignment N, ¬ T27_good z →
        (1/20 : ℝ) < |armCount z true/N-1/2| := by
      intro z hz
      by_contra hh
      have he := abs_le.mp (le_of_not_gt hh)
      apply hz
      unfold T27_good
      have hlo : (9/20 : ℝ) ≤ armCount z true/N := by linarith [he.1]
      have hhi : armCount z true/N ≤ (11/20 : ℝ) := by linarith [he.2]
      have hcl := (le_div_iff₀ hn).mp hlo
      have hcu := (div_le_iff₀ hn).mp hhi
      constructor <;> linarith
    have hm : prob (fun _ : Fin N => 1/2) (fun z => ¬ T27_good z) ≤
        prob (fun _ : Fin N => 1/2) (fun z => (1/20 : ℝ) < |armCount z true/N-1/2|) := by
      apply expect_mono _ T27_half
      intro z
      by_cases hz : ¬ T27_good z
      · simp only [if_pos hz, if_pos (hbad z hz), le_refl]
      · simp only [if_neg hz]
        split_ifs <;> norm_num
    apply hm.trans
    have hc := (DesignLimits.dl1_proof (fun _ : Fin N => (1/2 : ℝ)) T27_half
      (fun z => armCount z true/N-1/2) (1/20) (by norm_num)).2
    rw [T27_fraction_moment (show 0 < N by omega)] at hc
    convert hc using 1 <;> ring

def T27_covered {N : ℕ} (z : Assignment N) : Prop :=
    let R := sparseTable N
    let V := kernelVariance z (residual R z)
      (distanceKernel (nodeSeparation (sparsePopulation N)) uniformKernel (sparseBandwidth N))
    (-2 : ℝ) ≤ (hajek R z-ame (fun _ => 1/2) R)/Real.sqrt V ∧
      (hajek R z-ame (fun _ => 1/2) R)/Real.sqrt V ≤ 2

lemma T27_good_coverage {N : ℕ} (hN : 10 ≤ N) (z : Assignment N) (hg : T27_good z) :
    T27_covered z ↔ z ⟨0, by omega⟩ = true := by
  have hn : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : 0 < N := by omega
  have hcomp := T27_count_complement z
  have hgood := hg
  unfold T27_good at hgood
  have h1 : 0 < armCount z true := by linarith [hgood.1]
  have h0 : 0 < armCount z false := by linarith [hgood.2]
  have hq1 : 2 ≤ armCount z true := by linarith [hgood.1]
  have hq0 : 2 ≤ armCount z false := by linarith [hgood.2]
  have hq1N : armCount z true ≤ (N : ℝ) := (T27_count_bounds z true).2
  have hq0N : (N : ℝ) < 3*armCount z false := by linarith [hgood.2]
  have hv := T27_spike_variance (show 2 ≤ N by omega) z h1 h0
  dsimp only at hv
  unfold T27_covered
  dsimp only
  rw [hv, T27_ame hn0]
  have hmean : (3/4 : ℝ)/(N : ℝ) = 3/(4*(N : ℝ)) := by ring
  rw [hmean]
  cases ha : z (⟨0, by omega⟩ : Fin N) with
  | false =>
    have he : hajek (sparseTable N) z = -1/(4*armCount z false) := by
      simp only [hajek, T27_armMean hn0, ha, Bool.false_eq_true, if_false, if_true,
        show bit false = 0 from rfl]
      ring
    rw [he]
    simp only [show bit false = 0 from rfl, mul_zero, add_zero, Bool.false_eq_true]
    have hs := T27_false_interval (N : ℝ) (armCount z false) (by linarith) hq0 hq0N
    exact iff_false_intro (fun h => (not_le_of_gt hs) h.1)
  | true =>
    have he : hajek (sparseTable N) z = 1/armCount z true := by
      simp only [hajek, T27_armMean hn0, ha, Bool.true_eq_false, if_false, if_true,
        show bit true = 1 from rfl]
      ring
    rw [he]
    simp only [show bit true = 1 from rfl]
    norm_num only [mul_one, show (1/4 : ℝ)+3/4 = 1 by norm_num, one_pow, one_mul]
    exact iff_true_intro (T27_true_interval (N : ℝ) (armCount z true)
      (by linarith) hq1 hq1N)

lemma T27_first_probability {N : ℕ} (hN : 0 < N) :
    prob (fun _ => 1/2) (fun z : Assignment N => z ⟨0,hN⟩ = true) = (1/2 : ℝ) := by
  calc
    _ = expect (fun _ : Fin N => 1/2)
        (fun z => if z ⟨0,hN⟩ = true then (1 : ℝ) else 0) := by
      unfold prob
      apply congrArg (expect (fun _ : Fin N => (1/2 : ℝ)))
      funext z
      split_ifs <;> rfl
    _ = 1/2 := by
      simpa only [expect_const, mul_one] using
        T27_selected_update (fun _ : Assignment N => (1 : ℝ)) ⟨0,hN⟩ true

lemma T27_coverage_limit :
    Tendsto (fun N : ℕ => prob (fun _ : Fin N => 1/2) T27_covered) atTop (nhds (1/2 : ℝ)) := by
  have hlower : Tendsto (fun N : ℕ => (1/2 : ℝ) -
      prob (fun _ : Fin N => 1/2) (fun z => ¬ T27_good z)) atTop (nhds (1/2 : ℝ)) := by
    simpa using tendsto_const_nhds.sub T27_bad_limit
  have hupper : Tendsto (fun N : ℕ => (1/2 : ℝ) +
      prob (fun _ : Fin N => 1/2) (fun z => ¬ T27_good z)) atTop (nhds (1/2 : ℝ)) := by
    simpa using tendsto_const_nhds.add T27_bad_limit
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 10] with N hN
    have hnp : 0 < N := by omega
    conv_lhs => lhs; rw [← T27_first_probability hnp]
    unfold prob
    rw [← expect_sub]
    apply expect_mono _ T27_half
    intro z
    dsimp only
    by_cases hg : T27_good z
    · have he := T27_good_coverage hN z hg
      simp only [if_neg (not_not.mpr hg), sub_zero]
      rw [he]
    · by_cases hb : z ⟨0,hnp⟩ = true <;> by_cases hc : T27_covered z <;>
        simp [hb, hc, hg]
  · filter_upwards [eventually_ge_atTop 10] with N hN
    have hnp : 0 < N := by omega
    conv_rhs => lhs; rw [← T27_first_probability hnp]
    unfold prob
    rw [← expect_add]
    apply expect_mono _ T27_half
    intro z
    dsimp only
    by_cases hg : T27_good z
    · have he := T27_good_coverage hN z hg
      simp only [if_neg (not_not.mpr hg), add_zero]
      rw [he]
    · by_cases hb : z ⟨0,hnp⟩ = true <;> by_cases hc : T27_covered z <;>
        simp [hb, hc, hg]

lemma T27_cdf (x : ℝ) : normalCDF x =
    ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x := by
  rw [ProbabilityTheory.cdf_eq_real]
  rfl

lemma T27_nominal :
    0 < 2*(1-normalCDF 2) ∧ 2*(1-normalCDF 2) < 1 ∧
    (3/4 : ℝ) ≤ 1-2*(1-normalCDF 2) := by
  have hstrict := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf
  have hzero := AronowAudit.P053.NormalCompletion.normal_cdf_zero
  have hlt : normalCDF 2 < 1 := by
    have hs := hstrict (show (2 : ℝ) < 3 by norm_num)
    have hu := ProbabilityTheory.cdf_le_one (ProbabilityTheory.gaussianReal 0 1) 3
    rw [T27_cdf]
    linarith
  have hgt : (1/2 : ℝ) < normalCDF 2 := by
    have hs := hstrict (show (0 : ℝ) < 2 by norm_num)
    rw [hzero] at hs
    simpa only [T27_cdf] using hs
  refine ⟨by linarith, by linarith, ?_⟩
  let γ := ProbabilityTheory.gaussianReal 0 1
  have htail : γ.real {x : ℝ | (2 : ℝ) ≤ |x|} ≤ 1/4 := by
    have hc := ProbabilityTheory.meas_ge_le_variance_div_sq
      (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) 2)
      (show (0 : ℝ) < 2 by norm_num)
    simp only [ProbabilityTheory.variance_id_gaussianReal, NNReal.coe_one,
      id_eq, ProbabilityTheory.integral_id_gaussianReal, sub_zero] at hc
    have hh := ENNReal.toReal_mono (by norm_num : ENNReal.ofReal ((1 : ℝ)/2^2) ≠ ⊤) hc
    norm_num at hh
    exact hh
  have hsub : Set.Iic (-2 : ℝ) ∪ Set.Ioi 2 ⊆ {x : ℝ | (2 : ℝ) ≤ |x|} := by
    intro x hx
    rcases hx with hx | hx
    · change x ≤ -2 at hx
      change 2 ≤ |x|
      exact (show 2 ≤ -x by linarith).trans (neg_le_abs x)
    · change 2 < x at hx
      change 2 ≤ |x|
      exact hx.le.trans (le_abs_self x)
  have hm : γ.real (Set.Iic (-2 : ℝ) ∪ Set.Ioi 2) ≤ 1/4 :=
    (measureReal_mono hsub (measure_ne_top _ _)).trans htail
  have hd : Disjoint (Set.Iic (-2 : ℝ)) (Set.Ioi 2) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' : x ≤ -2 := hx
    have hy' : 2 < x := hy
    linarith
  rw [measureReal_union hd measurableSet_Ioi] at hm
  have hcomp := measureReal_add_measureReal_compl (μ := γ) (s := Set.Iic (2 : ℝ))
    measurableSet_Iic
  simp only [Set.compl_Iic, probReal_univ] at hcomp
  have hneg : normalCDF (-2) = 1-normalCDF 2 := by
    simpa only [T27_cdf] using AronowAudit.P053.NormalCompletion.normal_cdf_neg 2
  have hleft : γ.real (Set.Iic (-2 : ℝ)) = normalCDF (-2) := rfl
  have hright : γ.real (Set.Iic (2 : ℝ)) = normalCDF 2 := rfl
  rw [hleft, hneg] at hm
  rw [hright] at hcomp
  linarith

theorem ned_coverage_counterexample_proof :
    BoundedOutcomes sparsePopulation ∧ QuadraticSpacing sparsePopulation ∧
    NEDConditions sparsePopulation (1/2) 1 ∧ KernelConditions uniformKernel ∧
    Tendsto sparseBandwidth atTop atTop ∧
    Asymptotics.IsLittleO atTop sparseBandwidth (fun N => (N : ℝ)^(1/6 : ℝ)) ∧
    (∀ N : ℕ, 3 ≤ N → WellDefined (sparsePopulation N) 1) ∧
    LiminfAtLeast (kernelHomophily sparsePopulation (1/2) 1 uniformKernel sparseBandwidth) 0 ∧
    Tendsto (fun N : ℕ => (N : ℝ)*variance (fun _ => 1/2)
      (linearHajek (fun _ => 1/2) (circleAverage (sparsePopulation N) 1))) atTop (nhds 0) ∧
    Tendsto (fun N : ℕ => prob (fun _ => 1/2) (fun z =>
      let R := circleAverage (sparsePopulation N) 1
      let V := kernelVariance z (residual R z) (distanceKernel (nodeSeparation (sparsePopulation N)) uniformKernel (sparseBandwidth N))
      (-2 : ℝ) ≤ (hajek R z-ame (fun _ => 1/2) R)/Real.sqrt V ∧
        (hajek R z-ame (fun _ => 1/2) R)/Real.sqrt V ≤ 2)) atTop (nhds (1/2)) ∧
    0 < 2*(1-normalCDF 2) ∧ 2*(1-normalCDF 2) < 1 ∧
    (3/4 : ℝ) ≤ 1-2*(1-normalCDF 2) := by
  refine ⟨T27_bounded, T27_spacing, T27_ned, T27_kernel, T27_bandwidth_diverges,
    T27_bandwidth_rate, fun N _ => T27_wellDefined N, T27_homophily,
    T27_variance_limit, ?_, T27_nominal⟩
  apply T27_coverage_limit.congr'
  filter_upwards [] with N
  apply congrArg (prob (fun _ : Fin N => (1/2 : ℝ)))
  funext z
  simp only [T27_circle]
  rfl

end
end AronowAudit.P004.Wave1
