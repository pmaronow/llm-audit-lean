import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Integral.Prod

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGP0014B1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-! Local identity, finite bootstrap bound, heavy-law cell bounds,
and transfer of the ordinary sign-indicator CLT. -/

lemma regular_local_branch (G : ℝ → ℝ) (h : |G 0-1/2| < 1/4) :
    regularHeavyFunctional G = G 0-1/2 := by
  have hb := abs_lt.mp h
  have hm : G 0 ∈ Set.Icc (1/4 : ℝ) (3/4) := by
    constructor <;> linarith
  exact if_pos hm

lemma regular_local_subtraction (F G : ℝ → ℝ) (hF : F 0 = 1/2)
    (hG : ∀ x, |G x-F x| < 1/4) :
    regularHeavyFunctional G-regularHeavyFunctional F = G 0-F 0 := by
  have hG0 : |G 0-1/2| < 1/4 := by simpa only [hF] using hG 0
  have hF0 : |F 0-1/2| < 1/4 := by rw [hF]; norm_num
  rw [regular_local_branch G hG0, regular_local_branch F hF0]
  ring

/-- A finite variance lower bound from just two distinct atoms. -/
lemma regular_two_atom_variance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ℝ) (m : ℝ) (a b : ι) (hab : a ≠ b) :
    (z a-z b)^2 ≤ 2 * ∑ i, (z i-m)^2 := by
  have hsub : ({a,b} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => sq_nonneg (z i-m))
  have hp : (z a-m)^2+(z b-m)^2 ≤ ∑ i, (z i-m)^2 := by
    simpa only [Finset.sum_pair hab] using hs
  nlinarith [sq_nonneg (z a+z b-2*m)]

lemma regular_bootstrap_two_atoms {n : ℕ} (hn : 0 < n)
    (T : (Fin n → ℝ) → ℝ) (s : Fin n → ℝ)
    (a b : Fin n → Fin n) (hab : a ≠ b) :
    (T (resample s a)-T (resample s b))^2 /
      (2*(n : ℝ)^n) ≤ bootVar T s := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hden : 0 < (n : ℝ)^n := pow_pos hnR n
  have hs := regular_two_atom_variance
    (fun c : Fin n → Fin n => T (resample s c)) (bootMean T s) a b hab
  unfold bootVar
  apply (div_le_iff₀ (mul_pos (by norm_num) hden)).mpr
  have he :
      ((∑ c : Fin n → Fin n, (T (resample s c)-bootMean T s)^2) /
        (n : ℝ)^n) * (2*(n : ℝ)^n) =
        2 * ∑ c : Fin n → Fin n, (T (resample s c)-bootMean T s)^2 := by
    field_simp [ne_of_gt hden]
    <;> ring
  rw [he]
  exact hs

lemma regular_constant_median {n : ℕ} (hn : 0 < n) (c : ℝ) :
    sampleMedian (fun _ : Fin n => c) = c := by
  unfold sampleMedian
  rw [List.ofFn_const]
  have hs : (List.replicate n c).mergeSort (fun a b => a ≤ b) = List.replicate n c :=
    List.perm_replicate.mp (List.mergeSort_perm _ _)
  rw [hs]
  exact List.getD_replicate c (Nat.div_lt_self hn (by norm_num : 1 < (2 : ℕ)))

lemma regular_constant_statistic {n : ℕ} (hn : 0 < n) (c : ℝ) :
    regularHeavyStatistic (fun _ : Fin n => c) = c := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  by_cases hc : c ≤ 0
  · have ha : ((Finset.univ.filter (fun _ : Fin n => c ≤ 0)).card : ℝ)/(n : ℝ) = 1 := by
      simp [hc, hnR]
    have hbad : ¬ (1 : ℝ) ∈ Set.Icc (1/4 : ℝ) (3/4) := by norm_num
    simpa only [regularHeavyStatistic, ha, if_neg hbad] using regular_constant_median hn c
  · have ha : ((Finset.univ.filter (fun _ : Fin n => c ≤ 0)).card : ℝ)/(n : ℝ) = 0 := by
      simp [hc]
    have hbad : ¬ (0 : ℝ) ∈ Set.Icc (1/4 : ℝ) (3/4) := by norm_num
    simpa only [regularHeavyStatistic, ha, if_neg hbad] using regular_constant_median hn c

lemma regular_nat_le_two_pow (n : ℕ) : (n : ℝ) ≤ (2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hpow : (1 : ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
    rw [Nat.cast_succ, pow_succ]
    linarith

lemma regular_sample_size_power_bound (n : ℕ) :
    (n : ℝ)^n ≤ (2 : ℝ)^(n^2) := by
  calc
    (n : ℝ)^n ≤ ((2 : ℝ)^n)^n :=
      pow_le_pow_left₀ (Nat.cast_nonneg n) (regular_nat_le_two_pow n) n
    _ = (2 : ℝ)^(n^2) := by rw [← pow_mul, pow_two]

/-- The entire pointwise bad-sample argument needs no heavy-law integration
or population second moment. Oddness is unnecessary for this implication. -/
lemma regular_bad_sample_deterministic {n : ℕ} (hn : 5 ≤ n) (s : Fin n → ℝ)
    (hhigh : ∃ i, (2 : ℝ)^(n^2) ≤ s i) (hcentral : ∃ j, |s j| ≤ 1) :
    5 < (n : ℝ)*bootVar regularHeavyStatistic s := by
  let H : ℝ := (2 : ℝ)^(n^2)
  let N : ℝ := (n : ℝ)^n
  have hn0 : 0 < n := by omega
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hH : (32 : ℝ) ≤ H := by
    have hexp : 5 ≤ n^2 := by nlinarith
    have hh := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hexp
    norm_num only [show (2 : ℝ)^5 = 32 by norm_num] at hh
    exact hh
  have hNpos : 0 < N := pow_pos (Nat.cast_pos.mpr hn0) _
  have hNH : N ≤ H := regular_sample_size_power_bound n
  obtain ⟨i,hi⟩ := hhigh
  obtain ⟨j,hj⟩ := hcentral
  change H ≤ s i at hi
  have hjupper : s j ≤ 1 := (le_abs_self _).trans hj
  have hij : i ≠ j := by
    intro he
    have hh : H ≤ s j := by simpa only [he] using hi
    linarith
  let a : Fin n → Fin n := fun _ => i
  let b : Fin n → Fin n := fun _ => j
  have hab : a ≠ b := by
    intro he
    exact hij (congrFun he ⟨0,hn0⟩)
  have hpair := regular_bootstrap_two_atoms hn0 regularHeavyStatistic s a b hab
  have ha : regularHeavyStatistic (resample s a) = s i := regular_constant_statistic hn0 (s i)
  have hb : regularHeavyStatistic (resample s b) = s j := regular_constant_statistic hn0 (s j)
  rw [ha,hb] at hpair
  have hdiff : H-1 ≤ s i-s j := by linarith
  have hsq : (H-1)^2 ≤ (s i-s j)^2 :=
    pow_le_pow_left₀ (by linarith) hdiff 2
  have hHN : H*N ≤ H^2 := by
    have hh := mul_le_mul_of_nonneg_left hNH (show (0 : ℝ) ≤ H by linarith)
    simpa only [pow_two] using hh
  have hsqH : H^2/4 ≤ (H-1)^2 := by nlinarith [sq_nonneg (H-2)]
  have hlower : H/8 ≤ (s i-s j)^2/(2*N) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hNpos)).mpr
    nlinarith
  have hV : H/8 ≤ bootVar regularHeavyStatistic s := hlower.trans hpair
  have hscaled := mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg n)
  have hbase := mul_le_mul_of_nonneg_left
    (show (4 : ℝ) ≤ H/8 by linarith) (Nat.cast_nonneg n)
  nlinarith

lemma regular_cp_tail_obstruction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ)
    (hbad : ∀ᶠ k in atTop, (3/16 : ℝ) ≤ prob μ {ω | 5 < Z k ω}) :
    ¬ CP μ Z (1/4) := by
  intro hcp
  have hzero := hcp 1 (by norm_num)
  have hsmall := hzero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 3/16 by norm_num))
  have himpossible : ∀ᶠ k : ℕ in atTop, False := by
    filter_upwards [hbad, hsmall] with k hk hsmallk
    have hs : {ω | 5 < Z k ω} ⊆ {ω | (1 : ℝ) ≤ dist (Z k ω) (1/4)} := by
      intro ω hω
      change 5 < Z k ω at hω
      rw [Set.mem_setOf_eq, Real.dist_eq]
      exact (by linarith : (1 : ℝ) ≤ Z k ω-1/4).trans (le_abs_self _)
    have hp : prob μ {ω | 5 < Z k ω} ≤
        prob μ {ω | (1 : ℝ) ≤ dist (Z k ω) (1/4)} :=
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hs)
    linarith
  obtain ⟨k,hk⟩ := himpossible.exists
  exact hk

lemma regular_heavy_transform_measurable :
    Measurable (fun u : ℝ => (2 : ℝ)^(1/u^2)) := by
  apply (Real.continuous_const_rpow (show (2 : ℝ) ≠ 0 by norm_num)).measurable.comp
  fun_prop

lemma regular_uniform_symmetric_eq :
    uniformLaw (-1) 1 = (1/2 : ℝ≥0∞) • volume.restrict (Set.Icc (-1 : ℝ) 1) := by
  unfold uniformLaw
  have hd : (fun x : ℝ => ENNReal.ofReal
      (if x ∈ Set.Icc (-1 : ℝ) 1 then (1-(-1))⁻¹ else 0)) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1/2 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;> simp [hx, Set.indicator, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)] <;> norm_num
  rw [hd, withDensity_indicator measurableSet_Icc, withDensity_const]

lemma regular_uniform_zero_one_mass : (uniformLaw 0 1) Set.univ = 1 := by
  rw [uniformLaw_zero_one_eq_restrict, Measure.restrict_apply MeasurableSet.univ]
  norm_num [Real.volume_Icc]

lemma regular_heavy_cdf_zero : cdf heavyBootstrapLaw id 0 = 1/2 := by
  have hu : uniformLaw (-1) 1 (Set.Iic 0) = 1/2 := by
    rw [regular_uniform_symmetric_eq, Measure.smul_apply,
      Measure.restrict_apply measurableSet_Iic]
    have he : Set.Iic (0 : ℝ) ∩ Set.Icc (-1 : ℝ) 1 = Set.Icc (-1 : ℝ) 0 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨hx,hl,hu⟩
        exact ⟨hl,hx⟩
      · rintro ⟨hl,hx⟩
        exact ⟨hx,hl,by linarith⟩
    rw [he]
    norm_num [Real.volume_Icc]
  have hpositive : (fun u : ℝ => (2 : ℝ)^(1/u^2)) ⁻¹' Set.Iic 0 = ∅ := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
    exact not_le_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hnegative : (fun u : ℝ => -((2 : ℝ)^(1/u^2))) ⁻¹' Set.Iic 0 = Set.univ := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
    exact neg_nonpos.mpr (Real.rpow_pos_of_pos (by norm_num) _).le
  change (heavyBootstrapLaw (Set.Iic 0)).toReal = 1/2
  rw [heavyBootstrapLaw, Measure.add_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply regular_heavy_transform_measurable measurableSet_Iic,
    Measure.map_apply (show Measurable (fun u : ℝ => -((2 : ℝ)^(1/u^2))) from regular_heavy_transform_measurable.neg) measurableSet_Iic,
    hpositive, hnegative, measure_empty, regular_uniform_zero_one_mass, hu]
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul]

lemma regular_heavy_central_lower :
    (1/2 : ℝ≥0∞) ≤ heavyBootstrapLaw (Set.Icc (-1 : ℝ) 1) := by
  have hu : uniformLaw (-1) 1 (Set.Icc (-1 : ℝ) 1) = 1 := by
    rw [regular_uniform_symmetric_eq, Measure.smul_apply,
      Measure.restrict_apply measurableSet_Icc]
    norm_num [Real.volume_Icc, ENNReal.inv_mul_cancel]
  have hfirst : (1/2 : ℝ≥0∞) =
      ((1/2 : ℝ≥0∞) • uniformLaw (-1) 1) (Set.Icc (-1 : ℝ) 1) := by
    rw [Measure.smul_apply, hu]
    simp
  unfold heavyBootstrapLaw
  rw [Measure.add_apply, Measure.add_apply]
  calc
    (1/2 : ℝ≥0∞) =
        ((1/2 : ℝ≥0∞) • uniformLaw (-1) 1) (Set.Icc (-1 : ℝ) 1) := hfirst
    _ ≤ _ := le_trans le_self_add le_self_add

lemma regular_heavy_tail_lower (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (1/(4*(n : ℝ))) ≤ heavyBootstrapLaw (Set.Ici ((2 : ℝ)^(n^2))) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hsmall : (1 : ℝ)/(n : ℝ) ≤ 1 := (div_le_one hnR).mpr hn1
  have hmass : uniformLaw 0 1 (Set.Ioc (0 : ℝ) (1/(n : ℝ))) =
      ENNReal.ofReal (1/(n : ℝ)) := by
    rw [uniformLaw_zero_one_eq_restrict, Measure.restrict_apply measurableSet_Ioc]
    have he : Set.Ioc (0 : ℝ) (1/(n : ℝ)) ∩ Set.Icc (0 : ℝ) 1 =
        Set.Ioc (0 : ℝ) (1/(n : ℝ)) := by
      apply Set.inter_eq_left.mpr
      intro u hu
      exact ⟨hu.1.le, hu.2.trans hsmall⟩
    rw [he, Real.volume_Ioc, sub_zero]
  have hsubset : Set.Ioc (0 : ℝ) (1/(n : ℝ)) ⊆
      (fun u : ℝ => (2 : ℝ)^(1/u^2)) ⁻¹' Set.Ici ((2 : ℝ)^(n^2)) := by
    intro u hu
    have hmul : u*(n : ℝ) ≤ 1 := (le_div_iff₀ hnR).mp hu.2
    have hmul0 : 0 ≤ u*(n : ℝ) := mul_nonneg hu.1.le hnR.le
    have hsq : u^2*(n : ℝ)^2 ≤ 1 := by
      have hh := mul_nonneg (sub_nonneg.mpr hmul) (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hmul0)
      nlinarith
    have hexp : ((n^2 : ℕ) : ℝ) ≤ 1/u^2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hu.1)]
      push_cast
      nlinarith
    change (2 : ℝ)^(n^2) ≤ (2 : ℝ)^(1/u^2)
    rw [← Real.rpow_natCast (2 : ℝ) (n^2)]
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hexp
  have hm : ENNReal.ofReal (1/(n : ℝ)) ≤
      ((uniformLaw 0 1).map (fun u : ℝ => (2 : ℝ)^(1/u^2)))
        (Set.Ici ((2 : ℝ)^(n^2))) := by
    rw [Measure.map_apply regular_heavy_transform_measurable measurableSet_Ici]
    rw [← hmass]
    exact measure_mono hsubset
  have hquarter : ENNReal.ofReal (1/(4*(n : ℝ))) =
      (1/4 : ℝ≥0∞)*ENNReal.ofReal (1/(n : ℝ)) := by
    rw [show (1/(4*(n : ℝ))) = (1/4 : ℝ)*(1/(n : ℝ)) by
      field_simp [hnR.ne']
      <;> ring]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/4)]
    simp [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [hquarter]
  have hpart := mul_le_mul_right hm (1/4 : ℝ≥0∞)
  have hsum :
      ((1/4 : ℝ≥0∞) • (uniformLaw 0 1).map (fun u : ℝ => (2 : ℝ)^(1/u^2)))
        (Set.Ici ((2 : ℝ)^(n^2))) ≤ heavyBootstrapLaw (Set.Ici ((2 : ℝ)^(n^2))) := by
    unfold heavyBootstrapLaw
    rw [Measure.add_apply, Measure.add_apply]
    exact (le_add_self).trans le_self_add
  exact hpart.trans (by simpa only [Measure.smul_apply, smul_eq_mul] using hsum)

lemma regular_iid_none {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X)
    (A : Set ℝ) (hA : MeasurableSet A) (n : ℕ) :
    prob μ {ω | ∀ i : Fin n, X i ω ∉ A} =
      (1-prob μ {ω | X 0 ω ∈ A})^n := by
  have hmap (i : ℕ) : μ (X i ⁻¹' Aᶜ) = μ (X 0 ⁻¹' Aᶜ) := by
    rw [← Measure.map_apply (hiid.1 i) hA.compl,
      ← Measure.map_apply (hiid.1 0) hA.compl]
    exact congrArg (fun ν : Measure ℝ => ν Aᶜ) (hiid.2.2 i).map_eq
  have he : {ω | ∀ i : Fin n, X i ω ∉ A} =
      ⋂ i ∈ Finset.range n, X i ⁻¹' Aᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range,
      Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro h i hi
      exact h ⟨i,hi⟩
    · intro h i
      exact h i i.isLt
  have hind := hiid.2.1.measure_inter_preimage_eq_mul (Finset.range n)
    (sets := fun _ => Aᶜ) (fun _ _ => hA.compl)
  unfold prob
  rw [he,hind]
  simp_rw [hmap]
  rw [Finset.prod_const, Finset.card_range, ENNReal.toReal_pow]
  have hc : (μ (X 0 ⁻¹' Aᶜ)).toReal = 1-prob μ {ω | X 0 ω ∈ A} := by
    have hh := measureReal_compl (μ := μ) (hA.preimage (hiid.1 0))
    rw [probReal_univ] at hh
    change (μ ((X 0 ⁻¹' A)ᶜ)).toReal = 1 - (μ (X 0 ⁻¹' A)).toReal at hh
    exact hh
  change _ = (1 - prob μ {ω | X 0 ω ∈ A}) ^ n
  rw [hc]

lemma regular_no_high_numeric (n : ℕ) (hn : 5 ≤ n) :
    (1-1/(4*(n : ℝ)))^n ≤ (25/32 : ℝ) := by
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (1-1/(4*(n : ℝ)))^n ≤ Real.exp (-(1/4 : ℝ)) := by
    have h := Real.one_sub_div_pow_le_exp_neg (n := n) (t := (1/4 : ℝ)) (by linarith)
    have he : (1/4 : ℝ)/(n : ℝ) = 1/(4*(n : ℝ)) := by
      field_simp
      <;> ring
    simpa only [he] using h
  have hquadratic := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 1/4 by norm_num)
  have hlow : (41/32 : ℝ) ≤ Real.exp (1/4) := by
    convert hquadratic using 1 <;> norm_num
  have hprod : Real.exp (-(1/4 : ℝ))*Real.exp (1/4) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hlow (Real.exp_pos (-(1/4 : ℝ))).le
  rw [hprod] at hm
  have he : Real.exp (-(1/4 : ℝ)) ≤ (25/32 : ℝ) := by linarith
  exact hpow.trans he

lemma regular_heavy_bad_sample_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X)
    (hlaw : μ.map (X 0) = heavyBootstrapLaw) (n : ℕ) (hn : 5 ≤ n) :
    (3/16 : ℝ) ≤ prob μ {ω | 5 < (n : ℝ)*bootVar regularHeavyStatistic (firstSample X n ω)} := by
  let H : ℝ := (2 : ℝ)^(n^2)
  let A : Set ℝ := Set.Ici H
  let C : Set ℝ := Set.Icc (-1 : ℝ) 1
  let E : Set Ω := {ω | (∃ i : Fin n, X i ω ∈ A) ∧ (∃ j : Fin n, X j ω ∈ C)}
  let N₁ : Set Ω := {ω | ∀ i : Fin n, X i ω ∉ A}
  let N₂ : Set Ω := {ω | ∀ i : Fin n, X i ω ∉ C}
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hA : MeasurableSet A := measurableSet_Ici
  have hC : MeasurableSet C := measurableSet_Icc
  have hE : MeasurableSet E := by
    have he : E = (⋃ i : Fin n, X i ⁻¹' A) ∩ (⋃ j : Fin n, X j ⁻¹' C) := by
      ext ω
      simp [E]
    rw [he]
    exact (MeasurableSet.iUnion (fun i : Fin n => hA.preimage (hiid.1 i))).inter
      (MeasurableSet.iUnion (fun j : Fin n => hC.preimage (hiid.1 j)))
  have hEA : Eᶜ = N₁ ∪ N₂ := by
    ext ω
    simp only [E,N₁,N₂,Set.mem_compl_iff,Set.mem_setOf_eq,Set.mem_union]
    simp only [not_and_or,not_exists]
  have hq : 1/(4*(n : ℝ)) ≤ prob μ {ω | X 0 ω ∈ A} := by
    have hh := regular_heavy_tail_lower n hn0
    rw [← hlaw, Measure.map_apply (hiid.1 0) measurableSet_Ici] at hh
    have hr := ENNReal.toReal_mono (measure_ne_top μ _) hh
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(4*(n : ℝ)))] at hr
    exact hr
  have hc : (1/2 : ℝ) ≤ prob μ {ω | X 0 ω ∈ C} := by
    have hh := regular_heavy_central_lower
    rw [← hlaw, Measure.map_apply (hiid.1 0) measurableSet_Icc] at hh
    have hr := ENNReal.toReal_mono (measure_ne_top μ _) hh
    norm_num at hr
    exact hr
  have hn₁ : prob μ N₁ ≤ (25/32 : ℝ) := by
    rw [show N₁ = {ω | ∀ i : Fin n, X i ω ∉ A} from rfl,
      regular_iid_none μ X hiid A hA n]
    have hle : 1-prob μ {ω | X 0 ω ∈ A} ≤ 1-1/(4*(n : ℝ)) := by linarith
    have hnon : 0 ≤ 1-prob μ {ω | X 0 ω ∈ A} := sub_nonneg.mpr measureReal_le_one
    exact (pow_le_pow_left₀ hnon hle n).trans (regular_no_high_numeric n hn)
  have hn₂ : prob μ N₂ ≤ (1/32 : ℝ) := by
    rw [show N₂ = {ω | ∀ i : Fin n, X i ω ∉ C} from rfl,
      regular_iid_none μ X hiid C hC n]
    have hle : 1-prob μ {ω | X 0 ω ∈ C} ≤ (1/2 : ℝ) := by linarith
    have hnon : 0 ≤ 1-prob μ {ω | X 0 ω ∈ C} := sub_nonneg.mpr measureReal_le_one
    calc
      _ ≤ (1/2 : ℝ)^n := pow_le_pow_left₀ hnon hle n
      _ ≤ (1/2 : ℝ)^5 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ = 1/32 := by norm_num
  have hcompl := measureReal_add_measureReal_compl (μ := μ) hE
  have hunion : prob μ Eᶜ ≤ prob μ N₁+prob μ N₂ := by
    rw [hEA]
    exact measureReal_union_le _ _
  have hElower : (3/16 : ℝ) ≤ prob μ E := by
    have he : prob μ E+prob μ Eᶜ = 1 := by
      rw [probReal_univ] at hcompl
      exact hcompl
    linarith
  apply hElower.trans
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono
  rintro ω ⟨⟨i,hi⟩,⟨j,hj⟩⟩
  exact regular_bad_sample_deterministic hn (firstSample X n ω) ⟨i,hi⟩
    ⟨j,abs_le.mpr ⟨hj.1,hj.2⟩⟩

/-- CDF comparisons use only finite subadditivity, so this lemma does not
need measurability or integrability of the values on the exceptional sets. -/
lemma regular_cd_agree_off {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z W : ℕ → Ω → ℝ)
    (B : ℕ → Set Ω) (ν : Measure ℝ)
    (hag : ∀ n ω, ω ∉ B n → Z n ω = W n ω)
    (hB : Tendsto (fun n => prob μ (B n)) atTop (nhds 0))
    (hW : CD μ W ν) : CD μ Z ν := by
  intro x hx
  have hcomp (n : ℕ) :
      cdf μ (W n) x-prob μ (B n) ≤ cdf μ (Z n) x ∧
      cdf μ (Z n) x ≤ cdf μ (W n) x+prob μ (B n) := by
    have hZW : {ω | Z n ω ≤ x} ⊆ {ω | W n ω ≤ x} ∪ B n := by
      intro ω hω
      by_cases hb : ω ∈ B n
      · exact Or.inr hb
      · exact Or.inl (by change W n ω ≤ x; rw [← hag n ω hb]; exact hω)
    have hWZ : {ω | W n ω ≤ x} ⊆ {ω | Z n ω ≤ x} ∪ B n := by
      intro ω hω
      by_cases hb : ω ∈ B n
      · exact Or.inr hb
      · exact Or.inl (by change Z n ω ≤ x; rw [hag n ω hb]; exact hω)
    have h₁ : cdf μ (Z n) x ≤ cdf μ (W n) x+prob μ (B n) :=
      (measureReal_mono hZW).trans (measureReal_union_le _ _)
    have h₂ : cdf μ (W n) x ≤ cdf μ (Z n) x+prob μ (B n) :=
      (measureReal_mono hWZ).trans (measureReal_union_le _ _)
    exact ⟨by linarith,h₁⟩
  have hlo := (hW x hx).sub hB
  have hhi := (hW x hx).add hB
  simp only [sub_zero] at hlo
  simp only [add_zero] at hhi
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    (fun n => (hcomp n).1) (fun n => (hcomp n).2)

lemma regular_sign_count {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ((Finset.univ.filter (fun i : Fin n => firstSample X n ω i ≤ 0)).card : ℝ)/(n : ℝ) =
      sampleMean (fun i ω => if X i ω ≤ 0 then (1 : ℝ) else 0) n ω := by
  unfold sampleMean
  rw [← Fin.sum_univ_eq_sum_range (fun i => if X i ω ≤ 0 then (1 : ℝ) else 0) n]
  congr 1
  rw [Finset.card_filter]
  push_cast <;> rfl

lemma regular_sign_normal_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X)
    (hq : cdf μ (X 0) 0 = 1/2) :
    CD μ (fun k ω => Real.sqrt (2*k+1)*
      regularHeavyStatistic (firstSample X (2*k+1) ω)) (gaussianReal 0 (1/4)) := by
  let g : ℝ → ℝ := fun x => if x ≤ 0 then 1 else 0
  let Z : ℕ → Ω → ℝ := fun i ω => g (X i ω)
  let p : ℕ → Ω → ℝ := sampleMean Z
  have hg : Measurable g := measurable_const.piecewise measurableSet_Iic measurable_const
  have hZ : IID μ Z := ⟨fun i => hg.comp (hiid.1 i),
    hiid.2.1.comp (fun _ => g) (fun _ => hg), fun i => (hiid.2.2 i).comp hg⟩
  have h2 : MemLp (Z 0) 2 μ := MemLp.of_bound (hZ.1 0).aestronglyMeasurable 1
    (Eventually.of_forall (fun ω => by
      by_cases hω : X 0 ω ≤ 0 <;> simp [Z,g,hω]))
  have hA : MeasurableSet {ω | X 0 ω ≤ 0} := measurableSet_le (hiid.1 0) measurable_const
  have hm : mean μ (Z 0) = 1/2 := by
    have he : mean μ (Z 0) = cdf μ (X 0) 0 := by
      change (∫ ω, {ω | X 0 ω ≤ 0}.indicator (fun _ => (1 : ℝ)) ω ∂μ) = _
      rw [integral_indicator hA]
      simp [cdf, prob, Measure.real]
    exact he.trans hq
  have hsq : (∫ ω, (Z 0 ω)^2 ∂μ) = mean μ (Z 0) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => by
      by_cases hω : X 0 ω ≤ 0 <;> simp [Z,g,hω])
  have hv : var μ (Z 0) = 1/4 := by
    rw [var,variance_eq_sub h2]
    change (∫ ω, (Z 0 ω)^2 ∂μ)-(mean μ (Z 0))^2 = _
    rw [hsq,hm]
    norm_num
  have hpos : 0 < var μ (Z 0) := by rw [hv]; norm_num
  have hclt := central_limit_finite_variance μ Z hZ h2 hpos
  have hnn : (⟨var μ (Z 0), hpos.le⟩ : ℝ≥0) = (1/4 : ℝ≥0) := by
    apply Subtype.ext
    exact hv
  rw [hm,hnn] at hclt
  have hodd : Tendsto (fun k : ℕ => 2*k+1) atTop atTop :=
    tendsto_atTop_mono (fun k => by dsimp; omega) tendsto_id
  have hW : CD μ (fun k ω => Real.sqrt (2*k+1)*(p (2*k+1) ω-1/2))
      (gaussianReal 0 (1/4)) := by
    intro x hx
    have hh := (hclt x hx).comp hodd
    convert hh using 1
    funext k
    simp only [Function.comp_apply, cdf, p, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one]
  let B : ℕ → Set Ω := fun k => {ω | p (2*k+1) ω ∉ Set.Icc (1/4 : ℝ) (3/4)}
  have hp : CP μ p (1/2) := by
    have hh := empirical_cdf_consistency μ X hiid 0
    rw [hq] at hh
    convert hh using 1
  have hB : Tendsto (fun k => prob μ (B k)) atTop (nhds 0) := by
    have hlim := (hp (1/4) (by norm_num)).comp hodd
    have hbound (k : ℕ) : prob μ (B k) ≤
        prob μ {ω | (1/4 : ℝ) ≤ dist (p (2*k+1) ω) (1/2)} := by
      apply ENNReal.toReal_mono (measure_ne_top μ _)
      apply measure_mono
      intro ω hω
      change (1/4 : ℝ) ≤ dist (p (2*k+1) ω) (1/2)
      rw [Real.dist_eq]
      by_contra h
      have hh := abs_lt.mp (lt_of_not_ge h)
      apply hω
      exact ⟨by linarith,by linarith⟩
    exact squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
      (Eventually.of_forall hbound) hlim
  apply regular_cd_agree_off μ _ _ B _ ?_ hB hW
  intro k ω hω
  have hg : p (2*k+1) ω ∈ Set.Icc (1/4 : ℝ) (3/4) := Classical.not_not.mp hω
  have hc : ((Finset.univ.filter
      (fun i : Fin (2*k+1) => firstSample X (2*k+1) ω i ≤ 0)).card : ℝ)/
        ((2*k+1 : ℕ) : ℝ) = p (2*k+1) ω := regular_sign_count X _ ω
  simp only [regularHeavyStatistic,hc,if_pos hg]

theorem regular_functional_bootstrap_variance_counterexample_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (hlaw : μ.map (X 0)=heavyBootstrapLaw) :
   (∀ G : ℝ → ℝ,(∀ x,|G x-cdf heavyBootstrapLaw id x| < 1/4) →
     regularHeavyFunctional G-regularHeavyFunctional (cdf heavyBootstrapLaw id)=G 0-cdf heavyBootstrapLaw id 0) ∧
   CD μ (fun k ω => Real.sqrt (2*k+1)*regularHeavyStatistic (firstSample X (2*k+1) ω)) (gaussianReal 0 (1/4)) ∧
   (∀ n : ℕ,Odd n → 5 ≤ n → (3/16 : ℝ) ≤ prob μ {ω |
     5 < (n : ℝ)*bootVar regularHeavyStatistic (firstSample X n ω)}) ∧
   ¬ CP μ (fun k ω => ((2*k+1 : ℕ) : ℝ)*bootVar regularHeavyStatistic (firstSample X (2*k+1) ω)) (1/4) := by
  have hlocal : ∀ G : ℝ → ℝ, (∀ x, |G x-cdf heavyBootstrapLaw id x| < 1/4) →
      regularHeavyFunctional G-regularHeavyFunctional (cdf heavyBootstrapLaw id) =
        G 0-cdf heavyBootstrapLaw id 0 := by
    intro G hG
    exact regular_local_subtraction (cdf heavyBootstrapLaw id) G regular_heavy_cdf_zero hG
  have hq : cdf μ (X 0) 0 = 1/2 := by
    change (μ (X 0 ⁻¹' Set.Iic 0)).toReal = 1/2
    rw [← Measure.map_apply (hiid.1 0) measurableSet_Iic,hlaw]
    exact regular_heavy_cdf_zero
  have hnormal := regular_sign_normal_limit μ X hiid hq
  have hbad : ∀ n : ℕ, Odd n → 5 ≤ n → (3/16 : ℝ) ≤ prob μ {ω |
      5 < (n : ℝ)*bootVar regularHeavyStatistic (firstSample X n ω)} := by
    intro n _ hn
    exact regular_heavy_bad_sample_probability μ X hiid hlaw n hn
  refine ⟨hlocal,hnormal,hbad,?_⟩
  apply regular_cp_tail_obstruction
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with k hk
  exact hbad (2*k+1) ⟨k,by omega⟩ (by omega)

/-! Finite-density KL and a.e. separated argmax identities. -/

/-- Positivity only at one fixed comparator is needed. No intersection over
the parameter space occurs here. -/
lemma averaged_kl_comparator_positive {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
    (νX : Measure (Fin K → ℝ)) (κ : Measure ℝ)
    (f : ℝ → (Fin K → ℝ) → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ)
    (hf : Measurable (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1))
    (hg : Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
    (hfn : ∀ y x, 0 ≤ f y x)
    (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω)) =
      (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (f xy.2 xy.1)))
    (hdom : ∀ᵐ xy ∂(νX.prod κ), 0 < f xy.2 xy.1 → 0 < g xy.2 xy.1 t) :
    ∀ᵐ ω ∂μ, ∀ i, 0 < g (Y i ω) (X i ω) t := by
  have hd : ∀ᵐ xy ∂(νX.prod κ).withDensity
      (fun xy => ENNReal.ofReal (f xy.2 xy.1)), 0 < g xy.2 xy.1 t := by
    apply (ae_withDensity_iff hf.ennreal_ofReal).mpr
    filter_upwards [hdom] with xy hxy hne
    exact hxy (lt_of_le_of_ne (hfn _ _) (by
      intro he
      apply hne
      simp only [← he, ENNReal.ofReal_zero]))
  rw [← htrue] at hd
  have hp : ∀ᵐ ω ∂μ, 0 < g (Y 0 ω) (X 0 ω) t :=
    (ae_map_iff (hiid.1 0).aemeasurable
      (measurableSet_lt measurable_const hg)).mp hd
  exact iid_positive_at_parameter μ X Y hiid g t hg hp

lemma averaged_kl_product_to_log {Ω : Type*} {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (n : ℕ) (ω : Ω) (s t : Fin τ → ℝ)
    (hp : ∀ i, 0 < g (Y i ω) (X i ω) s)
    (hmax : sampleLikelihood X Y g n ω s ≤ sampleLikelihood X Y g n ω t) :
    sampleLogLikelihood X Y g n ω s ≤ sampleLogLikelihood X Y g n ω t := by
  have hs : 0 < sampleLikelihood X Y g n ω s :=
    Finset.prod_pos (fun i _ => hp i)
  have ht : 0 < sampleLikelihood X Y g n ω t := lt_of_lt_of_le hs hmax
  have htf : ∀ i ∈ Finset.range n, g (Y i ω) (X i ω) t ≠ 0 :=
    Finset.prod_ne_zero_iff.mp ht.ne'
  have hl := Real.log_le_log hs hmax
  unfold sampleLikelihood at hl
  rw [Real.log_prod (fun i _ => (hp i).ne'), Real.log_prod htf] at hl
  exact div_le_div_of_nonneg_right hl (Nat.cast_nonneg n)

lemma averaged_kl_separated_argmax_ae {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Θ : Set E) (M : E → ℝ) (L : ℕ → Ω → E → ℝ)
    (that : ℕ → Ω → E) (tstar : E) (ht : tstar ∈ Θ)
    (hthat : ∀ n ω, that n ω ∈ Θ) (Δ e : ℕ → Ω → ℝ)
    (hbound : ∀ n ω t, t ∈ Θ → |L n ω t-M t| ≤ Δ n ω)
    (hopt : ∀ n, ∀ᵐ ω ∂μ, L n ω tstar-e n ω ≤ L n ω (that n ω))
    (hsep : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ t ∈ Θ, ε ≤ dist t tstar → M t ≤ M tstar-δ)
    (hΔ : CP μ Δ 0) (he : CP μ e 0) : CP μ that tstar := by
  intro ε hε
  obtain ⟨δ,hδ,hgap⟩ := hsep ε hε
  have hlim : Tendsto (fun n => prob μ {ω | δ/4 ≤ dist (Δ n ω) 0}+
      prob μ {ω | δ/2 ≤ dist (e n ω) 0}) atTop (nhds 0) := by
    simpa only [zero_add] using
      (hΔ (δ/4) (by positivity)).add (he (δ/2) (by positivity))
  have hprob (n : ℕ) : prob μ {ω | ε ≤ dist (that n ω) tstar} ≤
      prob μ {ω | δ/4 ≤ dist (Δ n ω) 0}+
      prob μ {ω | δ/2 ≤ dist (e n ω) 0} := by
    have hs : ∀ᵐ ω ∂μ, ω ∈ {ω | ε ≤ dist (that n ω) tstar} →
        ω ∈ {ω | δ/4 ≤ dist (Δ n ω) 0} ∪ {ω | δ/2 ≤ dist (e n ω) 0} := by
      filter_upwards [hopt n] with ω hop hω
      have hg := hgap (that n ω) (hthat n ω) hω
      have ha := argmax_finite_gap M (L n ω) (that n ω) tstar (Δ n ω) (e n ω)
        (hbound n ω _ (hthat n ω)) (hbound n ω tstar ht) hop
      by_contra h
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le,
        Real.dist_eq, sub_zero] at h
      have hD := (le_abs_self (Δ n ω)).trans_lt h.1
      have he' := (le_abs_self (e n ω)).trans_lt h.2
      linarith
    have hm := measure_mono_ae hs
    have hmR := ENNReal.toReal_mono (measure_ne_top μ _) hm
    exact hmR.trans (measureReal_union_le _ _)
  exact squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
    (Eventually.of_forall hprob) hlim

lemma averaged_kl_separation_global {E : Type*} [MetricSpace E]
    (Θ : Set E) (M : E → ℝ) (s : E)
    (hsep : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ t ∈ Θ, ε ≤ dist t s → M t ≤ M s-δ) :
    ∀ t ∈ Θ, M t ≤ M s := by
  intro t ht
  by_cases hd : dist t s = 0
  · have he : t = s := dist_eq_zero.mp hd
    subst t
    exact le_rfl
  · obtain ⟨δ,hδ,hgap⟩ := hsep (dist t s) (lt_of_le_of_ne dist_nonneg (Ne.symm hd))
    have hh := hgap t ht le_rfl
    linarith

/-- A density-ratio proof over the finite measure Q, rather than over the
possibly merely s-finite reference measure. -/
lemma averaged_kl_density_identity {A : Type*} [MeasurableSpace A]
    (ν : Measure A) (p q : A → ℝ) (hp : Measurable p) (hq : Measurable q)
    (hpn : ∀ x, 0 ≤ p x) (hqn : ∀ x, 0 ≤ q x)
    (hpm : (∫⁻ x, ENNReal.ofReal (p x) ∂ν) = 1)
    (hqm : (∫⁻ x, ENNReal.ofReal (q x) ∂ν) = 1)
    (hdom : ∀ᵐ x ∂ν, 0 < p x → 0 < q x)
    (hent : Integrable (fun x => p x*Real.log (p x)) ν)
    (hcross : Integrable (fun x => p x*Real.log (q x)) ν) :
    InformationTheory.klDiv
        (ν.withDensity (fun x => ENNReal.ofReal (p x)))
        (ν.withDensity (fun x => ENNReal.ofReal (q x))) =
      ENNReal.ofReal (∫ x, p x*Real.log (p x)-p x*Real.log (q x) ∂ν) ∧
    0 ≤ ∫ x, p x*Real.log (p x)-p x*Real.log (q x) ∂ν := by
  let P := ν.withDensity (fun x => ENNReal.ofReal (p x))
  let Q := ν.withDensity (fun x => ENNReal.ofReal (q x))
  let r : A → ℝ := fun x => p x/q x
  have hr : Measurable r := hp.div hq
  have hrn : ∀ x, 0 ≤ r x := fun x => div_nonneg (hpn x) (hqn x)
  letI : IsProbabilityMeasure P := ⟨by
    simpa only [P, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hpm⟩
  letI : IsProbabilityMeasure Q := ⟨by
    simpa only [Q, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hqm⟩
  have hPQ : P = Q.withDensity (fun x => ENNReal.ofReal (r x)) := by
    dsimp only [P, Q]
    rw [← withDensity_mul ν hq.ennreal_ofReal hr.ennreal_ofReal]
    apply withDensity_congr_ae
    filter_upwards [hdom] with x hx
    change ENNReal.ofReal (p x) = ENNReal.ofReal (q x)*ENNReal.ofReal (p x/q x)
    rw [← ENNReal.ofReal_mul (hqn x)]
    congr 1
    by_cases hpz : p x = 0
    · simp only [hpz, zero_div, mul_zero]
    · have hpx : 0 < p x := lt_of_le_of_ne (hpn x) (Ne.symm hpz)
      have hqx : q x ≠ 0 := (hx hpx).ne'
      field_simp [hqx]
      <;> ring
  have hAC : P ≪ Q := by
    rw [hPQ]
    exact withDensity_absolutelyContinuous _ _
  have hRN : P.rnDeriv Q =ᵐ[Q] fun x => ENNReal.ofReal (r x) := by
    rw [hPQ]
    exact Measure.rnDeriv_withDensity Q hr.ennreal_ofReal
  have hpos : ∀ᵐ x ∂P, 0 < p x ∧ 0 < q x := by
    apply (ae_withDensity_iff hp.ennreal_ofReal).mpr
    filter_upwards [hdom] with x hx hne
    have hpx : 0 < p x := by
      by_contra h
      exact hne (ENNReal.ofReal_eq_zero.mpr (le_of_not_gt h))
    exact ⟨hpx,hx hpx⟩
  have hllr : llr P Q =ᵐ[P] fun x => Real.log (p x)-Real.log (q x) := by
    filter_upwards [hAC.ae_eq hRN, hpos] with x hx hpx
    rw [llr, hx, ENNReal.toReal_ofReal (hrn x)]
    exact Real.log_div hpx.1.ne' hpx.2.ne'
  have hpR (x : A) : (ENNReal.ofReal (p x)).toReal = p x :=
    ENNReal.toReal_ofReal (hpn x)
  have hdiff : Integrable (fun x => Real.log (p x)-Real.log (q x)) P := by
    apply (integrable_withDensity_iff_integrable_smul' hp.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
    simp only [hpR, smul_eq_mul, mul_sub]
    exact hent.sub hcross
  have hli : Integrable (llr P Q) P := hdiff.congr hllr.symm
  have hL : (∫ x, llr P Q x ∂P) =
      ∫ x, p x*Real.log (p x)-p x*Real.log (q x) ∂ν := by
    rw [integral_congr_ae hllr]
    rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [hpR, smul_eq_mul, mul_sub]
  have hnonneg := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hAC hli
  have hkl := InformationTheory.klDiv_of_ac_of_integrable hAC hli
  rw [hL] at hnonneg hkl
  simpa only [probReal_univ, add_sub_cancel_right] using And.intro hkl hnonneg

/-- The finite-entropy identity for maximum-likelihood consistency.
No entropy assumption is used in the averaged-KL consistency argument. -/
lemma averaged_kl_entropy_adapter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
    (X : Ω → Fin K → ℝ) (Y : Ω → ℝ) (hXY : Measurable (fun ω => (X ω,Y ω)))
    (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX]
    (κ : Measure ℝ) [SFinite κ]
    (f : ℝ → (Fin K → ℝ) → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ)
    (hf : Measurable (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1))
    (hg : Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
    (hfn : ∀ y x, 0 ≤ f y x) (hgn : ∀ y x, 0 ≤ g y x t)
    (hfnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (f y x) ∂κ) = 1)
    (hgnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ) = 1)
    (htrue : μ.map (fun ω => (X ω,Y ω)) =
      (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (f xy.2 xy.1)))
    (hdom : ∀ᵐ xy ∂(νX.prod κ), 0 < f xy.2 xy.1 → 0 < g xy.2 xy.1 t)
    (hent : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
      f xy.2 xy.1*Real.log (f xy.2 xy.1)) (νX.prod κ))
    (hcross : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
      f xy.2 xy.1*Real.log (g xy.2 xy.1 t)) (νX.prod κ)) :
    averageKLExt νX κ f g t ≠ ∞ ∧
    (averageKLExt νX κ f g t).toReal =
      (∫ x, ∫ y, f y x*Real.log (f y x) ∂κ ∂νX)-
        expectedLogLikelihood μ X Y g t ∧
    averageKL νX κ f g t = (averageKLExt νX κ f g t).toReal := by
  let d : ((Fin K → ℝ) × ℝ) → ℝ := fun xy =>
    f xy.2 xy.1*Real.log (f xy.2 xy.1)-
      f xy.2 xy.1*Real.log (g xy.2 xy.1 t)
  let D : (Fin K → ℝ) → ℝ := fun x => ∫ y, d (x,y) ∂κ
  have hdi : Integrable d (νX.prod κ) := hent.sub hcross
  have hDi : Integrable D νX := hdi.integral_prod_left
  have hsections : ∀ᵐ x ∂νX,
      InformationTheory.klDiv
          (κ.withDensity (fun y => ENNReal.ofReal (f y x)))
          (κ.withDensity (fun y => ENNReal.ofReal (g y x t))) =
        ENNReal.ofReal (D x) ∧ 0 ≤ D x := by
    filter_upwards [hent.prod_right_ae, hcross.prod_right_ae,
      Measure.ae_ae_of_ae_prod hdom] with x hxent hxcross hxdom
    exact averaged_kl_density_identity κ (fun y => f y x) (fun y => g y x t)
      (hf.comp (measurable_const.prodMk measurable_id))
      (hg.comp (measurable_const.prodMk measurable_id))
      (fun y => hfn y x) (fun y => hgn y x)
      (hfnorm x) (hgnorm x) hxdom hxent hxcross
  have hDnonneg : 0 ≤ᵐ[νX] D := hsections.mono (fun _ h => h.2)
  have hExt : averageKLExt νX κ f g t = ENNReal.ofReal (∫ x, D x ∂νX) := by
    unfold averageKLExt
    rw [lintegral_congr_ae (hsections.mono (fun _ h => h.1))]
    exact (ofReal_integral_eq_lintegral_ofReal hDi hDnonneg).symm
  have hDintnonneg : 0 ≤ ∫ x, D x ∂νX := integral_nonneg_of_ae hDnonneg
  have hreal : (averageKLExt νX κ f g t).toReal = ∫ x, D x ∂νX := by
    rw [hExt, ENNReal.toReal_ofReal hDintnonneg]
  have hM : expectedLogLikelihood μ X Y g t =
      ∫ xy : (Fin K → ℝ) × ℝ,
        f xy.2 xy.1*Real.log (g xy.2 xy.1 t) ∂(νX.prod κ) := by
    unfold expectedLogLikelihood mean
    rw [← integral_map hXY.aemeasurable hg.log.aestronglyMeasurable, htrue]
    rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    have hfR (xy : (Fin K → ℝ) × ℝ) :
        (ENNReal.ofReal (f xy.2 xy.1)).toReal = f xy.2 xy.1 :=
      ENNReal.toReal_ofReal (hfn _ _)
    simp only [hfR, smul_eq_mul]
  have hDformula : (∫ x, D x ∂νX) =
      (∫ x, ∫ y, f y x*Real.log (f y x) ∂κ ∂νX)-
        expectedLogLikelihood μ X Y g t := by
    rw [hM, ← integral_prod d hdi]
    rw [show (∫ xy, d xy ∂(νX.prod κ)) =
      (∫ xy : (Fin K → ℝ) × ℝ, f xy.2 xy.1*Real.log (f xy.2 xy.1) ∂(νX.prod κ))-
      (∫ xy : (Fin K → ℝ) × ℝ, f xy.2 xy.1*Real.log (g xy.2 xy.1 t) ∂(νX.prod κ))
      from integral_sub hent hcross]
    rw [integral_prod _ hent]
  have hOld : averageKL νX κ f g t = ∫ x, D x ∂νX := by
    unfold averageKL conditionalKL
    apply integral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hdom] with x hx
    apply integral_congr_ae
    filter_upwards [hx] with y hy
    change f y x*Real.log (f y x/g y x t) =
      f y x*Real.log (f y x)-f y x*Real.log (g y x t)
    by_cases hz : f y x = 0
    · simp only [hz, zero_mul, sub_self]
    · have hp : 0 < f y x := lt_of_le_of_ne (hfn y x) (Ne.symm hz)
      rw [Real.log_div hz (hy hp).ne', mul_sub]
  refine ⟨?_, hreal.trans hDformula, hOld.trans hreal.symm⟩
  rw [hExt]
  exact ENNReal.ofReal_ne_top


theorem averaged_kl_ml_consistency_proof {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
  (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
  (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
  (f : ℝ → (Fin K → ℝ) → ℝ)
  (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
  (hf : Measurable (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1))
  (hfn : ∀ y x, 0 ≤ f y x) (hfnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (f y x) ∂κ)=1)
  (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω)) =
    (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (f xy.2 xy.1)))
  (Θ : Set (Fin τ → ℝ))
  (hg : ∀ t ∈ Θ, Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
  (hgn : ∀ t ∈ Θ, ∀ y x, 0 ≤ g y x t)
  (hgnorm : ∀ t ∈ Θ, ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ)=1)
  (hdom : ∀ᵐ xy ∂(νX.prod κ), ∀ t ∈ Θ, 0 < f xy.2 xy.1 → 0 < g xy.2 xy.1 t)
  (hlog : ∀ t ∈ Θ, Integrable (fun ω => Real.log (g (Y 0 ω) (X 0 ω) t)) μ)
  (tstar : Fin τ → ℝ) (ht : tstar ∈ Θ)
  (hsep : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Θ,
    ε ≤ dist t tstar → expectedLogLikelihood μ (X 0) (Y 0) g t ≤
      expectedLogLikelihood μ (X 0) (Y 0) g tstar-δ)
  (that : ℕ → Ω → Fin τ → ℝ) (hm : ∀ n, Measurable (that n))
  (hthat : ∀ n ω, that n ω ∈ Θ)
  (e Δ : ℕ → Ω → ℝ) (hen : ∀ n ω, 0 ≤ e n ω)
  (he : CP μ e 0) (hΔ : CP μ Δ 0)
  (hbound : ∀ n ω t, t ∈ Θ →
    |sampleLogLikelihood X Y g n ω t-expectedLogLikelihood μ (X 0) (Y 0) g t| ≤ Δ n ω)
  (hmax : (∀ n ω t, t ∈ Θ →
    sampleLikelihood X Y g n ω t ≤ sampleLikelihood X Y g n ω (that n ω)) ∨
    (∀ n ω t, t ∈ Θ → sampleLogLikelihood X Y g n ω t-e n ω ≤
      sampleLogLikelihood X Y g n ω (that n ω))) :
  CP μ that tstar ∧
  ((Integrable (fun xy : (Fin K → ℝ) × ℝ =>
      f xy.2 xy.1*Real.log (f xy.2 xy.1)) (νX.prod κ) ∧
    ∀ t ∈ Θ, Integrable (fun xy : (Fin K → ℝ) × ℝ =>
      f xy.2 xy.1*Real.log (g xy.2 xy.1 t)) (νX.prod κ)) →
    ∀ t ∈ Θ, averageKLExt νX κ f g tstar ≤ averageKLExt νX κ f g t) := by
  have hopt : ∀ n, ∀ᵐ ω ∂μ,
      sampleLogLikelihood X Y g n ω tstar-e n ω ≤
        sampleLogLikelihood X Y g n ω (that n ω) := by
    rcases hmax with hprod | hlogmax
    · have hdomstar : ∀ᵐ xy ∂(νX.prod κ),
          0 < f xy.2 xy.1 → 0 < g xy.2 xy.1 tstar :=
        hdom.mono (fun _ h => h tstar ht)
      have hp := averaged_kl_comparator_positive μ X Y hiid νX κ f g tstar
        hf (hg tstar ht) hfn htrue hdomstar
      intro n
      filter_upwards [hp] with ω hω
      have hl := averaged_kl_product_to_log X Y g n ω tstar (that n ω) hω
        (hprod n ω tstar ht)
      linarith [hen n ω]
    · intro n
      exact Eventually.of_forall (fun ω => hlogmax n ω tstar ht)
  have hcp : CP μ that tstar :=
    averaged_kl_separated_argmax_ae μ Θ
      (expectedLogLikelihood μ (X 0) (Y 0) g)
      (sampleLogLikelihood X Y g) that tstar ht hthat Δ e
      hbound hopt hsep hΔ he
  refine ⟨hcp, ?_⟩
  intro hentropy t ht'
  have hidentity (u : Fin τ → ℝ) (hu : u ∈ Θ) :=
    averaged_kl_entropy_adapter μ (X 0) (Y 0) (hiid.1 0) νX κ f g u hf (hg u hu)
      hfn (hgn u hu) hfnorm (hgnorm u hu) htrue
      (hdom.mono (fun _ h => h u hu)) hentropy.1 (hentropy.2 u hu)
  have hstar := hidentity tstar ht
  have hother := hidentity t ht'
  have hpop : expectedLogLikelihood μ (X 0) (Y 0) g t ≤
      expectedLogLikelihood μ (X 0) (Y 0) g tstar :=
    averaged_kl_separation_global Θ (expectedLogLikelihood μ (X 0) (Y 0) g)
      tstar hsep t ht'
  apply (ENNReal.toReal_le_toReal hstar.1 hother.1).mp
  rw [hstar.2.1, hother.2.1]
  linarith

/-! Translate the unique real averaged-KL minimum using the finite-entropy
identity, then apply product-MLE consistency. -/

theorem product_averaged_kl_ml_consistency_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (f : ℝ → (Fin K → ℝ) → ℝ)
   (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (hfmeas : Measurable (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1))
   (hfpos : ∀ y x,0 ≤ f y x) (hfnorm : ∀ x,(∫⁻ y,ENNReal.ofReal (f y x) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=
     (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (f xy.2 xy.1)))
   (Θ : Set (Fin τ → ℝ)) (hcompact : IsCompact Θ)
   (hgmeas : ∀ t∈Θ,Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
   (hgpos : ∀ t∈Θ,∀ y x,0 ≤ g y x t)
   (hgnorm : ∀ t∈Θ,∀ x,(∫⁻ y,ENNReal.ofReal (g y x t) ∂κ)=1)
   (hdom : ∀ t∈Θ,∀ᵐ xy ∂(νX.prod κ),0 < f xy.2 xy.1 → 0 < g xy.2 xy.1 t)
   (hentropy : Integrable (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1*Real.log (f xy.2 xy.1)) (νX.prod κ))
   (hcross : ∀ t∈Θ,Integrable
     (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1*Real.log (g xy.2 xy.1 t)) (νX.prod κ))
   (hM : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) g) Θ)
   (tstar : Fin τ → ℝ) (ht : tstar∈Θ)
   (hunique : ∀ t∈Θ,averageKL νX κ f g tstar ≤ averageKL νX κ f g t ∧
     (averageKL νX κ f g t=averageKL νX κ f g tstar → t=tstar))
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → sampleLikelihood X Y g n ω t ≤ sampleLikelihood X Y g n ω (that n ω))
   (Δ : ℕ → Ω → ℝ) (hbound : ∀ n ω t,t∈Θ →
     |sampleLogLikelihood X Y g n ω t-expectedLogLikelihood μ (X 0) (Y 0) g t| ≤ Δ n ω)
   (hlim : CP μ Δ 0) : CP μ that tstar := by
  let M := expectedLogLikelihood μ (X 0) (Y 0) g
  let C : ℝ := ∫ x, ∫ y, f y x*Real.log (f y x) ∂κ ∂νX
  have hid (t : Fin τ → ℝ) (ht' : t ∈ Θ) :
      averageKL νX κ f g t = C-M t := by
    have hi := averaged_kl_entropy_adapter μ (X 0) (Y 0) (hiid.1 0) νX κ f g t
      hfmeas (hgmeas t ht') hfpos (hgpos t ht') hfnorm (hgnorm t ht')
      htrue (hdom t ht') hentropy (hcross t ht')
    exact hi.2.2.trans hi.2.1
  have hu : ∀ t ∈ Θ, M t ≤ M tstar ∧ (M t = M tstar → t = tstar) := by
    intro t ht'
    have hs := hid tstar ht
    have ho := hid t ht'
    constructor
    · have hle := (hunique t ht').1
      rw [hs, ho] at hle
      linarith
    · intro heq
      apply (hunique t ht').2
      rw [hs, ho, heq]
  have hp := averaged_kl_comparator_positive μ X Y hiid νX κ f g tstar
    hfmeas (hgmeas tstar ht) hfpos htrue (hdom tstar ht)
  exact product_mle_consistency_core μ X Y g Θ hcompact tstar ht hM hu that hthat hp
    (fun n ω => hmax n ω tstar ht) Δ hbound hlim

end
end AronowAudit.P001.Wave1
