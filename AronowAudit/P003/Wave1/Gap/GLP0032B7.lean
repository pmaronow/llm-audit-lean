import AronowAudit.P003.P003_Audit
import Mathlib.Data.List.Sort
import Mathlib.Data.Rat.BigOperators

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

/-- A strict majority above a bound controls both middle order statistics. -/
lemma glp0032b7_median_majority (xs : List ℝ) (B : ℝ) (hne : xs ≠ [])
    (hmaj : xs.length < 2*(xs.filter fun x => decide (B ≤ x)).length) :
    B ≤ median xs := by
  let ys := xs.mergeSort (fun x y => x ≤ y)
  have hp : ys.Perm xs := List.mergeSort_perm _ _
  have hlen : ys.length = xs.length := hp.length_eq
  have hf : (ys.filter fun x => decide (B ≤ x)).length =
      (xs.filter fun x => decide (B ≤ x)).length := (hp.filter _).length_eq
  have hypos : 0 < ys.length := by
    rw [hlen]
    exact List.length_pos_iff_ne_nil.mpr hne
  have hyne : ys ≠ [] := List.length_pos_iff_ne_nil.mp hypos
  have hmaj' : ys.length < 2*(ys.filter fun x => decide (B ≤ x)).length := by
    simpa only [hlen, hf] using hmaj
  have hs : ys.SortedLE := List.sortedLE_mergeSort
  let a := (ys.length-1)/2
  let b := ys.length/2
  have ha : a < ys.length := by dsimp [a]; omega
  have hb : b < ys.length := by dsimp [b]; omega
  have hab : a ≤ b := by dsimp [a, b]; omega
  have hlo : B ≤ ys[a] := by
    by_contra h
    have halt : ys[a] < B := lt_of_not_ge h
    have hnil : ((ys.take (a+1)).filter fun x => decide (B ≤ x)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
      have hja : j ≤ a := by omega
      have hjlen : j < ys.length := by omega
      have hle : ys[j] ≤ ys[a] := hs.getElem_le_getElem_of_le hja
      simpa only [decide_eq_true_eq, not_le] using lt_of_le_of_lt hle halt
    have hcount : (ys.filter fun x => decide (B ≤ x)).length ≤
        ys.length - (a+1) := by
      calc
        (ys.filter fun x => decide (B ≤ x)).length =
            ((ys.drop (a+1)).filter fun x => decide (B ≤ x)).length := by
          conv_lhs => rw [← List.take_append_drop (a+1) ys]
          rw [List.filter_append, hnil, List.nil_append]
        _ ≤ (ys.drop (a+1)).length := List.length_filter_le _ _
        _ = ys.length - (a+1) := List.length_drop
    dsimp [a] at hcount
    omega
  have hhi : B ≤ ys[b] := hlo.trans (hs.getElem_le_getElem_of_le hab)
  change B ≤ if ys = [] then 0 else
    (ys[(ys.length-1)/2]! + ys[ys.length/2]!)/2
  rw [if_neg hyne, getElem!_pos ys _ ha, getElem!_pos ys _ hb]
  linarith

lemma glp0032b7_z_bounds (z : ℝ)
    (hz : 1.95996398454005 < z ∧ z < 1.95996398454006) :
    0 < z ∧ (1.95996398454005 : ℝ)^2 ≤ z^2 ∧
      z^2 ≤ (1.95996398454006 : ℝ)^2 ∧ 3 ≤ z^2 ∧ z^2 ≤ 4 := by
  have hp : 0 < z := by linarith [hz.1]
  have hl : (1.95996398454005 : ℝ)^2 ≤ z^2 :=
    (sq_le_sq₀ (by norm_num) hp.le).mpr hz.1.le
  have hu : z^2 ≤ (1.95996398454006 : ℝ)^2 :=
    (sq_le_sq₀ hp.le (by norm_num)).mpr hz.2.le
  refine ⟨hp, hl, hu, ?_, ?_⟩ <;> nlinarith

lemma glp0032b7_interval_sq (z T V : ℝ) (hz : 0 ≤ z) (hv : 0 ≤ V) :
    (0 ∈ Set.Icc (T-z*Real.sqrt V) (T+z*Real.sqrt V)) ↔ T^2 ≤ z^2*V := by
  have hw : 0 ≤ z*Real.sqrt V := mul_nonneg hz (Real.sqrt_nonneg _)
  have hsq : (z*Real.sqrt V)^2 = z^2*V := by rw [mul_pow, Real.sq_sqrt hv]
  change (T-z*Real.sqrt V ≤ 0 ∧ 0 ≤ T+z*Real.sqrt V) ↔ _
  rw [← hsq, sq_le_sq, abs_of_nonneg hw, abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma glp0032b7_coverage_certificate (z T V : ℝ) (P : Prop)
    (hz : 0 ≤ z) (hlz : 3 ≤ z^2) (huz : z^2 ≤ 4) (hv : 0 ≤ V)
    (hl : T^2 ≤ 3*V ↔ P) (hu : T^2 ≤ 4*V ↔ P) :
    (0 ∈ Set.Icc (T-z*Real.sqrt V) (T+z*Real.sqrt V)) ↔ P := by
  rw [glp0032b7_interval_sq z T V hz hv]
  constructor
  · intro h
    exact hu.mp (h.trans (mul_le_mul_of_nonneg_right huz hv))
  · intro h
    exact (hl.mpr h).trans (mul_le_mul_of_nonneg_right hlz hv)

/-- Closed rational certificates include the degenerate zero-variance endpoints. -/
lemma glp0032b7_hc1_25_certificate : ∀ k : Fin 26,
    (0 : ℚ) ≤ waldVarianceQ 25 k.val ∧
    ((waldEstimateQ 25 k.val)^2 ≤ 3*waldVarianceQ 25 k.val ↔
      10 ≤ k.val ∧ k.val ≤ 15) ∧
    ((waldEstimateQ 25 k.val)^2 ≤ 4*waldVarianceQ 25 k.val ↔
      10 ≤ k.val ∧ k.val ≤ 15) ∧
    (10 ≤ k.val ∧ k.val ≤ 15 → (1/50 : ℚ) ≤ waldVarianceQ 25 k.val) := by
  decide +kernel

def glp0032b7_hc0_variance (k : ℕ) : ℚ := 2*(k : ℚ)*(25-k)/15625

lemma glp0032b7_hc0_certificate : ∀ k : Fin 26,
    (0 : ℚ) ≤ glp0032b7_hc0_variance k.val ∧
    ((waldEstimateQ 25 k.val)^2 ≤ 3*glp0032b7_hc0_variance k.val ↔
      10 ≤ k.val ∧ k.val ≤ 15) ∧
    ((waldEstimateQ 25 k.val)^2 ≤ 4*glp0032b7_hc0_variance k.val ↔
      10 ≤ k.val ∧ k.val ≤ 15) ∧
    (10 ≤ k.val ∧ k.val ≤ 15 → (12/625 : ℚ) ≤ glp0032b7_hc0_variance k.val) := by
  decide +kernel

lemma glp0032b7_hc1_50_certificate : ∀ k : Fin 51,
    (0 : ℚ) ≤ waldVarianceQ 50 k.val ∧
    ((waldEstimateQ 50 k.val)^2 ≤ 3*waldVarianceQ 50 k.val ↔
      21 ≤ k.val ∧ k.val ≤ 29) ∧
    ((waldEstimateQ 50 k.val)^2 ≤ 4*waldVarianceQ 50 k.val ↔
      21 ≤ k.val ∧ k.val ≤ 29) := by
  decide +kernel

lemma glp0032b7_covering_width (z : ℝ)
    (hz : 1.95996398454005 < z ∧ z < 1.95996398454006)
    (k : Fin 26) (hc : 0 ∈ waldInterval z 25 k.val) :
    2*z*Real.sqrt (1/50) ≤ waldWidth z 25 k.val := by
  obtain ⟨hzpos, _, _, hlz, huz⟩ := glp0032b7_z_bounds z hz
  obtain ⟨hv, hl, hu, hmin⟩ := glp0032b7_hc1_25_certificate k
  have hcov : 10 ≤ k.val ∧ k.val ≤ 15 := by
    apply (glp0032b7_coverage_certificate z (waldEstimateQ 25 k.val)
      (waldVarianceQ 25 k.val) _ hzpos.le hlz huz
      (by exact_mod_cast hv) (by exact_mod_cast hl) (by exact_mod_cast hu)).mp hc
  have hmin' : (1/50 : ℝ) ≤ (waldVarianceQ 25 k.val : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (hmin hcov)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmin') (by positivity)

lemma glp0032b7_run_median (z : ℝ)
    (hz : 1.95996398454005 < z ∧ z < 1.95996398454006)
    (runs : List (Fin 26)) (hne : runs ≠ [])
    (hmaj : runs.length < 2*(runs.filter fun k => 0 ∈ waldInterval z 25 k.val).length) :
    2*z*Real.sqrt (1/50) ≤ median (runs.map fun k => waldWidth z 25 k.val) := by
  apply glp0032b7_median_majority _ _ (by simpa using hne)
  have hcount : (runs.filter fun k => 0 ∈ waldInterval z 25 k.val).length ≤
      ((runs.map fun k => waldWidth z 25 k.val).filter fun x =>
        decide (2*z*Real.sqrt (1/50) ≤ x)).length := by
    simp only [← List.countP_eq_length_filter, List.countP_map]
    apply List.countP_mono_left
    intro k hk hc
    simp only [Function.comp_apply, decide_eq_true_eq] at hc ⊢
    exact glp0032b7_covering_width z hz k hc
  simp only [List.length_map]
  omega

lemma glp0032b7_width_lower (z V b : ℝ)
    (hz : 1.95996398454005 < z ∧ z < 1.95996398454006)
    (hv : 0 ≤ V) (hb : 0 ≤ b)
    (hc : b^2 < 4*(1.95996398454005 : ℝ)^2*V) :
    b < 2*z*Real.sqrt V := by
  obtain ⟨hzpos, hl, _, _, _⟩ := glp0032b7_z_bounds z hz
  have hbound := mul_le_mul_of_nonneg_right hl (show 0 ≤ 4*V by positivity)
  have hs : (2*z*Real.sqrt V)^2 = 4*z^2*V := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hv]
    ring
  have hp : 0 ≤ 2*z*Real.sqrt V := by positivity
  nlinarith

lemma glp0032b7_width_upper (z V b : ℝ)
    (hz : 1.95996398454005 < z ∧ z < 1.95996398454006)
    (hv : 0 ≤ V) (hb : 0 ≤ b)
    (hc : 4*(1.95996398454006 : ℝ)^2*V < b^2) :
    2*z*Real.sqrt V < b := by
  obtain ⟨_, _, hu, _, _⟩ := glp0032b7_z_bounds z hz
  have hbound := mul_le_mul_of_nonneg_right hu (show 0 ≤ 4*V by positivity)
  have hs : (2*z*Real.sqrt V)^2 = 4*z^2*V := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hv]
    ring
  nlinarith

lemma glp0032b7_hc0 (z : ℝ)
    (hz : 1.95996398454005 < z ∧ z < 1.95996398454006)
    (k : ℕ) (hk : k ≤ 25) :
    let V₀ := 2*(k : ℝ)*(25-k)/15625
    let T := (waldEstimateQ 25 k : ℝ)
    (0 ∈ Set.Icc (T-z*Real.sqrt V₀) (T+z*Real.sqrt V₀) ↔ 10 ≤ k ∧ k ≤ 15) ∧
    (10 ≤ k ∧ k ≤ 15 → 0.54 < 2*z*Real.sqrt V₀) := by
  obtain ⟨hzpos, _, _, hlz, huz⟩ := glp0032b7_z_bounds z hz
  obtain ⟨hv, hl, hu, hmin⟩ := glp0032b7_hc0_certificate ⟨k, by omega⟩
  have hvcast : (glp0032b7_hc0_variance k : ℝ) = 2*(k : ℝ)*(25-k)/15625 := by
    norm_num [glp0032b7_hc0_variance]
  dsimp only
  rw [← hvcast]
  constructor
  · apply glp0032b7_coverage_certificate z _ _ _ hzpos.le hlz huz
      (by exact_mod_cast hv) (by exact_mod_cast hl) (by exact_mod_cast hu)
  · intro hc
    have hmin' : (12/625 : ℝ) ≤ (glp0032b7_hc0_variance k : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr (hmin hc)
    have hb : (0.54 : ℝ) < 2*z*Real.sqrt (12/625) :=
      glp0032b7_width_lower z _ _ hz (by norm_num) (by norm_num) (by norm_num)
    exact hb.trans_le (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmin') (by positivity))

lemma glp0032b7_hc1_50 (z : ℝ)
    (hz : 1.95996398454005 < z ∧ z < 1.95996398454006)
    (k : ℕ) (hk : k ≤ 50) :
    0 ∈ waldInterval z 50 k ↔ 21 ≤ k ∧ k ≤ 29 := by
  obtain ⟨hzpos, _, _, hlz, huz⟩ := glp0032b7_z_bounds z hz
  obtain ⟨hv, hl, hu⟩ := glp0032b7_hc1_50_certificate ⟨k, by omega⟩
  apply glp0032b7_coverage_certificate z _ _ _ hzpos.le hlz huz
      (by exact_mod_cast hv) (by exact_mod_cast hl) (by exact_mod_cast hu)

/-- Both closed tails are evaluated directly, retaining the boundary atoms. -/
lemma glp0032b7_mass_25 :
    ((∑ k ∈ Finset.range 26, if waldVarianceQ 25 k ≤ 77/3750
      then (binomial 25 k : ℚ)^2 else 0) / binomial 50 25 ≥ 1/2) ∧
    ((∑ k ∈ Finset.range 26, if (77/3750 : ℚ) ≤ waldVarianceQ 25 k
      then (binomial 25 k : ℚ)^2 else 0) / binomial 50 25 ≥ 1/2) := by
  decide +kernel

lemma glp0032b7_mass_50 :
    ((∑ k ∈ Finset.range 51, if waldVarianceQ 50 k ≤ 621/61250
      then (binomial 50 k : ℚ)^2 else 0) / binomial 100 50 ≥ 1/2) ∧
    ((∑ k ∈ Finset.range 51, if (621/61250 : ℚ) ≤ waldVarianceQ 50 k
      then (binomial 50 k : ℚ)^2 else 0) / binomial 100 50 ≥ 1/2) := by
  decide +kernel

lemma glp0032b7_design_median (z : ℝ) (hz : 0 < z) (m : ℕ) (v : ℚ)
    (hv : 0 < v)
    (hmass :
      ((∑ k ∈ Finset.range (m+1), if waldVarianceQ m k ≤ v
        then (binomial m k : ℚ)^2 else 0) / binomial (2*m) m ≥ 1/2) ∧
      ((∑ k ∈ Finset.range (m+1), if v ≤ waldVarianceQ m k
        then (binomial m k : ℚ)^2 else 0) / binomial (2*m) m ≥ 1/2)) :
    IsWaldMedian (waldWidth z m) m (2*z*Real.sqrt (v : ℝ)) := by
  have hz2 : 0 < 2*z := by positivity
  have hv' : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hle (k : ℕ) : waldWidth z m k ≤ 2*z*Real.sqrt (v : ℝ) ↔
      waldVarianceQ m k ≤ v := by
    unfold waldWidth
    rw [mul_le_mul_iff_right₀ hz2, Real.sqrt_le_sqrt_iff hv'.le]
    norm_cast
  have hge (k : ℕ) :
      2*z*Real.sqrt (v : ℝ) ≤ waldWidth z m k ↔ v ≤ waldVarianceQ m k := by
    unfold waldWidth
    rw [mul_le_mul_iff_right₀ hz2, Real.sqrt_le_sqrt_iff' hv']
    norm_cast
  unfold IsWaldMedian
  constructor
  · simp_rw [hle]
    simp_rw [binomial_eq_choose] at hmass
    simpa only [Rat.cast_div, Rat.cast_sum, apply_ite, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_zero, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hmass.1
  · simp_rw [hge]
    simp_rw [binomial_eq_choose] at hmass
    simpa only [Rat.cast_div, Rat.cast_sum, apply_ite, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_zero, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hmass.2

/-- P003-T8: sharp finite-run bound, HC0, and both design medians. -/
theorem wald_median_and_hc0_proof (z : ℝ)
    (hz : 1.95996398454005 < z ∧ z < 1.95996398454006) :
    (∀ runs : List (Fin 26), runs ≠ [] →
      runs.length < 2*(runs.filter fun k => 0 ∈ waldInterval z 25 k.val).length →
      2*z*Real.sqrt (1/50) ≤ median (runs.map fun k => waldWidth z 25 k.val)) ∧
    (∀ k : ℕ, k ≤ 25 →
      let V₀ := 2*(k : ℝ)*(25-k)/15625
      let T := (waldEstimateQ 25 k : ℝ)
      (0 ∈ Set.Icc (T-z*Real.sqrt V₀) (T+z*Real.sqrt V₀) ↔ 10 ≤ k ∧ k ≤ 15) ∧
      (10 ≤ k ∧ k ≤ 15 → 0.54 < 2*z*Real.sqrt V₀)) ∧
    IsWaldMedian (waldWidth z 25) 25 (2*z*Real.sqrt (77/3750)) ∧
    (∀ k : ℕ, k ≤ 50 → (0 ∈ waldInterval z 50 k ↔ 21 ≤ k ∧ k ≤ 29)) ∧
    IsWaldMedian (waldWidth z 50) 50 (2*z*Real.sqrt (621/61250)) ∧
    (0.56170 < 2*z*Real.sqrt (77/3750) ∧ 2*z*Real.sqrt (77/3750) < 0.56171) ∧
    (0.39470 < 2*z*Real.sqrt (621/61250) ∧ 2*z*Real.sqrt (621/61250) < 0.39471) := by
  have hzpos : 0 < z := (glp0032b7_z_bounds z hz).1
  refine ⟨glp0032b7_run_median z hz, glp0032b7_hc0 z hz, ?_,
    glp0032b7_hc1_50 z hz, ?_, ?_, ?_⟩
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using
      glp0032b7_design_median z hzpos 25 (77/3750) (by norm_num) glp0032b7_mass_25
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using
      glp0032b7_design_median z hzpos 50 (621/61250) (by norm_num) glp0032b7_mass_50
  · constructor
    · exact glp0032b7_width_lower z _ _ hz (by norm_num) (by norm_num) (by norm_num)
    · exact glp0032b7_width_upper z _ _ hz (by norm_num) (by norm_num) (by norm_num)
  · constructor
    · exact glp0032b7_width_lower z _ _ hz (by norm_num) (by norm_num) (by norm_num)
    · exact glp0032b7_width_upper z _ _ hz (by norm_num) (by norm_num) (by norm_num)

end AronowAudit.P003.Wave1
