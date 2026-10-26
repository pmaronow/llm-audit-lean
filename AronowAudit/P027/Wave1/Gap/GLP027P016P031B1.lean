import AronowAudit.P027.P027_Audit
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

namespace AronowAudit.P027.Wave1

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory Function
attribute [local instance] Classical.propDecidable

/-! Scalar normalization and the atomic product law. -/

def all_pps_shapeMass (s : ℝ) (j : ℕ) : ℝ :=
  (∏ i ∈ Finset.range j, (s + (i : ℝ))) / (j.factorial : ℝ) *
    (3/8 : ℝ) ^ s * (5/8 : ℝ)^j

lemma all_pps_shapeMass_pos (s : ℝ) (hs : 0 < s) (j : ℕ) :
    0 < all_pps_shapeMass s j := by
  unfold all_pps_shapeMass
  apply mul_pos
  · apply mul_pos
    · apply div_pos
      · exact Finset.prod_pos (fun i _ => by positivity)
      · exact_mod_cast Nat.factorial_pos j
    · exact Real.rpow_pos_of_pos (by norm_num) _
  · positivity

lemma all_pps_rising_product (s : ℝ) (j : ℕ) :
    (ascPochhammer ℝ j).eval s =
      ∏ i ∈ Finset.range j, (s + (i : ℝ)) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]

lemma all_pps_choose_coefficient (s : ℝ) (j : ℕ) :
    Ring.choose (s + j - 1) j =
      (∏ i ∈ Finset.range j, (s + (i : ℝ))) / (j.factorial : ℝ) := by
  rw [← Ring.multichoose_eq]
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero j)).mpr
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer s j
  simpa only [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval,
    all_pps_rising_product, mul_comm] using h

lemma all_pps_shapeMass_hasSum (s : ℝ) :
    HasSum (all_pps_shapeMass s) 1 := by
  have hball : (5/8 : ℝ) ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero]
    norm_num
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero s).hasSum hball
  simp only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    all_pps_choose_coefficient] at h
  have h' := h.mul_left ((3/8 : ℝ)^s)
  convert h' using 1
  · ext j
    dsimp [all_pps_shapeMass]
    ring
  · norm_num only [show (1 - (5/8 : ℝ)) = 3/8 by norm_num]
    exact (mul_one_div_cancel (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3/8) s).ne').symm

lemma all_pps_nbMass_pos (j : ℕ) : 0 < nbMass j :=
  all_pps_shapeMass_pos (18/5) (by norm_num) j

lemma all_pps_nbMass_hasSum : HasSum nbMass 1 :=
  all_pps_shapeMass_hasSum (18/5)

def all_pps_scalarLaw : Measure ℕ :=
  Measure.sum (fun j => ENNReal.ofReal (nbMass j) • Measure.dirac j)

lemma all_pps_scalar_singleton (j : ℕ) :
    all_pps_scalarLaw {j} = ENNReal.ofReal (nbMass j) := by
  simp [all_pps_scalarLaw, Measure.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, Set.indicator_apply, eq_comm]

lemma all_pps_scalar_probability : IsProbabilityMeasure all_pps_scalarLaw := by
  constructor
  simp only [all_pps_scalarLaw, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => (all_pps_nbMass_pos j).le)
    all_pps_nbMass_hasSum.summable, all_pps_nbMass_hasSum.tsum_eq]
  norm_num

lemma all_pps_product_singleton (N : ℕ) (v : Fin N → ℕ) :
    nbProductLawN N {v} = ENNReal.ofReal (∏ k, nbMass (v k)) := by
  simp [nbProductLawN, Measure.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, Set.indicator_apply, eq_comm]

lemma all_pps_product_eq_pi (N : ℕ) :
    nbProductLawN N = Measure.pi (fun _ : Fin N => all_pps_scalarLaw) := by
  letI : IsProbabilityMeasure all_pps_scalarLaw := all_pps_scalar_probability
  apply Measure.ext_of_singleton
  intro v
  rw [all_pps_product_singleton, Measure.pi_singleton]
  simp_rw [all_pps_scalar_singleton]
  exact ENNReal.ofReal_prod_of_nonneg (fun k _ => (all_pps_nbMass_pos (v k)).le)

lemma all_pps_product_probability (N : ℕ) : IsProbabilityMeasure (nbProductLawN N) := by
  letI : IsProbabilityMeasure all_pps_scalarLaw := all_pps_scalar_probability
  rw [all_pps_product_eq_pi]
  infer_instance

lemma all_pps_product_singleton_real (N : ℕ) (v : Fin N → ℕ) :
    (nbProductLawN N {v}).toReal = ∏ k, nbMass (v k) := by
  rw [all_pps_product_singleton, ENNReal.toReal_ofReal]
  exact Finset.prod_nonneg (fun k _ => (all_pps_nbMass_pos (v k)).le)

lemma all_pps_one_large_sum (N L : ℕ) (hN : 0 < N) :
    (∑ k : Fin N, if k.val = 0 then (L : ℝ) else 1) = (L:ℝ)+N-1 := by
  let z : Fin N := ⟨0, hN⟩
  have hz (k : Fin N) : k.val = 0 ↔ k = z := by
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp_rw [hz]
  calc
    _ = ∑ k : Fin N, ((if k = z then (L:ℝ)-1 else 0)+1) := by
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring
    _ = (L:ℝ)+N-1 := by rw [Finset.sum_add_distrib]; simp; ring

lemma all_pps_table (row : Fin 6) :
    2 ≤ ppsConfigurationN row ∧
    0 < ppsConfigurationM row ∧
    ppsConfigurationM row < ppsConfigurationN row ∧
    1 ≤ ppsConfigurationL row ∧
    ppsConfigurationL row =
      (ppsConfigurationN row-1)/(ppsConfigurationM row-1)+1 ∧
    (ppsConfigurationM row : ℝ) * ppsConfigurationL row /
      ((ppsConfigurationL row:ℝ)+ppsConfigurationN row-1) = ppsConfigurationPi row ∧
    1 < ppsConfigurationPi row := by
  fin_cases row <;>
    norm_num [ppsConfigurationN, ppsConfigurationM, ppsConfigurationL, ppsConfigurationPi]

theorem all_pps_configurations_invalid_proof (row : Fin 6) :
    let N := ppsConfigurationN row
    let m := ppsConfigurationM row
    let L := ppsConfigurationL row
    let v : Fin N → ℕ := fun k => if k.val = 0 then L-1 else 0
    let x : Fin N → ℝ := fun k => 1 + (v k : ℝ)
    2 ≤ N ∧ 0 < m ∧ m < N ∧ L = (N-1)/(m-1)+1 ∧
    (∑ k, x k) = (L:ℝ)+N-1 ∧
    (∀ k, x k = if k.val = 0 then L else 1) ∧
    (∃ k : Fin N, k.val = 0 ∧ printedPPS m x k = ppsConfigurationPi row ∧
      1 < printedPPS m x k) ∧
    IsProbabilityMeasure (nbProductLawN N) ∧
    0 < ((nbProductLawN N) {v}).toReal ∧
    ∀ (Ω' : Type) [Fintype Ω'] (D : Design (Fin N) Ω'),
      ¬ (∀ k, pi D k = printedPPS m x k) := by
  dsimp only
  obtain ⟨hN, hm, hmN, hL, hformula, hratio, hratio_gt⟩ := all_pps_table row
  let N := ppsConfigurationN row
  let m := ppsConfigurationM row
  let L := ppsConfigurationL row
  let v : Fin N → ℕ := fun k => if k.val = 0 then L-1 else 0
  let x : Fin N → ℝ := fun k => 1+(v k:ℝ)
  have hx (k : Fin N) : x k = if k.val = 0 then L else 1 := by
    dsimp [x, v]
    split_ifs
    · rw [Nat.cast_sub hL]
      push_cast
      ring
    · norm_num
  have hsum : (∑ k, x k) = (L:ℝ)+N-1 := by
    simp_rw [hx]
    simpa only [apply_ite, Nat.cast_one] using all_pps_one_large_sum N L (by omega)
  let z : Fin N := ⟨0, by omega⟩
  have hz : z.val = 0 := rfl
  have hpi : printedPPS m x z = ppsConfigurationPi row := by
    rw [printedPPS, hsum, hx, if_pos hz]
    exact hratio
  have hgt : 1 < printedPPS m x z := hpi ▸ hratio_gt
  refine ⟨hN, hm, hmN, hformula, hsum, hx, ⟨z, hz, hpi, hgt⟩,
    all_pps_product_probability N, ?_, ?_⟩
  · rw [all_pps_product_singleton_real]
    exact Finset.prod_pos (fun k _ => all_pps_nbMass_pos (v k))
  · intro Ω' _ D hD
    have hle := pi_le_one D z
    rw [hD z] at hle
    exact (not_lt_of_ge hle) hgt

/-! Factorial moments and their transport to the eight-coordinate law. -/

lemma nb_generated_rising_shift (s : ℝ) (j : ℕ) :
    (∏ i ∈ Finset.range (j+1), (s+(i:ℝ))) =
      s * (∏ i ∈ Finset.range j, (s+1+(i:ℝ))) := by
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  rw [mul_comm _ s]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

lemma nb_generated_shape_shift (s : ℝ) (j : ℕ) :
    ((j+1:ℕ):ℝ) * all_pps_shapeMass s (j+1) =
      (s*(5/3:ℝ)) * all_pps_shapeMass (s+1) j := by
  unfold all_pps_shapeMass
  rw [nb_generated_rising_shift, Nat.factorial_succ,
    Real.rpow_add (by norm_num : (0:ℝ) < 3/8), Real.rpow_one, pow_succ]
  push_cast
  field_simp
  <;> ring

lemma nb_generated_first_shape (s : ℝ) :
    HasSum (fun j : ℕ => (j:ℝ)*all_pps_shapeMass s j) (s*(5/3:ℝ)) := by
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero,
    nb_generated_shape_shift, mul_one] using
    (all_pps_shapeMass_hasSum (s+1)).mul_left (s*(5/3:ℝ))

lemma nb_generated_second_shape (s : ℝ) :
    HasSum (fun j : ℕ => (j:ℝ)*((j:ℝ)-1)*all_pps_shapeMass s j)
      ((s*(5/3:ℝ))*((s+1)*(5/3:ℝ))) := by
  apply (hasSum_nat_add_iff' 1).mp
  have ht := (nb_generated_first_shape (s+1)).mul_left (s*(5/3:ℝ))
  convert ht using 1
  · ext j
    have hh := nb_generated_shape_shift s j
    push_cast at hh ⊢
    calc
      _ = (j:ℝ)*(((j:ℝ)+1)*all_pps_shapeMass s (j+1)) := by ring
      _ = _ := by rw [hh]; ring
  · simp

lemma nb_generated_first_sum : HasSum (fun j : ℕ => (j:ℝ)*nbMass j) 6 := by
  convert nb_generated_first_shape (18/5) using 1
  · rfl
  · norm_num

lemma nb_generated_factorial_sum :
    HasSum (fun j : ℕ => (j:ℝ)*((j:ℝ)-1)*nbMass j) 46 := by
  convert nb_generated_second_shape (18/5) using 1
  · rfl
  · norm_num

lemma nb_generated_square_sum : HasSum (fun j : ℕ => (j:ℝ)^2*nbMass j) 52 := by
  convert nb_generated_factorial_sum.add nb_generated_first_sum using 1
  · ext j; ring
  · norm_num

lemma nb_generated_centered_sum :
    HasSum (fun j : ℕ => ((j:ℝ)-6)^2*nbMass j) 16 := by
  convert (nb_generated_square_sum.sub (nb_generated_first_sum.mul_left 12)).add
    (all_pps_nbMass_hasSum.mul_left 36) using 1
  · ext j; ring
  · norm_num

lemma nb_generated_scalar_integral (f : ℕ → ℝ) (a : ℝ)
    (hf : ∀ j, 0 ≤ f j) (hs : HasSum (fun j => f j*nbMass j) a) :
    Integrable f all_pps_scalarLaw ∧ (∫ j, f j ∂all_pps_scalarLaw) = a := by
  have hsum : Summable (fun j => (ENNReal.ofReal (nbMass j)).toReal * ‖f j‖) := by
    simpa only [ENNReal.toReal_ofReal (all_pps_nbMass_pos _).le,
      Real.norm_eq_abs, abs_of_nonneg (hf _), mul_comm] using hs.summable
  refine ⟨integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top) hsum, ?_⟩
  rw [all_pps_scalarLaw, integral_sum_dirac_eq_tsum (fun _ => ENNReal.ofReal_ne_top) hsum]
  simpa only [ENNReal.toReal_ofReal (all_pps_nbMass_pos _).le, smul_eq_mul,
    mul_comm] using hs.tsum_eq

lemma nb_generated_coordinate_map (N : ℕ) (k : Fin N) :
    (nbProductLawN N).map (fun v => v k) = all_pps_scalarLaw := by
  letI : IsProbabilityMeasure all_pps_scalarLaw := all_pps_scalar_probability
  rw [all_pps_product_eq_pi]
  exact (measurePreserving_eval (fun _ : Fin N => all_pps_scalarLaw) k).map_eq

lemma nb_generated_coordinate_integral (N : ℕ) (k : Fin N) (f : ℕ → ℝ) (a : ℝ)
    (hf : ∀ j, 0 ≤ f j) (hs : HasSum (fun j => f j*nbMass j) a) :
    Integrable (fun v => f (v k)) (nbProductLawN N) ∧
      (∫ v, f (v k) ∂nbProductLawN N) = a := by
  obtain ⟨hi, he⟩ := nb_generated_scalar_integral f a hf hs
  have hm : (nbProductLawN N).map (fun v => v k) = all_pps_scalarLaw :=
    nb_generated_coordinate_map N k
  have him : Integrable f ((nbProductLawN N).map (fun v => v k)) := hm.symm ▸ hi
  refine ⟨him.comp_measurable (measurable_pi_apply k), ?_⟩
  rw [← integral_map (measurable_pi_apply k).aemeasurable him.aestronglyMeasurable, hm]
  exact he

lemma nb_generated_cylinder (N : ℕ) (k : Fin N) (j : ℕ) :
    (nbProductLawN N {v | v k = j}).toReal = nbMass j := by
  have hm := congrArg (fun μ : Measure ℕ => μ {j}) (nb_generated_coordinate_map N k)
  rw [Measure.map_apply (measurable_pi_apply k) (measurableSet_singleton j),
    all_pps_scalar_singleton] at hm
  rw [show {v | v k = j} = (fun v : Fin N → ℕ => v k) ⁻¹' {j} from rfl, hm,
    ENNReal.toReal_ofReal (all_pps_nbMass_pos j).le]

lemma nb_generated_witness_mass :
    (nbProductLaw {nbWitness}).toReal = nbMass 29*nbMass 0^7 := by
  change (nbProductLawN 8 {nbWitness}).toReal = _
  rw [all_pps_product_singleton_real]
  rw [Fin.prod_univ_succ]
  simp [nbWitness]

theorem nb_generated_witness_proof :
    IsProbabilityMeasure nbProductLaw ∧
    (∀ (k : Fin 8) (j : ℕ), (nbProductLaw {v | v k = j}).toReal = nbMass j) ∧
    (∀ k : Fin 8, outcomeE nbProductLaw (fun v => (v k:ℝ)) = 6 ∧
      outcomeE nbProductLaw (fun v => ((v k:ℝ)-6)^2) = 16) ∧
    (nbProductLaw {nbWitness}).toReal = nbMass 29*nbMass 0^7 ∧
    0 < (nbProductLaw {nbWitness}).toReal := by
  refine ⟨all_pps_product_probability 8, nb_generated_cylinder 8, ?_,
    nb_generated_witness_mass, ?_⟩
  · intro k
    exact ⟨(nb_generated_coordinate_integral 8 k (fun j => (j:ℝ)) 6
      (fun j => by positivity) nb_generated_first_sum).2,
      (nb_generated_coordinate_integral 8 k (fun j => ((j:ℝ)-6)^2) 16
      (fun j => sq_nonneg _) nb_generated_centered_sum).2⟩
  · rw [nb_generated_witness_mass]
    exact nb_witness_positive

/-! Half-open cumulative intervals and the uniform-start law. -/

lemma systematic_left_nonneg {N : ℕ} (π : Fin N → ℝ)
    (hp : ∀ k, 0 ≤ π k) (k : Fin N) : 0 ≤ cumulativeLeft π k := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hp a
  · exact le_rfl

lemma systematic_left_zero {N : ℕ} (π : Fin (N+1) → ℝ) :
    cumulativeLeft π 0 = 0 := by simp [cumulativeLeft]

lemma systematic_left_succ {N : ℕ} (π : Fin (N+1) → ℝ) (k : Fin N) :
    cumulativeLeft π k.succ = π 0+cumulativeLeft (fun a => π a.succ) k := by
  unfold cumulativeLeft
  rw [Fin.sum_univ_succ]
  simp

lemma systematic_right_le_total {N : ℕ} (π : Fin N → ℝ)
    (hp : ∀ k, 0 ≤ π k) (k : Fin N) :
    cumulativeLeft π k+π k ≤ ∑ a, π a := by
  have heq : cumulativeLeft π k+π k =
      ∑ a, ((if a.val < k.val then π a else 0)+(if a = k then π a else 0)) := by
    simp [Finset.sum_add_distrib, cumulativeLeft]
  rw [heq]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a = k
  · subst a; simp
  · by_cases hlt : a.val < k.val
    · simp [ha, hlt]
    · simpa [ha, hlt] using hp a

lemma systematic_interval_owner {N : ℕ} (π : Fin N → ℝ)
    (hp : ∀ k, 0 ≤ π k) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < ∑ k, π k) :
    ∃! k, cumulativeLeft π k ≤ t ∧ t < cumulativeLeft π k+π k := by
  induction N generalizing t with
  | zero =>
      simp only [Fin.sum_univ_zero] at ht₁
      exact (not_lt_of_ge ht₀ ht₁).elim
  | succ N ih =>
      by_cases hfirst : t < π 0
      · refine ⟨0, by simpa only [systematic_left_zero, zero_add] using And.intro ht₀ hfirst, ?_⟩
        intro k
        refine Fin.cases (fun _ => rfl) (fun a ha => ?_) k
        simp only [systematic_left_succ] at ha
        have hnonneg := systematic_left_nonneg (fun b => π b.succ) (fun b => hp b.succ) a
        linarith [ha.1]
      · have htail₀ : 0 ≤ t-π 0 := sub_nonneg.mpr (le_of_not_gt hfirst)
        have htail₁ : t-π 0 < ∑ k : Fin N, π k.succ := by
          rw [Fin.sum_univ_succ] at ht₁
          linarith
        obtain ⟨a, ha, huniq⟩ := ih (fun b => π b.succ) (fun b => hp b.succ)
          (t-π 0) htail₀ htail₁
        refine ⟨a.succ, ?_, ?_⟩
        · simp only [systematic_left_succ]
          constructor <;> linarith [ha.1, ha.2]
        · intro k
          refine Fin.cases ?_ (fun b hb => ?_) k
          · intro hzero
            simp only [systematic_left_zero, zero_add] at hzero
            exact (hfirst hzero.2).elim
          · simp only [systematic_left_succ] at hb
            have hba : b = a := huniq b ⟨by linarith [hb.1], by linarith [hb.2]⟩
            exact congrArg Fin.succ hba

lemma systematic_grid_unique {m : ℕ} (s t u : ℝ) (hwidth : t-s ≤ 1)
    (i j : Fin m) (hi : s ≤ u+(i:ℝ) ∧ u+(i:ℝ) < t)
    (hj : s ≤ u+(j:ℝ) ∧ u+(j:ℝ) < t) : i = j := by
  rcases lt_trichotomy i.val j.val with hij | hij | hji
  · have hstep : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
    linarith [hi.1, hj.2]
  · exact Fin.ext hij
  · have hstep : (j:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hji
    linarith [hj.1, hi.2]

lemma systematic_selection_iff {N : ℕ} (π : Fin N → ℝ) (m : ℕ)
    (hm : 0 < m) (hs : ∑ k, π k = m) (u : ℝ) (k : Fin N) :
    systematicSelected π m u k ↔
      ∃ j : Fin m, cumulativeLeft π k ≤ u+(j:ℝ) ∧
        u+(j:ℝ) < cumulativeLeft π k+π k := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [systematicSelected, hs, div_self hm', mul_one]

lemma systematic_unique_sum {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p]
    (h : ∃! a, p a) :
    (∑ a, if p a then (1:ℕ) else 0) = 1 := by
  obtain ⟨a, ha, huniq⟩ := h
  rw [Finset.sum_eq_single a]
  · simp [ha]
  · intro b _ hba
    exact if_neg (fun hb => hba (huniq b hb))
  · simp

lemma systematic_cardinality {N : ℕ} (π : Fin N → ℝ) (m : ℕ) (hm : 0 < m)
    (hp : ∀ k, 0 < π k ∧ π k ≤ 1) (hs : ∑ k, π k = m)
    (u : ℝ) (hu₀ : 0 ≤ u) (hu₁ : u < 1) :
    (Finset.univ.filter (fun k => systematicSelected π m u k)).card = m := by
  have hrow (k : Fin N) :
      (if systematicSelected π m u k then (1:ℕ) else 0) =
        ∑ j : Fin m, if cumulativeLeft π k ≤ u+(j:ℝ) ∧
          u+(j:ℝ) < cumulativeLeft π k+π k then 1 else 0 := by
    rw [systematic_selection_iff π m hm hs]
    split_ifs with hex
    · symm
      apply systematic_unique_sum
      obtain ⟨j, hj⟩ := hex
      refine ⟨j, hj, ?_⟩
      intro i hi
      exact systematic_grid_unique _ _ u (by linarith [(hp k).2]) i j hi hj
    · symm
      apply Finset.sum_eq_zero
      intro j _
      exact if_neg (fun hj => hex ⟨j, hj⟩)
  calc
    _ = ∑ k : Fin N, if systematicSelected π m u k then (1:ℕ) else 0 := by simp
    _ = ∑ k : Fin N, ∑ j : Fin m,
        if cumulativeLeft π k ≤ u+(j:ℝ) ∧
          u+(j:ℝ) < cumulativeLeft π k+π k then 1 else 0 :=
      Finset.sum_congr rfl (fun k _ => hrow k)
    _ = ∑ j : Fin m, ∑ k : Fin N,
        if cumulativeLeft π k ≤ u+(j:ℝ) ∧
          u+(j:ℝ) < cumulativeLeft π k+π k then 1 else 0 := Finset.sum_comm
    _ = ∑ _ : Fin m, 1 := by
      apply Finset.sum_congr rfl
      intro j _
      apply systematic_unique_sum
      apply systematic_interval_owner π (fun k => (hp k).1.le) (u+(j:ℝ))
      · positivity
      · rw [hs]
        have hj : (j:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast Nat.succ_le_of_lt j.isLt
        linarith
    _ = m := by simp

def systematic_startPiece (s t j : ℝ) : Set ℝ :=
  Set.Ico 0 1 ∩ Set.Ico (s-j) (t-j)

def systematic_cellPiece (s t j : ℝ) : Set ℝ :=
  Set.Ico s t ∩ Set.Ico j (j+1)

lemma systematic_piece_volume (s t j : ℝ) :
    volume (systematic_startPiece s t j) = volume (systematic_cellPiece s t j) := by
  unfold systematic_startPiece systematic_cellPiece
  rw [Set.Ico_inter_Ico, Set.Ico_inter_Ico, Real.volume_Ico, Real.volume_Ico]
  congr 1
  change min 1 (t-j) - max 0 (s-j) = min t (j+1) - max s j
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma systematic_start_disjoint (m : ℕ) (s t : ℝ) (hwidth : t-s ≤ 1) :
    Pairwise (Disjoint on (fun j : Fin m => systematic_startPiece s t (j:ℝ))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro u hui huj
  apply hij
  exact systematic_grid_unique s t u hwidth i j
    ⟨by linarith [hui.2.1], by linarith [hui.2.2]⟩
    ⟨by linarith [huj.2.1], by linarith [huj.2.2]⟩

lemma systematic_cell_disjoint (m : ℕ) (s t : ℝ) :
    Pairwise (Disjoint on (fun j : Fin m => systematic_cellPiece s t (j:ℝ))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro u hui huj
  have heq : i = j := by
    rcases lt_trichotomy i.val j.val with h | h | h
    · have hstep : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
      linarith [hui.2.2, huj.2.1]
    · exact Fin.ext h
    · have hstep : (j:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
      linarith [huj.2.2, hui.2.1]
  exact hij heq

lemma systematic_cell_union (m : ℕ) (s t : ℝ) (hs : 0 ≤ s) (ht : t ≤ m) :
    (⋃ j : Fin m, systematic_cellPiece s t (j:ℝ)) = Set.Ico s t := by
  ext u
  constructor
  · intro hu
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hu
    exact hj.1
  · intro hu
    have hu₀ : 0 ≤ u := hs.trans hu.1
    have hfloor : ⌊u⌋₊ < m := (Nat.floor_lt hu₀).mpr (hu.2.trans_le ht)
    apply Set.mem_iUnion.mpr
    refine ⟨⟨⌊u⌋₊, hfloor⟩, hu, ?_⟩
    exact ⟨Nat.floor_le hu₀, Nat.lt_floor_add_one u⟩

lemma systematic_grid_volume (m : ℕ) (s t : ℝ) (hs : 0 ≤ s) (ht : t ≤ m)
    (hwidth : t-s ≤ 1) :
    volume (Set.Ico 0 1 ∩ {u | ∃ j : Fin m, s ≤ u+(j:ℝ) ∧ u+(j:ℝ) < t}) =
      ENNReal.ofReal (t-s) := by
  have hset : Set.Ico 0 1 ∩ {u | ∃ j : Fin m, s ≤ u+(j:ℝ) ∧ u+(j:ℝ) < t} =
      ⋃ j : Fin m, systematic_startPiece s t (j:ℝ) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_setOf_eq,
      Set.mem_iUnion, systematic_startPiece]
    constructor
    · rintro ⟨hu, j, hj⟩
      exact ⟨j, hu, ⟨by linarith [hj.1], by linarith [hj.2]⟩⟩
    · rintro ⟨j, hu, hj⟩
      exact ⟨hu, j, ⟨by linarith [hj.1], by linarith [hj.2]⟩⟩
  rw [hset, measure_iUnion (systematic_start_disjoint m s t hwidth)
    (fun _ => measurableSet_Ico.inter measurableSet_Ico), tsum_fintype]
  calc
    _ = ∑ j : Fin m, volume (systematic_cellPiece s t (j:ℝ)) :=
      Finset.sum_congr rfl (fun j _ => systematic_piece_volume s t (j:ℝ))
    _ = volume (⋃ j : Fin m, systematic_cellPiece s t (j:ℝ)) := by
      rw [measure_iUnion (systematic_cell_disjoint m s t)
        (fun _ => measurableSet_Ico.inter measurableSet_Ico), tsum_fintype]
    _ = ENNReal.ofReal (t-s) := by rw [systematic_cell_union m s t hs ht, Real.volume_Ico]

lemma systematic_selection_measurable {N : ℕ} (π : Fin N → ℝ) (m : ℕ)
    (hm : 0 < m) (hs : ∑ k, π k = m) (k : Fin N) :
    MeasurableSet {u | systematicSelected π m u k} := by
  have hset : {u | systematicSelected π m u k} =
      ⋃ j : Fin m, Set.Ico (cumulativeLeft π k-(j:ℝ))
        (cumulativeLeft π k+π k-(j:ℝ)) := by
    ext u
    simp only [Set.mem_setOf_eq, systematic_selection_iff π m hm hs,
      Set.mem_iUnion, Set.mem_Ico]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, by linarith [hj.1], by linarith [hj.2]⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, by linarith [hj.1], by linarith [hj.2]⟩
  rw [hset]
  exact MeasurableSet.iUnion (fun _ => measurableSet_Ico)

lemma systematic_marginal_integral {N : ℕ} (π : Fin N → ℝ) (m : ℕ) (hm : 0 < m)
    (hp : ∀ k, 0 < π k ∧ π k ≤ 1) (hs : ∑ k, π k = m) (k : Fin N) :
    (∫ u : ℝ, (if systematicSelected π m u k then (1:ℝ) else 0)
      ∂(volume.restrict (Set.Ico 0 1))) = π k := by
  let E : Set ℝ := {u | systematicSelected π m u k}
  have hE : MeasurableSet E := systematic_selection_measurable π m hm hs k
  change (∫ u : ℝ, E.indicator (fun _ => (1:ℝ)) u
    ∂(volume.restrict (Set.Ico 0 1))) = π k
  rw [integral_indicator_const 1 hE, smul_eq_mul, mul_one,
    measureReal_restrict_apply hE]
  change (volume (E ∩ Set.Ico 0 1)).toReal = π k
  rw [Set.inter_comm]
  have heq : Set.Ico 0 1 ∩ E = Set.Ico 0 1 ∩
      {u | ∃ j : Fin m, cumulativeLeft π k ≤ u+(j:ℝ) ∧
        u+(j:ℝ) < cumulativeLeft π k+π k} := by
    ext u
    simp only [E, Set.mem_inter_iff, Set.mem_setOf_eq, systematic_selection_iff π m hm hs]
  rw [heq, systematic_grid_volume m (cumulativeLeft π k) (cumulativeLeft π k+π k)
    (systematic_left_nonneg π (fun a => (hp a).1.le) k)
    (by rw [← hs]; exact systematic_right_le_total π (fun a => (hp a).1.le) k)
    (by linarith [(hp k).2])]
  simpa only [add_sub_cancel_left] using ENNReal.toReal_ofReal (hp k).1.le

theorem systematic_probability_construction_proof {N : ℕ} (hN : 2 ≤ N)
    (m : ℕ) (hm : 0 < m) (hmN : m < N)
    (π : Fin N → ℝ) (hp : ∀ k, 0 < π k ∧ π k ≤ 1) (hs : ∑ k, π k = m) :
    (∀ u : ℝ, 0 ≤ u → u < 1 →
      (Finset.univ.filter (fun k => systematicSelected π m u k)).card = m) ∧
    (∀ k, (∫ u : ℝ, (if systematicSelected π m u k then (1:ℝ) else 0)
      ∂(MeasureTheory.volume.restrict (Set.Ico 0 1))) = π k) := by
  exact ⟨fun u hu₀ hu₁ => systematic_cardinality π m hm hp hs u hu₀ hu₁,
    systematic_marginal_integral π m hm hp hs⟩

end
end AronowAudit.P027.Wave1
