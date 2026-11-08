import SAP.P022.WH.W1.Leaves
import AronowAudit.P022.P022_Variance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T1_L4

open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal
noncomputable section

lemma threshold_pos (q : ℕ) : 0 < perturbedThreshold q := by
  unfold perturbedThreshold
  have hD : (0 : ℝ) < (q : ℝ) + 6 := by positivity
  have hsmall : 1 / (2 * ((q : ℝ) + 6)) < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < 2 * ((q : ℝ) + 6))]
    nlinarith
  linarith

lemma threshold_lt_one (q : ℕ) : perturbedThreshold q < 1 := by
  unfold perturbedThreshold
  have hD : (0 : ℝ) < (q : ℝ) + 6 := by positivity
  have : 0 < 1 / (2 * ((q : ℝ) + 6)) := by positivity
  linarith

lemma row_below_threshold (q : ℕ) (t : Bool)
    (i : Fin (perturbedCornerWitness.design q).N) :
    rowOutcomes perturbedCornerWitness t q i ≤ perturbedThreshold q := by
  have hi : (i.val : ℝ) + 3 ≤ (q : ℝ) + 6 := by
    have hn : i.val < q + 4 := by
      change i.val < q + 4
      exact i.isLt
    exact_mod_cast (show i.val + 3 ≤ q + 6 by omega)
  have hd : (0 : ℝ) < (i.val : ℝ) + 3 := by positivity
  have hD : (0 : ℝ) < (q : ℝ) + 6 := by positivity
  have hrecip : 1 / ((q : ℝ) + 6) ≤ 1 / ((i.val : ℝ) + 3) :=
    one_div_le_one_div_of_le hd hi
  have hhalf : 1 / (2 * ((q : ℝ) + 6)) < 1 / ((q : ℝ) + 6) := by
    apply one_div_lt_one_div_of_lt hD
    nlinarith
  have hshift : 1 / (2 * ((q : ℝ) + 6)) < 1 / ((i.val : ℝ) + 3) :=
    hhalf.trans_le hrecip
  cases t
  · change (if i.val % 2 = 0 then 0 else 1) -
      1 / ((i.val : ℝ) + 3) ≤ perturbedThreshold q
    by_cases hb : i.val % 2 = 0
    · rw [if_pos hb]
      calc
        0 - 1 / ((i.val : ℝ) + 3) ≤ 0 :=
          sub_nonpos.mpr (by positivity)
        _ ≤ perturbedThreshold q := (threshold_pos q).le
    · rw [if_neg hb]
      change 1 - 1 / ((i.val : ℝ) + 3) ≤ 1 - 1 / (2 * ((q : ℝ) + 6))
      exact sub_le_sub_left hshift.le 1
  · change (if i.val % 4 < 2 then 0 else 1) -
      1 / ((i.val : ℝ) + 3) ≤ perturbedThreshold q
    by_cases hb : i.val % 4 < 2
    · rw [if_pos hb]
      calc
        0 - 1 / ((i.val : ℝ) + 3) ≤ 0 :=
          sub_nonpos.mpr (by positivity)
        _ ≤ perturbedThreshold q := (threshold_pos q).le
    · rw [if_neg hb]
      change 1 - 1 / ((i.val : ℝ) + 3) ≤ 1 - 1 / (2 * ((q : ℝ) + 6))
      exact sub_le_sub_left hshift.le 1

lemma population_cdf_at_threshold (q : ℕ) (t : Bool) :
    empiricalCDF (rowOutcomes perturbedCornerWitness t q) (perturbedThreshold q) = 1 := by
  have hbelow := row_below_threshold q t
  have hN : 0 < (perturbedCornerWitness.design q).N := by
    have h := (perturbedCornerWitness.design q).population_min
    omega
  unfold empiricalCDF
  have hconst : (fun i : Fin (perturbedCornerWitness.design q).N =>
      if rowOutcomes perturbedCornerWitness t q i ≤ perturbedThreshold q then (1 : ℝ) else 0) =
      fun _ => 1 := by
    funext i
    simp [hbelow i]
  rw [hconst]
  exact mean_const hN 1

lemma sampled_cdf_at_threshold (q : ℕ) (t : Bool)
    (π : Assignment (perturbedCornerWitness.design q)) :
    sampledCDF perturbedCornerWitness t q π (perturbedThreshold q) = 1 := by
  cases t
  · change empiricalCDF
      (observedControl (perturbedCornerWitness.design q)
        (rowOutcomes perturbedCornerWitness false q) π) (perturbedThreshold q) = 1
    have hbelow : ∀ i, observedControl (perturbedCornerWitness.design q)
        (rowOutcomes perturbedCornerWitness false q) π i ≤ perturbedThreshold q := by
      intro i
      exact row_below_threshold q false
        ⟨(π ⟨(perturbedCornerWitness.design q).m + i.val, by
          have h := (perturbedCornerWitness.design q).sample_le
          omega⟩).val, by
          exact (π ⟨(perturbedCornerWitness.design q).m + i.val, by
            have h := (perturbedCornerWitness.design q).sample_le
            omega⟩).isLt⟩
    unfold empiricalCDF
    have hconst : (fun i : Fin (perturbedCornerWitness.design q).k =>
        if observedControl (perturbedCornerWitness.design q)
          (rowOutcomes perturbedCornerWitness false q) π i ≤ perturbedThreshold q then
          (1 : ℝ) else 0) = fun _ => 1 := by
      funext i
      simp [hbelow i]
    rw [hconst]
    exact mean_const (by have h := (perturbedCornerWitness.design q).control_min; omega) 1
  · change empiricalCDF
      (observedTreatment (perturbedCornerWitness.design q)
        (rowOutcomes perturbedCornerWitness true q) π) (perturbedThreshold q) = 1
    have hbelow : ∀ i, observedTreatment (perturbedCornerWitness.design q)
        (rowOutcomes perturbedCornerWitness true q) π i ≤ perturbedThreshold q := by
      intro i
      exact row_below_threshold q true
        ⟨(π ⟨i.val, by
          have h := (perturbedCornerWitness.design q).sample_le
          omega⟩).val, by
          exact (π ⟨i.val, by
            have h := (perturbedCornerWitness.design q).sample_le
            omega⟩).isLt⟩
    unfold empiricalCDF
    have hconst : (fun i : Fin (perturbedCornerWitness.design q).m =>
        if observedTreatment (perturbedCornerWitness.design q)
          (rowOutcomes perturbedCornerWitness true q) π i ≤ perturbedThreshold q then
          (1 : ℝ) else 0) = fun _ => 1 := by
      funext i
      simp [hbelow i]
    rw [hconst]
    exact mean_const (by have h := (perturbedCornerWitness.design q).treatment_min; omega) 1

lemma law_cdf_bounds (t : Bool) (x : ℝ) :
    0 ≤ lawCDF cornerLaw t x ∧ lawCDF cornerLaw t x ≤ 1 := by
  rw [corner_law_facts.1 t x]
  unfold bernoulliHalfCDF
  by_cases hx : x < 0
  · simp [hx]
  · by_cases hx1 : x < 1 <;> norm_num [hx, hx1]

lemma cdf_distance_ge_at (t : Bool) (F : ℝ → ℝ) (x : ℝ)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ 1)
    (hFx : F x = 1) (hLx : lawCDF cornerLaw t x = 1 / 2) :
    (1 / 2 : ℝ) ≤ cdfDistance (lawCDF cornerLaw t) F := by
  have hbound (z : ℝ) : |lawCDF cornerLaw t z - F z| ≤ 1 := by
    have hL := law_cdf_bounds t z
    have hB := hF z
    rw [abs_le]
    constructor <;> linarith
  have hbdd : BddAbove (Set.range (fun z => |lawCDF cornerLaw t z - F z|)) :=
    ⟨1, by rintro y ⟨z, rfl⟩; exact hbound z⟩
  have hpoint : |lawCDF cornerLaw t x - F x| = (1 / 2 : ℝ) := by
    rw [hLx, hFx]
    norm_num
  unfold cdfDistance
  rw [← hpoint]
  exact le_csSup hbdd (Set.mem_range_self x)

lemma empirical_cdf_bounds_self {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ) (x : ℝ) :
    0 ≤ empiricalCDF y x ∧ empiricalCDF y x ≤ 1 :=
  AronowAudit.P022.empirical_cdf_bounds hN y x

lemma population_error_lower (q : ℕ) (t : Bool) :
    (1 / 2 : ℝ) ≤ cdfDistance (lawCDF cornerLaw t)
      (empiricalCDF (rowOutcomes perturbedCornerWitness t q)) := by
  apply cdf_distance_ge_at t _ (perturbedThreshold q)
  · intro x
    exact empirical_cdf_bounds_self
      (by have h := (perturbedCornerWitness.design q).population_min; omega) _ x
  · exact population_cdf_at_threshold q t
  · rw [corner_law_facts.1 t (perturbedThreshold q)]
    unfold bernoulliHalfCDF
    have hp := threshold_pos q
    have hu := threshold_lt_one q
    simp [not_lt.mpr hp.le, hu]

lemma sampled_cdf_bounds (q : ℕ) (t : Bool)
    (π : Assignment (perturbedCornerWitness.design q)) (x : ℝ) :
    0 ≤ sampledCDF perturbedCornerWitness t q π x ∧
      sampledCDF perturbedCornerWitness t q π x ≤ 1 := by
  cases t
  · change 0 ≤ empiricalCDF
      (observedControl (perturbedCornerWitness.design q)
        (rowOutcomes perturbedCornerWitness false q) π) x ∧ _ ≤ 1
    exact empirical_cdf_bounds_self
      (by have h := (perturbedCornerWitness.design q).control_min; omega) _ x
  · change 0 ≤ empiricalCDF
      (observedTreatment (perturbedCornerWitness.design q)
        (rowOutcomes perturbedCornerWitness true q) π) x ∧ _ ≤ 1
    exact empirical_cdf_bounds_self
      (by have h := (perturbedCornerWitness.design q).treatment_min; omega) _ x

lemma sampled_error_lower (q : ℕ) (t : Bool)
    (π : Assignment (perturbedCornerWitness.design q)) :
    (1 / 2 : ℝ) ≤ cdfDistance (lawCDF cornerLaw t)
      (sampledCDF perturbedCornerWitness t q π) := by
  apply cdf_distance_ge_at t _ (perturbedThreshold q)
  · exact sampled_cdf_bounds q t π
  · exact sampled_cdf_at_threshold q t π
  · rw [corner_law_facts.1 t (perturbedThreshold q)]
    unfold bernoulliHalfCDF
    have hp := threshold_pos q
    have hu := threshold_lt_one q
    simp [not_lt.mpr hp.le, hu]

end

end SAP.P022.WH.W1.P.T1_L4

open SAP.P022.WH.W1.P.T1_L4

theorem SAP.P022.WH.W1.T1_L4_proof : SAP.P022.WH.W1.T1_L4 := by
  change SAP.P022.PerturbedThresholdFacts
  intro q t
  refine ⟨threshold_pos q, threshold_lt_one q, population_cdf_at_threshold q t, ?_,
    population_error_lower q t, ?_⟩
  · rw [corner_law_facts.1 t (perturbedThreshold q)]
    unfold bernoulliHalfCDF
    have hp := threshold_pos q
    have hu := threshold_lt_one q
    simp [not_lt.mpr hp.le, hu]
  · intro π
    exact ⟨sampled_cdf_at_threshold q t π, sampled_error_lower q t π⟩
