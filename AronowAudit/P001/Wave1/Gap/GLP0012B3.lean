import AronowAudit.P001.Wave1.MarSelection.N1
import AronowAudit.P001.Wave1.MarSelection.N2
import AronowAudit.P001.Wave1.MarSelection.N3
import AronowAudit.P001.Wave1.MarSelection.N4
import AronowAudit.P001.Wave1.MarSelection.N5
import AronowAudit.P001.Wave1.MarDiscrete.N1
import Mathlib.Analysis.Normed.Group.Tannery

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

local instance instDecidableGLP0012B3 (p : Prop) : Decidable p := Classical.propDecidable p


/-- Every atom in the specified dyadic series has strictly positive mass. -/
lemma T27_mass_pos (i : Σ m : ℕ, Fin (2 ^ m)) : 0 < dyadicMass i := by
  unfold dyadicMass
  positivity

/-- The total mass at level `m` is the next geometric term. -/
lemma T27_level_mass (m : ℕ) :
    (∑' k : Fin (2 ^ m), dyadicMass ⟨m, k⟩) = (1 / 2 : ℝ) ^ (m + 1) := by
  simp only [dyadicMass, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hc : (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  rw [show 2 * m + 1 = m + (m + 1) by omega, pow_add, ← mul_assoc, hc, one_mul]

lemma T27_geometric : HasSum (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1)) 1 := by
  convert (hasSum_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left
    (1 / 2 : ℝ) using 1
  · ext m
    rw [pow_succ]
    ring
  · norm_num

lemma T27_mass_summable : Summable dyadicMass := by
  apply (summable_sigma_of_nonneg (fun i => (T27_mass_pos i).le)).2
  refine ⟨fun m => (hasSum_fintype (fun k : Fin (2 ^ m) => dyadicMass ⟨m, k⟩)).summable, ?_⟩
  simpa only [T27_level_mass] using T27_geometric.summable

lemma T27_total_mass : (∑' i, dyadicMass i) = 1 := by
  rw [T27_mass_summable.tsum_sigma]
  simpa only [T27_level_mass] using T27_geometric.tsum_eq

lemma T27_cdf_summable (x : ℝ) :
    Summable (fun i => if dyadicValue i ≤ x then dyadicMass i else 0) := by
  apply Summable.of_nonneg_of_le _ _ T27_mass_summable
  · intro i
    split_ifs
    · exact (T27_mass_pos i).le
    · exact le_refl _
  · intro i
    split_ifs <;> linarith [T27_mass_pos i]

/-- An explicit floor construction supplies a midpoint in each interior interval. -/
lemma T27_midpoints_dense (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ i : Σ m : ℕ, Fin (2 ^ m), a < dyadicValue i ∧ dyadicValue i < b := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hab)
    (by norm_num : (1 / 2 : ℝ) < 1)
  rw [div_pow, one_pow] at hm
  have hpow : 0 < (2 : ℝ) ^ m := by positivity
  have hwidth : 1 < (b - a) * (2 : ℝ) ^ m := (div_lt_iff₀ hpow).1 hm
  let k : ℕ := ⌊(2 : ℝ) ^ m * a + 1 / 2⌋₊
  have hklo : (2 : ℝ) ^ m * a + 1 / 2 < (k : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hkhi : (k : ℝ) ≤ (2 : ℝ) ^ m * a + 1 / 2 :=
    Nat.floor_le (by positivity)
  have hden : 0 < 2 * (2 : ℝ) ^ m := by positivity
  have hva : a < (2 * (k : ℝ) + 1) / (2 * (2 : ℝ) ^ m) := by
    apply (lt_div_iff₀ hden).2
    nlinarith
  have hvb : (2 * (k : ℝ) + 1) / (2 * (2 : ℝ) ^ m) < b := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hk : k < 2 ^ m := by
    have hh := (div_lt_iff₀ hden).1 (hvb.trans hb)
    exact_mod_cast (show (k : ℝ) < (2 : ℝ) ^ m by nlinarith)
  refine ⟨⟨m, ⟨k, hk⟩⟩, ?_, ?_⟩
  · simpa only [dyadicValue, pow_succ, mul_comm] using hva
  · simpa only [dyadicValue, pow_succ, mul_comm] using hvb

lemma T27_strict_increase (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    dyadicCDF a < dyadicCDF b := by
  obtain ⟨i, hai, hib⟩ := T27_midpoints_dense a b ha hab hb
  apply Summable.tsum_lt_tsum (i := i) _ _ (T27_cdf_summable a) (T27_cdf_summable b)
  · intro j
    by_cases hj : dyadicValue j ≤ a
    · simp only [if_pos hj, if_pos (hj.trans hab.le), le_refl]
    · simp only [if_neg hj]
      split_ifs <;> linarith [T27_mass_pos j]
  · simpa only [if_neg (not_le.mpr hai), if_pos hib.le] using T27_mass_pos i

/-- The point one third is not among these dyadic atoms. -/
lemma T27_third_not_atom (i : Σ m : ℕ, Fin (2 ^ m)) : dyadicValue i ≠ (1 / 3 : ℝ) := by
  intro h
  unfold dyadicValue at h
  have hh := (div_eq_iff (by positivity : (2 : ℝ) ^ (i.1 + 1) ≠ 0)).1 h
  have hreal : (3 : ℝ) * (2 * (i.2 : ℝ) + 1) = (2 : ℝ) ^ (i.1 + 1) := by
    linarith
  have hnat : 3 * (2 * (i.2 : ℕ) + 1) = 2 ^ (i.1 + 1) := by
    exact_mod_cast hreal
  have hdvd : 3 ∣ 2 ^ (i.1 + 1) := by
    rw [← hnat]
    exact dvd_mul_right _ _
  have hbad := Nat.prime_three.dvd_of_dvd_pow hdvd
  norm_num at hbad

/-- Summable domination justifies passage to the limit at every non-atom. -/
lemma T27_continuous_off_atoms (c : ℝ)
    (hc : ∀ i : Σ m : ℕ, Fin (2 ^ m), dyadicValue i ≠ c) : ContinuousAt dyadicCDF c := by
  apply tendsto_tsum_of_dominated_convergence T27_mass_summable
  · intro i
    rcases lt_or_gt_of_ne (hc i) with hi | hi
    · have heq : (fun _ : ℝ => dyadicMass i) =ᶠ[𝓝 c]
          (fun x => if dyadicValue i ≤ x then dyadicMass i else 0) := by
        filter_upwards [eventually_gt_nhds hi] with x hx
        simp only [if_pos hx.le]
      simpa only [if_pos hi.le] using tendsto_const_nhds.congr' heq
    · have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 c]
          (fun x => if dyadicValue i ≤ x then dyadicMass i else 0) := by
        filter_upwards [eventually_lt_nhds hi] with x hx
        simp only [if_neg (not_le.mpr hx)]
      simpa only [if_neg (not_le.mpr hi)] using tendsto_const_nhds.congr' heq
  · exact Eventually.of_forall (fun x i => by
      split_ifs <;> simp only [Real.norm_eq_abs, abs_of_pos (T27_mass_pos i), norm_zero]
      · exact le_refl _
      · exact (T27_mass_pos i).le)

theorem dense_discrete_cdf_counterexample_proof : Summable dyadicMass ∧ (∑' i,dyadicMass i)=1 ∧
   (∀ a b : ℝ, 0 < a → a < b → b < 1 → dyadicCDF a < dyadicCDF b) ∧
   ContinuousAt dyadicCDF (1/3) ∧
   ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x-1/3| < ε → dyadicCDF x=dyadicCDF (1/3) := by
  refine ⟨T27_mass_summable, T27_total_mass, T27_strict_increase,
    T27_continuous_off_atoms (1 / 3) T27_third_not_atom, ?_⟩
  rintro ⟨ε, hε, hflat⟩
  let t : ℝ := min (ε / 2) (1 / 6)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have hte : t < ε := (min_le_left _ _).trans_lt (by linarith)
  have ht6 : t ≤ 1 / 6 := min_le_right _ _
  have heq := hflat (1 / 3 + t) (by
    simpa only [add_sub_cancel_left, abs_of_pos ht] using hte)
  have hlt := T27_strict_increase (1 / 3) (1 / 3 + t) (by norm_num)
    (by linarith) (by linarith)
  exact hlt.ne heq.symm

end

end AronowAudit.P001.Wave1
