import AronowAudit.P004.Wave1.NedHeadlineBlueprint
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic

namespace AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators

/-- Count dyadic annuli using their containing balls and sum the geometric bound. -/
theorem dy_proof : DY := by
  classical
  intro N D i Cb r e A c hCb hr he hA hspacing hc
  let T : Finset (Fin N) := Finset.univ.filter (fun j => 3 * r < D i j)
  let κ : Fin N → ℕ := fun j => ⌊Real.logb 2 (D i j / (3 * r))⌋₊
  let F : ℕ → Finset (Fin N) := fun k => T.filter (fun j => κ j = k)
  let q : ℝ := (2 : ℝ) ^ (2 - e)
  let H : ℝ := 37 * Cb * r^2 * A
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have h3r : 0 < 3 * r := by positivity
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg htwo (by linarith)
  have hH0 : 0 ≤ H := by dsimp only [H]; positivity

  -- The chosen half-open annuli satisfy 2^κ ≤ D/(3r) < 2^(κ+1).
  -- Assigning exact dyadic boundary points to the next annulus causes no loss.
  have hdyadic (j : Fin N) (hj : j ∈ T) :
      (2 : ℝ) ^ κ j ≤ D i j / (3 * r) ∧
        D i j / (3 * r) < (2 : ℝ) ^ (κ j + 1) := by
    have hjfar : 3 * r < D i j := (Finset.mem_filter.mp hj).2
    have hx1 : 1 < D i j / (3 * r) := by
      apply (lt_div_iff₀ h3r).2
      simpa only [one_mul] using hjfar
    have hx0 : 0 < D i j / (3 * r) := zero_lt_one.trans hx1
    have hlog0 : 0 ≤ Real.logb 2 (D i j / (3 * r)) :=
      Real.logb_nonneg htwo hx1.le
    constructor
    · have hfloor : (κ j : ℝ) ≤ Real.logb 2 (D i j / (3 * r)) :=
        Nat.floor_le hlog0
      have hh := (Real.le_logb_iff_rpow_le htwo hx0).mp hfloor
      simpa only [Real.rpow_natCast] using hh
    · have hfloor : Real.logb 2 (D i j / (3 * r)) < ((κ j + 1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (Nat.lt_floor_add_one (Real.logb 2 (D i j / (3 * r))))
      have hh := (Real.logb_lt_iff_lt_rpow htwo hx0).mp hfloor
      simpa only [Real.rpow_natCast] using hh

  -- Only the ball upper bound is used: no subtraction of two upper envelopes.
  have hFsub (k : ℕ) : F k ⊆ ball D i (6 * r * (2 : ℝ)^k) := by
    intro j hj
    obtain ⟨hjT, hjκ⟩ := Finset.mem_filter.mp hj
    have hu := (hdyadic j hjT).2
    rw [hjκ] at hu
    have hdist : D i j < (2 : ℝ)^(k + 1) * (3 * r) :=
      (div_lt_iff₀ h3r).mp hu
    have hdist' : D i j ≤ 6 * r * (2 : ℝ)^k := by
      calc
        D i j ≤ (2 : ℝ)^(k + 1) * (3 * r) := hdist.le
        _ = 6 * r * (2 : ℝ)^k := by rw [pow_succ]; ring
    simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and] using hdist'

  have hFcard (k : ℕ) : ((F k).card : ℝ) ≤
      37 * Cb * r^2 * ((2 : ℝ)^k)^2 := by
    have hp1 : 1 ≤ (2 : ℝ)^k := one_le_pow₀ (by norm_num)
    have hr2 : 1 ≤ r^2 := one_le_pow₀ hr
    have hp2 : 1 ≤ ((2 : ℝ)^k)^2 := one_le_pow₀ hp1
    have hscale : 1 ≤ r^2 * ((2 : ℝ)^k)^2 := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ r^2 * ((2 : ℝ)^k)^2 :=
          mul_le_mul hr2 hp2 (by norm_num) (sq_nonneg r)
    have hinner : 1 + (6 * r * (2 : ℝ)^k)^2 ≤
        37 * r^2 * ((2 : ℝ)^k)^2 := by nlinarith only [hscale]
    calc
      ((F k).card : ℝ) ≤ ((ball D i (6 * r * (2 : ℝ)^k)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card (hFsub k))
      _ ≤ Cb * (1 + (6 * r * (2 : ℝ)^k)^2) :=
        hspacing _ (by positivity)
      _ ≤ Cb * (37 * r^2 * ((2 : ℝ)^k)^2) :=
        mul_le_mul_of_nonneg_left hinner hCb.le
      _ = 37 * Cb * r^2 * ((2 : ℝ)^k)^2 := by ring

  have hFweight (k : ℕ) (j : Fin N) (hj : j ∈ F k) :
      c j ≤ A * ((2 : ℝ)^k) ^ (-e) := by
    obtain ⟨hjT, hjκ⟩ := Finset.mem_filter.mp hj
    have hjfar : 3 * r < D i j := (Finset.mem_filter.mp hjT).2
    have hlo := (hdyadic j hjT).1
    rw [hjκ] at hlo
    calc
      c j ≤ A * (D i j / (3 * r)) ^ (-e) := (hc j hjfar).2
      _ ≤ A * ((2 : ℝ)^k) ^ (-e) := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact Real.rpow_le_rpow_of_nonpos (pow_pos (by norm_num) k) hlo (by linarith)

  have hpowers (k : ℕ) :
      ((2 : ℝ)^k)^2 * ((2 : ℝ)^k) ^ (-e) = q^k := by
    calc
      ((2 : ℝ)^k)^2 * ((2 : ℝ)^k) ^ (-e) =
          ((2 : ℝ)^k) ^ (2 : ℝ) * ((2 : ℝ)^k) ^ (-e) := by
        rw [Real.rpow_two]
      _ = ((2 : ℝ)^k) ^ ((2 : ℝ) + (-e)) :=
        (Real.rpow_add (pow_pos (by norm_num) k) _ _).symm
      _ = (2 : ℝ) ^ ((k : ℝ) * (2 - e)) := by
        simpa only [sub_eq_add_neg] using
          (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) k (2 - e)).symm
      _ = ((2 : ℝ) ^ (2 - e)) ^ k := by
        rw [mul_comm (k : ℝ) (2 - e), Real.rpow_mul_natCast (by norm_num)]
      _ = q^k := rfl

  have hFsum (k : ℕ) : ∑ j ∈ F k, c j ≤ H * q^k := by
    have hw0 : 0 ≤ A * ((2 : ℝ)^k) ^ (-e) := by positivity
    calc
      ∑ j ∈ F k, c j ≤ ∑ _j ∈ F k, A * ((2 : ℝ)^k) ^ (-e) :=
        Finset.sum_le_sum (fun j hj => hFweight k j hj)
      _ = ((F k).card : ℝ) * (A * ((2 : ℝ)^k) ^ (-e)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (37 * Cb * r^2 * ((2 : ℝ)^k)^2) *
          (A * ((2 : ℝ)^k) ^ (-e)) :=
        mul_le_mul_of_nonneg_right (hFcard k) hw0
      _ = H * (((2 : ℝ)^k)^2 * ((2 : ℝ)^k) ^ (-e)) := by
        dsimp only [H]
        ring
      _ = H * q^k := by rw [hpowers]

  have hpartition : (∑ j ∈ T, c j) =
      ∑ k ∈ T.image κ, ∑ j ∈ F k, c j := by
    exact (Finset.sum_fiberwise_of_maps_to
      (s := T) (t := T.image κ) (g := κ)
      (fun j hj => Finset.mem_image_of_mem κ hj) c).symm
  have hgeom : ∑ k ∈ T.image κ, q^k ≤ (1 - q)⁻¹ := by
    calc
      ∑ k ∈ T.image κ, q^k ≤ ∑' k : ℕ, q^k :=
        (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum
          (T.image κ) (fun k _ => pow_nonneg hq0 k)
      _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1
  calc
    ∑ j ∈ Finset.univ.filter (fun j => 3 * r < D i j), c j =
        ∑ k ∈ T.image κ, ∑ j ∈ F k, c j := hpartition
    _ ≤ ∑ k ∈ T.image κ, H * q^k :=
      Finset.sum_le_sum (fun k _ => hFsum k)
    _ = H * ∑ k ∈ T.image κ, q^k := (Finset.mul_sum _ _ _).symm
    _ ≤ H * (1 - q)⁻¹ := mul_le_mul_of_nonneg_left hgeom hH0
    _ = 37 * Cb * r^2 * A / (1 - (2 : ℝ) ^ (2 - e)) := by
      simp only [H, q, div_eq_mul_inv]

end
end AronowAudit.P004.Wave1.NedHeadline
