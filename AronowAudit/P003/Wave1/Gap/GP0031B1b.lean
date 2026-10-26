import AronowAudit.P003.Wave1.Gap.GLP0031B2
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! P003-T18: the expected shuffle cost exceeds every linear-polylogarithmic bound.
Uses the proved finite expected-cost lower bound from GLP0031B2. -/

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

lemma GP0031B1b_balanced_runtime_family_arithmetic (r : ℕ) (hr : 4 ≤ r) :
    2^r = 4*(2^r/4) ∧ 2^r/2 = 2*(2^r/4) ∧
    2^r/4 = 2*((2^r/4)/2) ∧ 0 < 2^r/4 := by
  have he : r = 4+(r-4) := by omega
  have hn : 2^r = 16*2^(r-4) := by
    conv_lhs => rw [he,pow_add]
    norm_num
  have ht : 0 < 2^(r-4) := by positivity
  rw [hn]
  omega

lemma GP0031B1b_balanced_shuffle_not_linear_polylog_logTwo (r : ℕ) :
    logTwo ((2^r : ℕ) : ℝ) = (r : ℝ) := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  simp only [logTwo,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  field_simp [h2]

lemma GP0031B1b_balanced_shuffle_not_linear_polylog_recommendedK (r : ℕ) (hr : 6 ≤ r) :
    0 < recommendedK (1/8) (2^r) ∧
    32*Real.log (32*((2^r : ℕ) : ℝ)*logTwo ((2^r : ℕ) : ℝ)) ≤
      (recommendedK (1/8) (2^r) : ℝ) := by
  have hdef : recommendedK (1/8) (2^r) =
      ⌈32*Real.log (32*((2^r : ℕ) : ℝ)*logTwo ((2^r : ℕ) : ℝ))⌉₊ := by
    unfold recommendedK
    congr 1
    have harg : 4*((2^r : ℕ) : ℝ)*logTwo ((2^r : ℕ) : ℝ)/(1/8) =
        32*((2^r : ℕ) : ℝ)*logTwo ((2^r : ℕ) : ℝ) := by ring
    rw [harg]
    norm_num <;> ring
  have hn : (1 : ℝ) ≤ ((2^r : ℕ) : ℝ) := by
    have hnpos : 0 < (2 : ℕ)^r := by positivity
    exact_mod_cast (show 1 ≤ (2 : ℕ)^r by omega)
  have hrR : (6 : ℝ) ≤ r := by exact_mod_cast hr
  have harg : 1 < 32*((2^r : ℕ) : ℝ)*logTwo ((2^r : ℕ) : ℝ) := by
    rw [GP0031B1b_balanced_shuffle_not_linear_polylog_logTwo]
    nlinarith
  have hp : 0 < 32*Real.log (32*((2^r : ℕ) : ℝ)*logTwo ((2^r : ℕ) : ℝ)) :=
    mul_pos (by norm_num) (Real.log_pos harg)
  rw [hdef]
  exact ⟨by have := Nat.one_le_ceil_iff.mpr hp; omega,Nat.le_ceil _⟩

lemma GP0031B1b_balanced_shuffle_not_linear_polylog_quadratic (r K : ℕ) (hr : 6 ≤ r)
    (hK : 0 < K)
    (hcost : (((2^r/4+1 : ℕ) : ℝ)*K*((2^r-1 : ℕ) : ℝ))/2 ≤
      expectedUpperShuffleCost (1/2) (1/8) (2^r) K ⟨0,2^r/2,0,2^r/2⟩) :
    (((2^r : ℕ) : ℝ)^2)/16 ≤
      expectedUpperShuffleCost (1/2) (1/8) (2^r) K ⟨0,2^r/2,0,2^r/2⟩ := by
  obtain ⟨hn,hm,heven,hx⟩ := GP0031B1b_balanced_runtime_family_arithmetic r (by omega)
  have hn2 : 2 ≤ 2^r := by omega
  have hnR : (((2^r : ℕ) : ℝ)) = 4*((2^r/4 : ℕ) : ℝ) := by exact_mod_cast hn
  have hA : ((2^r : ℕ) : ℝ)/4 ≤ ((2^r/4+1 : ℕ) : ℝ) := by
    rw [Nat.cast_add,Nat.cast_one]
    linarith
  have hsub : ((2^r-1 : ℕ) : ℝ) = ((2^r : ℕ) : ℝ)-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hB : ((2^r : ℕ) : ℝ)/2 ≤ ((2^r-1 : ℕ) : ℝ) := by
    rw [hsub]
    have hnR2 : (2 : ℝ) ≤ ((2^r : ℕ) : ℝ) := by exact_mod_cast hn2
    linarith
  have hprod := mul_le_mul hA hB (by positivity) (by positivity)
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hprodK := mul_le_mul_of_nonneg_left hK1
    (show 0 ≤ ((2^r/4+1 : ℕ) : ℝ)*((2^r-1 : ℕ) : ℝ) by positivity)
  nlinarith

lemma GP0031B1b_balanced_shuffle_not_linear_polylog_log_littleO (c : ℝ) :
    (fun r : ℕ => Real.rpow (Real.log (((2^r : ℕ) : ℝ))) c)
      =o[Filter.atTop] (fun r : ℕ => ((2^r : ℕ) : ℝ)) := by
  have hn : Filter.Tendsto (fun r : ℕ => ((2^r : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  simpa only [Real.rpow_one, Function.comp_def, Real.rpow_eq_pow] using
    (isLittleO_log_rpow_rpow_atTop c (by norm_num : (0 : ℝ) < 1)).comp_tendsto hn

/-- An eventual quadratic lower bound excludes every linear-polylogarithmic bound. -/
lemma GP0031B1b_balanced_shuffle_not_linear_polylog_of_quadratic (F : ℕ → ℝ) (c : ℝ)
    (hlower : ∀ᶠ r : ℕ in Filter.atTop, (((2^r : ℕ) : ℝ)^2)/16 ≤ F r) :
    ¬ F =O[Filter.atTop] (fun r : ℕ =>
      ((2^r : ℕ) : ℝ)*Real.rpow (Real.log (((2^r : ℕ) : ℝ))) c) := by
  intro hO
  obtain ⟨C,hC,hbound⟩ := hO.exists_pos
  have hε : (0 : ℝ) < 1/(32*C) := by positivity
  have hsmall := (GP0031B1b_balanced_shuffle_not_linear_polylog_log_littleO c).bound hε
  have hfalse : ∀ᶠ r : ℕ in Filter.atTop, False := by
    filter_upwards [hlower,hbound.bound,hsmall] with r hr hbig hlog
    have hn : (0 : ℝ) < ((2^r : ℕ) : ℝ) := by positivity
    have hF : 0 ≤ F r := le_trans (by positivity) hr
    have hp : 0 ≤ Real.rpow (Real.log (((2^r : ℕ) : ℝ))) c := Real.rpow_nonneg
      (Real.log_natCast_nonneg _) _
    rw [Real.norm_eq_abs,abs_of_nonneg hF,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hn.le hp)] at hbig
    rw [Real.norm_eq_abs,abs_of_nonneg hp,Real.norm_eq_abs,abs_of_pos hn] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC.le hn.le)
    have hconst : C*((2^r : ℕ) : ℝ)*(1/(32*C)*((2^r : ℕ) : ℝ)) =
        (((2^r : ℕ) : ℝ)^2)/32 := by field_simp [hC.ne']
    rw [hconst] at hmul
    nlinarith [sq_pos_of_pos hn]
  obtain ⟨r,hr⟩ := hfalse.exists
  exact hr

theorem balanced_shuffle_not_linear_polylog_proof (c : ℝ) (hc : 0 ≤ c) :
    ¬ (fun r : ℕ =>
      let n : ℕ := 2^r
      expectedUpperShuffleCost (1/2) (1/8) n (recommendedK (1/8) n) ⟨0,n/2,0,n/2⟩)
      =O[Filter.atTop] (fun r : ℕ =>
        let n : ℕ := 2^r
        (n : ℝ)*Real.rpow (Real.log n) c) := by
  apply GP0031B1b_balanced_shuffle_not_linear_polylog_of_quadratic
  filter_upwards [Filter.eventually_ge_atTop 6] with r hr
  obtain ⟨hK,hKlog⟩ := GP0031B1b_balanced_shuffle_not_linear_polylog_recommendedK r hr
  apply GP0031B1b_balanced_shuffle_not_linear_polylog_quadratic r (recommendedK (1/8) (2^r)) hr hK
  exact (balanced_shuffle_lower_bounds_proof r (recommendedK (1/8) (2^r))
    (by omega) hK).2 hr hKlog

end AronowAudit.P003.Wave1

