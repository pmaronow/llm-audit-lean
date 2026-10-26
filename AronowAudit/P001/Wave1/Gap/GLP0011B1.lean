import AronowAudit.P001.P001_Foundations
import Mathlib.Analysis.SpecificLimits.Normed

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGLP0011B1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/- The geometric moment series are evaluated by Mathlib's polynomial-geometric
   series formula, with exponents zero, one and two. -/
lemma geometric_base_hasSums :
    HasSum geoMass 1 ∧ HasSum (fun k : ℕ => (k : ℝ) * geoMass k) 1 ∧
      HasSum (fun k : ℕ => (k : ℝ)^2 * geoMass k) 3 := by
  have hr : ‖(1/2 : ℝ)‖ < 1 := by norm_num
  constructor
  · convert (hasSum_pow_mul_geometric_of_norm_lt_one 0 hr).mul_right (1/2 : ℝ) using 1
    · ext k
      simp [geoMass, pow_succ]
    · norm_num [Finset.sum_range_succ, Nat.stirlingSecond]
  constructor
  · convert (hasSum_pow_mul_geometric_of_norm_lt_one 1 hr).mul_right (1/2 : ℝ) using 1
    · ext k
      simp [geoMass, pow_succ, mul_assoc]
    · norm_num [Finset.sum_range_succ, Nat.stirlingSecond]
  · convert (hasSum_pow_mul_geometric_of_norm_lt_one 2 hr).mul_right (1/2 : ℝ) using 1
    · ext k
      simp [geoMass, pow_succ, mul_assoc]
    · norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

lemma geometric_base_moments :
    FiniteMomentLaw geoMass ∧ massMean geoMass = 1 ∧ massSecond geoMass = 3 := by
  obtain ⟨h0, h1, h2⟩ := geometric_base_hasSums
  refine ⟨⟨?_, h0.summable, h0.tsum_eq, h1.summable, h2.summable⟩,
    h1.tsum_eq, h2.tsum_eq⟩
  intro k
  exact (pow_pos (by norm_num : (0 : ℝ) < 1/2) _).le

def geometric_shiftMass (n k : ℕ) : ℝ := if n ≤ k then geoMass (k-n) else 0

lemma geometric_zero_extend_hasSum (f : ℕ → ℝ) (s : ℝ) (hf : HasSum f s) (n : ℕ) :
    HasSum (fun k => if n ≤ k then f (k-n) else 0) s := by
  have ht : HasSum (fun k => if n ≤ k+n then f (k+n-n) else 0) s := by
    simpa using hf
  have hp : (∑ k ∈ Finset.range n, if n ≤ k then f (k-n) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [not_le.mpr (Finset.mem_range.mp hk)]
  simpa only [hp, zero_add] using
    (ht.sum_range_add (f := fun k => if n ≤ k then f (k-n) else 0) (k := n))

lemma geometric_shift_hasSums (n : ℕ) :
    HasSum (geometric_shiftMass n) 1 ∧
    HasSum (fun k : ℕ => (k : ℝ) * geometric_shiftMass n k) ((n : ℝ)+1) ∧
    HasSum (fun k : ℕ => (k : ℝ)^2 * geometric_shiftMass n k)
      ((n : ℝ)^2+2*(n : ℝ)+3) := by
  obtain ⟨h0, h1, h2⟩ := geometric_base_hasSums
  have hm : HasSum (fun k : ℕ => ((n : ℝ)+(k : ℝ))*geoMass k) ((n : ℝ)+1) := by
    convert (h0.mul_left (n : ℝ)).add h1 using 1
    · ext k
      ring
    · ring
  have hs : HasSum (fun k : ℕ => ((n : ℝ)+(k : ℝ))^2*geoMass k)
      ((n : ℝ)^2+2*(n : ℝ)+3) := by
    convert ((h0.mul_left ((n : ℝ)^2)).add (h1.mul_left (2*(n : ℝ)))).add h2 using 1
    · ext k
      ring
    · ring
  refine ⟨geometric_zero_extend_hasSum geoMass 1 h0 n, ?_, ?_⟩
  · convert geometric_zero_extend_hasSum _ _ hm n using 1
    ext k
    by_cases hk : n ≤ k
    · simp only [geometric_shiftMass, if_pos hk, Nat.cast_sub hk]
      ring
    · simp [geometric_shiftMass, hk]
  · convert geometric_zero_extend_hasSum _ _ hs n using 1
    ext k
    by_cases hk : n ≤ k
    · simp only [geometric_shiftMass, if_pos hk, Nat.cast_sub hk]
      ring
    · simp [geometric_shiftMass, hk]

lemma geometric_shift_law (n : ℕ) : FiniteMomentLaw (geometric_shiftMass n) := by
  obtain ⟨h0, h1, h2⟩ := geometric_shift_hasSums n
  refine ⟨?_, h0.summable, h0.tsum_eq, h1.summable, h2.summable⟩
  intro k
  unfold geometric_shiftMass
  split_ifs
  · exact geometric_base_moments.1.1 _
  · exact le_rfl

lemma geometric_mix_moments (n : ℕ) (hn : 2 ≤ n) :
    FiniteMomentLaw (mixMass n) ∧ (∀ k, 0 < mixMass n k) ∧
    massMean (mixMass n) = 1+(n : ℝ)⁻¹^2 ∧
    massSecond (mixMass n) = 3+(n : ℝ)⁻¹+2*(n : ℝ)⁻¹^2 ∧
    (massMean (mixMass n)-massMean geoMass)/((n : ℝ)⁻¹^2) = 1 := by
  obtain ⟨h0, h1, h2⟩ := geometric_base_hasSums
  obtain ⟨g0, g1, g2⟩ := geometric_shift_hasSums n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hi : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (by linarith)
  have hi1 : (n : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by linarith : (0 : ℝ) < n)).mpr hn1
  have ha : 0 < 1-(n : ℝ)⁻¹^3 :=
    sub_pos.mpr (pow_lt_one₀ hi.le hi1 (by decide : (3 : ℕ) ≠ 0))
  have hm0 : HasSum (mixMass n) 1 := by
    convert (h0.mul_left (1-(n : ℝ)⁻¹^3)).add (g0.mul_left ((n : ℝ)⁻¹^3)) using 1
    · rfl
    · ring
  have hm1 : HasSum (fun k : ℕ => (k : ℝ)*mixMass n k) (1+(n : ℝ)⁻¹^2) := by
    convert (h1.mul_left (1-(n : ℝ)⁻¹^3)).add (g1.mul_left ((n : ℝ)⁻¹^3)) using 1
    · ext k
      dsimp [mixMass, geometric_shiftMass]
      ring
    · field_simp [hn0]
      <;> ring
  have hm2 : HasSum (fun k : ℕ => (k : ℝ)^2*mixMass n k)
      (3+(n : ℝ)⁻¹+2*(n : ℝ)⁻¹^2) := by
    convert (h2.mul_left (1-(n : ℝ)⁻¹^3)).add (g2.mul_left ((n : ℝ)⁻¹^3)) using 1
    · ext k
      dsimp [mixMass, geometric_shiftMass]
      ring
    · field_simp [hn0]
      <;> ring
  have hpos (k : ℕ) : 0 < mixMass n k := by
    apply add_pos_of_pos_of_nonneg
      (mul_pos ha (pow_pos (by norm_num : (0 : ℝ) < 1/2) _))
    exact mul_nonneg (pow_nonneg hi.le _) ((geometric_shift_law n).1 k)
  refine ⟨⟨fun k => (hpos k).le, hm0.summable, hm0.tsum_eq,
    hm1.summable, hm2.summable⟩, hpos, hm1.tsum_eq, hm2.tsum_eq, ?_⟩
  change (massMean (mixMass n)-massMean geoMass)/((n : ℝ)⁻¹^2) = 1
  have hm : massMean (mixMass n) = 1+(n : ℝ)⁻¹^2 := hm1.tsum_eq
  rw [hm, geometric_base_moments.2.1]
  field_simp [hn0]
  <;> ring

lemma geometric_cdf_summable (q : ℕ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hs : Summable q) (x : ℝ) :
    Summable (fun k : ℕ => if (k : ℝ) ≤ x then q k else 0) := by
  apply Summable.of_nonneg_of_le _ _ hs
  · intro k
    split_ifs <;> simp_all
  · intro k
    split_ifs <;> simp_all

lemma geometric_cdf_bounds (q : ℕ → ℝ) (hq : FiniteMomentLaw q) (x : ℝ) :
    0 ≤ massCDF q x ∧ massCDF q x ≤ 1 := by
  have hs := geometric_cdf_summable q hq.1 hq.2.1 x
  constructor
  · apply tsum_nonneg
    intro k
    split_ifs <;> simp_all [hq.1]
  · calc
      massCDF q x ≤ ∑' k, q k := by
        apply Summable.tsum_le_tsum _ hs hq.2.1
        intro k
        split_ifs <;> simp_all [hq.1]
      _ = 1 := hq.2.2.1

lemma geometric_mix_cdf (n : ℕ) (x : ℝ) :
    massCDF (mixMass n) x =
      (1-(n : ℝ)⁻¹^3)*massCDF geoMass x +
        (n : ℝ)⁻¹^3*massCDF (geometric_shiftMass n) x := by
  have hf := geometric_cdf_summable geoMass geometric_base_moments.1.1
    geometric_base_moments.1.2.1 x
  have hg := geometric_cdf_summable (geometric_shiftMass n) (geometric_shift_law n).1
    (geometric_shift_law n).2.1 x
  have he := ((hf.hasSum.mul_left (1-(n : ℝ)⁻¹^3)).add
    (hg.hasSum.mul_left ((n : ℝ)⁻¹^3))).tsum_eq
  change (∑' k : ℕ, if (k : ℝ) ≤ x then mixMass n k else 0) = _
  convert he using 1
  · apply tsum_congr
    intro k
    split_ifs <;> simp [mixMass, geometric_shiftMass]
  all_goals rfl

lemma geometric_cdf_quotient_bound (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    |(massCDF (mixMass n) x-massCDF geoMass x)/((n : ℝ)⁻¹^2)| ≤ (n : ℝ)⁻¹ := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hf := geometric_cdf_bounds geoMass geometric_base_moments.1 x
  have hg := geometric_cdf_bounds (geometric_shiftMass n) (geometric_shift_law n) x
  have hd : |massCDF (geometric_shiftMass n) x-massCDF geoMass x| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have he : (massCDF (mixMass n) x-massCDF geoMass x)/((n : ℝ)⁻¹^2) =
      (n : ℝ)⁻¹*(massCDF (geometric_shiftMass n) x-massCDF geoMass x) := by
    rw [geometric_mix_cdf]
    field_simp [hn0]
    <;> ring
  rw [he, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd
    (inv_nonneg.mpr (Nat.cast_nonneg n))

theorem geometric_mean_perturbation_proof : FiniteMomentLaw geoMass ∧ massMean geoMass = 1 ∧ massSecond geoMass = 3 ∧
   (∀ n, 2  ≤  n → FiniteMomentLaw (mixMass n) ∧ (∀ k, 0  <  mixMass n k) ∧
     massMean (mixMass n) = 1 + (n : ℝ)⁻¹^2 ∧
     massSecond (mixMass n) = 3 + (n : ℝ)⁻¹ + 2*(n : ℝ)⁻¹^2 ∧
     (massMean (mixMass n) - massMean geoMass) / ((n : ℝ)⁻¹^2) = 1) ∧
   Tendsto (fun (n : ℕ) => massSecond (mixMass n) - (massMean (mixMass n))^2) atTop (nhds 2) ∧
   Tendsto (fun n : ℕ => (n : ℝ)⁻¹^2) atTop (nhds 0) ∧
   (∀ ε : ℝ, 0  <  ε → ∀ᶠ n in atTop, ∀ x : ℝ,
     |(massCDF (mixMass n) x - massCDF geoMass x) / ((n : ℝ)⁻¹^2)|  <  ε) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hi2 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹^2) atTop (nhds 0) := by
    simpa using hi.pow 2
  refine ⟨geometric_base_moments.1, geometric_base_moments.2.1,
    geometric_base_moments.2.2, geometric_mix_moments, ?_, hi2, ?_⟩
  · have hv : Tendsto (fun n : ℕ =>
        (3+(n : ℝ)⁻¹+2*(n : ℝ)⁻¹^2)-(1+(n : ℝ)⁻¹^2)^2) atTop (nhds 2) := by
      convert (((tendsto_const_nhds.add hi).add (hi2.const_mul 2)).sub
        ((tendsto_const_nhds.add hi2).pow 2)) using 1 <;> norm_num
    apply hv.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    obtain ⟨_, _, hm, hs, _⟩ := geometric_mix_moments n hn
    rw [hm, hs]
  · intro ε hε
    have he : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ < ε := hi.eventually (gt_mem_nhds hε)
    filter_upwards [eventually_ge_atTop (2 : ℕ), he] with n hn hεn
    intro x
    exact (geometric_cdf_quotient_bound n hn x).trans_lt hεn

end

end AronowAudit.P001.Wave1
