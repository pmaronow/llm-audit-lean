import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The two printed degree-rate conditions and the exact fourth-power subsequence. -/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n3_proof : N3 := by
  classical
  have hpower : Tendsto (fun n : ℕ => (n : ℝ) ^ (3 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
      tendsto_natCast_atTop_atTop
  have hJ : Tendsto sieveJ atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hb : ∀ᶠ n : ℕ in atTop, (b : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
      hpower.eventually (eventually_ge_atTop (b : ℝ))
    filter_upwards [hb] with n hn
    exact (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg n) _)).mpr hn
  have hsmall :
      Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop
  have hratio :
      Tendsto (fun n : ℕ => (sieveJ n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) ?_ hsmall
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hfloor : (sieveJ n : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    calc
      (sieveJ n : ℝ) / (n : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right hfloor hnpos.le
      _ = (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
        rw [← Real.rpow_sub_one (ne_of_gt hnpos)]
        norm_num
  have hsubseq (t : ℕ) : sieveJ (t ^ 4) = t ^ 3 := by
    have hpow : (((t : ℝ) ^ 4) ^ (3 / 4 : ℝ)) = (t : ℝ) ^ 3 := by
      calc
        (((t : ℝ) ^ 4) ^ (3 / 4 : ℝ)) =
            (((t : ℝ) ^ (4 : ℝ)) ^ (3 / 4 : ℝ)) := by
              rw [← Real.rpow_natCast]; norm_num
        _ = (t : ℝ) ^ ((4 : ℝ) * (3 / 4 : ℝ)) :=
          (Real.rpow_mul (Nat.cast_nonneg t) _ _).symm
        _ = (t : ℝ) ^ (3 : ℕ) := by norm_num [Real.rpow_natCast]
    unfold sieveJ
    rw [Nat.cast_pow, hpow, ← Nat.cast_pow, Nat.floor_natCast]
  exact ⟨hJ, hratio, hsubseq⟩

end

end AronowAudit.P001.Wave1.SieveRate
