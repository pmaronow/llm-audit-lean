import SAP.P005a.WH.W2.Leaves
import AronowAudit.P005.Wave1.InteractedExpansion.N8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2.P.T7_L2

open Finset Filter SAP.P005a.Bridge AronowAudit.P005
open scoped BigOperators Topology
noncomputable section

/-- The raw-coordinate slope estimate, by the covariance calculation for a
special-unit arm. -/
theorem raw_slope_bound {n : ℕ} (hn : 6 ≤ n) (A : Finset (Fin n))
    (hzero : ∃ i ∈ A, i.val = 0) (hcard : 2 ≤ A.card) :
    |scalarSlope A (spikeA n) (spikeV n)| ≤ 2 := by
  obtain ⟨z, hz, hzval⟩ := hzero
  let B := A.erase z
  let t : ℝ := A.card
  let k : ℝ := B.card
  let e : ℝ := 1 / (n : ℝ)^2
  let U : ℝ := ∑ i ∈ B, spikeV n i
  let V : ℝ := ∑ i ∈ B, spikeV n i ^ 2
  let W : ℝ := t * V - U^2
  let D : ℝ := k - 2 * e * U + e^2 * W
  let C : ℝ := e * W - U
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hA : A.Nonempty := ⟨z, hz⟩
  have ht : 0 < t := by dsimp [t]; exact_mod_cast (show 0 < A.card by omega)
  have ht0 : t ≠ 0 := ne_of_gt ht
  have htk : t = k + 1 := by
    have h := Finset.card_erase_add_one hz
    dsimp [t, k, B]
    exact_mod_cast h.symm
  have hk : 0 < k := by
    have hc : (2 : ℝ) ≤ t := by dsimp [t]; exact_mod_cast hcard
    linarith
  have htn : t ≤ (n : ℝ) := by
    have h : A.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ A)
    dsimp [t]
    exact_mod_cast h
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hev : e * (t + 4) ≤ 1 := by
    change 1 / (n : ℝ)^2 * (t + 4) ≤ 1
    rw [show 1 / (n : ℝ)^2 * (t + 4) = (t + 4) / (n : ℝ)^2 by ring]
    apply (div_le_iff₀ (sq_pos_of_ne_zero hn0)).2
    nlinarith
  have hv0 : spikeV n z = 0 := by simp [spikeV, hzval]
  have ha0 : spikeA n z = 1 := by simp [spikeA, hzval]
  have hai (i : Fin n) (hi : i ∈ B) : spikeA n i = e * spikeV n i := by
    have hne : i.val ≠ 0 := by
      intro hi0
      have hiz : i = z := Fin.ext (hi0.trans hzval.symm)
      exact (Finset.mem_erase.mp hi).1 hiz
    simp [spikeA, hne, e, div_eq_mul_inv, mul_comm]
  have hsplit (f : Fin n → ℝ) : (∑ i ∈ A, f i) = f z + ∑ i ∈ B, f i :=
    (Finset.add_sum_erase A f hz).symm
  have hU : |U| ≤ k := by
    calc
      |U| ≤ ∑ i ∈ B, |spikeV n i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ B, (1 : ℝ) :=
        Finset.sum_le_sum (fun i hi =>
          AronowAudit.P005.Wave1.InteractedExpansion.spikeV_abs n (by omega) i)
      _ = k := by simp [k]
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hV : V ≤ k := by
    calc
      V ≤ ∑ _i ∈ B, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hv : |spikeV n i| ≤ 1 := by
          simpa [spikeV, AronowAudit.P005.spikeV] using
            AronowAudit.P005.Wave1.InteractedExpansion.spikeV_abs n (by omega) i
        have hv' := abs_le.mp hv
        have hp1 : 0 ≤ 1 - spikeV n i := by linarith
        have hp2 : 0 ≤ 1 + spikeV n i := by linarith
        have hp := mul_nonneg hp1 hp2
        nlinarith
      _ = k := by simp [k]
  have hCS : U^2 ≤ k * V := by
    simpa [U, V, k] using
      Finset.sum_mul_sq_le_sq_mul_sq B (fun _ => (1 : ℝ)) (spikeV n)
  have hW0 : 0 ≤ W := by dsimp [W]; nlinarith
  have hW : W ≤ t * k := by
    have h := mul_le_mul_of_nonneg_left hV ht.le
    dsimp [W]
    nlinarith [sq_nonneg U]
  have hsV : (∑ i ∈ A, spikeV n i) = U := by rw [hsplit, hv0]; simp [U]
  have hsA : (∑ i ∈ A, spikeA n i) = 1 + e * U := by
    rw [hsplit, ha0]
    congr 1
    calc
      (∑ i ∈ B, spikeA n i) = ∑ i ∈ B, e * spikeV n i :=
        Finset.sum_congr rfl hai
      _ = e * U := by rw [← Finset.mul_sum]
  have hsAA : (∑ i ∈ A, spikeA n i * spikeA n i) = 1 + e^2 * V := by
    rw [hsplit, ha0, one_mul]
    congr 1
    calc
      (∑ i ∈ B, spikeA n i * spikeA n i) = ∑ i ∈ B, e^2 * spikeV n i^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hai i hi]
        ring
      _ = e^2 * V := by rw [← Finset.mul_sum]
  have hsAV : (∑ i ∈ A, spikeA n i * spikeV n i) = e * V := by
    rw [hsplit, hv0, mul_zero, zero_add]
    calc
      (∑ i ∈ B, spikeA n i * spikeV n i) = ∑ i ∈ B, e * spikeV n i^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hai i hi]
        ring
      _ = e * V := by rw [← Finset.mul_sum]
  have hvar : sampleCov A (spikeA n) (spikeA n) = D / t^2 := by
    unfold sampleCov mean
    rw [hsAA, hsA]
    change (1 + e^2 * V) / t - ((1 + e * U) / t) * ((1 + e * U) / t) = D / t^2
    dsimp [D, W]
    rw [htk]
    field_simp [show k + 1 ≠ 0 by linarith]
    <;> ring
  have hcov : sampleCov A (spikeA n) (spikeV n) = C / t^2 := by
    unfold sampleCov mean
    rw [hsAV, hsA, hsV]
    change e * V / t - (1 + e * U) / t * (U / t) = C / t^2
    dsimp [C, W]
    field_simp [ht0]
    <;> ring
  have hD : 0 < D := by
    have h0 := AronowAudit.P005.Wave1.InteractedExpansion.n5_proof n hn A hcard
    have haeq : AronowAudit.P005.spikeA n = spikeA n := by funext i; rfl
    have h1 : 0 < AronowAudit.P005.sampleCov A (spikeA n) (spikeA n) := by
      simpa only [haeq] using h0
    have h : 0 < sampleCov A (spikeA n) (spikeA n) := by
      simpa only [SAP.P005a.Bridge.sampleCov_eq] using h1
    rw [hvar] at h
    exact (div_pos_iff_of_pos_right (sq_pos_of_ne_zero ht0)).mp h
  have hDlow : k - 2 * e * k ≤ D := by
    have hu := (abs_le.mp hU).2
    have hmul := mul_le_mul_of_nonneg_left hu (show 0 ≤ 2 * e by positivity)
    dsimp [D]
    nlinarith [mul_nonneg (sq_nonneg e) hW0]
  have hC : |C| ≤ e * t * k + k := by
    calc
      |C| = |e * W - U| := rfl
      _ ≤ |e * W| + |U| := abs_sub _ _
      _ ≤ e * (t * k) + k := by
        rw [abs_of_nonneg (mul_nonneg he hW0)]
        exact add_le_add (mul_le_mul_of_nonneg_left hW he) hU
      _ = _ := by ring
  have hslack : e * t * k + k ≤ 2 * (k - 2 * e * k) := by
    have h := mul_nonneg (sub_nonneg.mpr hev) hk.le
    nlinarith
  have hratio : |sampleCov A (spikeA n) (spikeV n) /
      sampleCov A (spikeA n) (spikeA n)| ≤ 2 := by
    have hcancel : (C / t^2) / (D / t^2) = C / D := by
      field_simp [ht0, ne_of_gt hD]
      <;> ring
    rw [hcov, hvar, hcancel, abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).2
    linarith
  simpa [scalarSlope] using hratio

/-- With half the population in an arm containing unit zero, its raw a-mean
is within n⁻² of 2/n. -/
theorem high_mean_deviation {n : ℕ} (hn : 6 ≤ n) (A : Finset (Fin n))
    (hzero : ∃ i ∈ A, i.val = 0) (hcard : A.card = n / 2) (hev : Even n) :
    |mean A (spikeA n) - 2 / (n : ℝ)| ≤ 1 / (n : ℝ)^2 := by
  obtain ⟨z, hz, hzval⟩ := hzero
  let B := A.erase z
  let t : ℝ := A.card
  let k : ℝ := B.card
  let e : ℝ := 1 / (n : ℝ)^2
  let U : ℝ := ∑ i ∈ B, spikeV n i
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hA : A.Nonempty := ⟨z, hz⟩
  have ht : 0 < t := by dsimp [t]; exact_mod_cast (show 0 < A.card by omega)
  have ht0 : t ≠ 0 := ne_of_gt ht
  have htk : t = k + 1 := by
    have h := Finset.card_erase_add_one hz
    dsimp [t, k, B]
    exact_mod_cast h.symm
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hk_le : k ≤ t := by rw [htk]; linarith
  have hte : t = (n : ℝ) / 2 := by
    dsimp [t]
    rw [hcard]
    rcases hev with ⟨m, hm⟩
    have hn_even : n = 2 * (n / 2) := by omega
    have hncast : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hn_even
    rw [hncast]
    ring
  have hv0 : spikeV n z = 0 := by simp [spikeV, hzval]
  have ha0 : spikeA n z = 1 := by simp [spikeA, hzval]
  have hai (i : Fin n) (hi : i ∈ B) : spikeA n i = e * spikeV n i := by
    have hne : i.val ≠ 0 := by
      intro hi0
      have hiz : i = z := Fin.ext (hi0.trans hzval.symm)
      exact (Finset.mem_erase.mp hi).1 hiz
    simp [spikeA, hne, e, div_eq_mul_inv, mul_comm]
  have hsplit (f : Fin n → ℝ) : (∑ i ∈ A, f i) = f z + ∑ i ∈ B, f i :=
    (Finset.add_sum_erase A f hz).symm
  have hU : |U| ≤ k := by
    calc
      |U| ≤ ∑ i ∈ B, |spikeV n i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ B, (1 : ℝ) :=
        Finset.sum_le_sum (fun i hi => by
          have hv : |spikeV n i| ≤ 1 := by
            simpa [spikeV, AronowAudit.P005.spikeV] using
              AronowAudit.P005.Wave1.InteractedExpansion.spikeV_abs n (by omega) i
          exact hv)
      _ = k := by simp [k]
  have hsA : (∑ i ∈ A, spikeA n i) = 1 + e * U := by
    rw [hsplit, ha0]
    congr 1
    calc
      (∑ i ∈ B, spikeA n i) = ∑ i ∈ B, e * spikeV n i :=
        Finset.sum_congr rfl hai
      _ = e * U := by rw [← Finset.mul_sum]
  have hmean : mean A (spikeA n) = (1 + e * U) / t := by
    unfold mean
    rw [hsA]
  have hdev_eq : mean A (spikeA n) - 2 / (n : ℝ) = e * U / t := by
    rw [hmean, hte]
    dsimp [e]
    field_simp [hn0]
    <;> ring
  have hdev : |e * U / t| ≤ e := by
    rw [abs_div, abs_mul, abs_of_nonneg (by dsimp [e]; positivity), abs_of_pos ht]
    apply (div_le_iff₀ ht).2
    have hmul := mul_le_mul_of_nonneg_left hU (show 0 ≤ e by dsimp [e]; positivity)
    dsimp [e] at *
    nlinarith [mul_nonneg (show 0 ≤ e by positivity) (sub_nonneg.mpr hk_le)]
  rw [hdev_eq]
  simpa [e] using hdev

end
end SAP.P005a.WH.W2.P.T7_L2

theorem SAP.P005a.WH.W2.T7_L2_proof : SAP.P005a.WH.W2.T7_L2 := by
  intro n hn A hzero hcard
  have hslope := SAP.P005a.WH.W2.P.T7_L2.raw_slope_bound hn A hzero hcard
  refine ⟨hslope, ?_⟩
  intro heven hbalanced
  have hmean_dev := SAP.P005a.WH.W2.P.T7_L2.high_mean_deviation
    hn A hzero hbalanced heven
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hn2pos : (0 : ℝ) < (n : ℝ)^2 := sq_pos_of_ne_zero (ne_of_gt hnpos)
  have hinv : 1 / (n : ℝ) ≤ 1 / 6 := by
    apply (div_le_iff₀ hnpos).2
    norm_num
    nlinarith
  have hinv2 : 1 / (n : ℝ)^2 ≤ 1 / 36 := by
    apply (div_le_iff₀ hn2pos).2
    norm_num
    nlinarith
  have hdelta : |1 / (n : ℝ) - mean A (spikeA n)| ≤ 7 / 36 := by
    calc
      |1 / (n : ℝ) - mean A (spikeA n)| =
          |-(1 / (n : ℝ)) - (mean A (spikeA n) - 2 / (n : ℝ))| := by congr 1 <;> ring
      _ ≤ |-(1 / (n : ℝ))| + |mean A (spikeA n) - 2 / (n : ℝ)| := abs_sub _ _
      _ ≤ 1 / 6 + 1 / 36 := by
        rw [abs_neg, abs_of_nonneg (by positivity)]
        exact add_le_add hinv (hmean_dev.trans hinv2)
      _ = 7 / 36 := by norm_num
  have hmeanV : |mean A (spikeV n)| ≤ 1 :=
    AronowAudit.P005.Wave1.InteractedExpansion.mean_abs_le_bound A
      (Finset.card_pos.mp (by omega)) _ 1
      (fun i hi => AronowAudit.P005.Wave1.InteractedExpansion.spikeV_abs n (by omega) i)
  unfold spikeFit
  calc
    _ ≤ |mean A (spikeV n)| + |(1 / (n : ℝ) - mean A (spikeA n)) *
      scalarSlope A (spikeA n) (spikeV n)| := abs_add_le _ _
    _ ≤ 1 + (7 / 36) * 2 := by
      rw [abs_mul]
      exact add_le_add hmeanV
        (mul_le_mul hdelta hslope (abs_nonneg _) (by norm_num))
    _ = 25 / 18 := by norm_num

