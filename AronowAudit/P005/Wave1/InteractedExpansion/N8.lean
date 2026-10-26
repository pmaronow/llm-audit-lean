import AronowAudit.P005.Wave1.InteractedExpansion.N5

set_option autoImplicit false
namespace AronowAudit.P005.Wave1.InteractedExpansion
open AronowAudit.P005 Finset Filter
open scoped BigOperators Topology
noncomputable section

/-- Entrywise absolute bounds pass to any nonempty arm. -/
theorem mean_abs_le_bound {n : ℕ} (A : Finset (Fin n)) (hA : A.Nonempty)
    (f : Fin n → ℝ) (c : ℝ) (hf : ∀ i ∈ A, |f i| ≤ c) : |mean A f| ≤ c := by
  apply abs_le.mpr
  constructor
  · calc
      -c = mean A (fun _ => -c) := (mean_const A hA _).symm
      _ ≤ mean A f := mean_mono A _ _ (fun i hi => (abs_le.mp (hf i hi)).1)
  · calc
      mean A f ≤ mean A (fun _ => c) :=
        mean_mono A _ _ (fun i hi => (abs_le.mp (hf i hi)).2)
      _ = c := mean_const A hA _

/-- A raw-sum proof using Cauchy--Schwarz.
Set B=A\{z}, k=|B|, t=k+1, U=sum_B v, V=sum_B v², e=n⁻².
Then t² Cov(a,v)=e(tV-U²)-U and t² Var(a)=k-2eU+e²(tV-U²). -/
theorem n8_proof : N8 := by
  intro h1 h5 n hn A hzero hcard
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
    dsimp [t]; exact_mod_cast h
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
        Finset.sum_le_sum (fun i hi => (h1 n (by omega)).2.2.1 i)
      _ = k := by simp [k]
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hV : V ≤ k := by
    calc
      V ≤ ∑ _i ∈ B, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have h := abs_le.mp ((h1 n (by omega)).2.2.1 i)
        nlinarith [h.1, h.2]
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
    have h := h5 n hn A hcard
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
  have hmeanV : |mean A (spikeV n)| ≤ 1 :=
    mean_abs_le_bound A hA _ 1 (fun i hi => (h1 n (by omega)).2.2.1 i)
  have hmeanAlo : -e ≤ mean A (spikeA n) := by
    calc
      -e = mean A (fun _ => -e) := (mean_const A hA _).symm
      _ ≤ mean A (spikeA n) := mean_mono A _ _
        (fun i hi => (spikeA_bounds n (by omega) i).1)
  have hmeanAhi : mean A (spikeA n) ≤ 1 := by
    calc
      _ ≤ mean A (fun _ => (1 : ℝ)) := mean_mono A _ _
        (fun i hi => (spikeA_bounds n (by omega) i).2)
      _ = 1 := mean_const A hA _
  have hsmall : 1 / (n : ℝ) + e ≤ 1 := by
    dsimp [e]
    have heq : 1 / (n : ℝ) + 1 / (n : ℝ)^2 = ((n : ℝ) + 1) / (n : ℝ)^2 := by
      field_simp [hn0]
      <;> ring
    rw [heq]
    exact (div_le_iff₀ (sq_pos_of_ne_zero hn0)).2 (by nlinarith)
  have hdif : |1 / (n : ℝ) - mean A (spikeA n)| ≤ 1 := by
    apply abs_le.mpr
    have hpos : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    constructor <;> linarith
  unfold armFit
  calc
    _ ≤ |mean A (spikeV n)| + |(1 / (n : ℝ) - mean A (spikeA n)) *
      (sampleCov A (spikeA n) (spikeV n) / sampleCov A (spikeA n) (spikeA n))| :=
      abs_add_le _ _
    _ ≤ 1 + 1 * 2 := by
      rw [abs_mul]
      exact add_le_add hmeanV (mul_le_mul hdif hratio (abs_nonneg _) (by norm_num))
    _ = 3 := by norm_num

end
end AronowAudit.P005.Wave1.InteractedExpansion
