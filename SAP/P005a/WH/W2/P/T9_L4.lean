import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Topology Matrix.Norms.Operator

namespace SAP.P005a.WH.W2.P.T9_L4

noncomputable section

private def expCoeff {k : ℕ} (X : Matrix (Fin k) (Fin k) ℝ) (n : ℕ) :
    Matrix (Fin k) (Fin k) ℝ := ((Nat.factorial n : ℝ)⁻¹) • X ^ n

private def expTailBound {k : ℕ} (X : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  ∑' n : ℕ, ‖expCoeff X (n + 2)‖

private lemma expTailBound_nonneg {k : ℕ} (X : Matrix (Fin k) (Fin k) ℝ) :
    0 ≤ expTailBound X := by
  apply tsum_nonneg
  intro n
  exact norm_nonneg _

private lemma expCoeff_summable {k : ℕ} (X : Matrix (Fin k) (Fin k) ℝ) :
    Summable fun n => ‖expCoeff X n‖ := by
  simpa [expCoeff] using (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) X)

private lemma exp_remainder_bound {k : ℕ} (X : Matrix (Fin k) (Fin k) ℝ)
    (t : ℝ) (ht : |t| ≤ 1) :
    ‖NormedSpace.exp (t • X) - 1 - t • X‖ ≤ t ^ 2 * expTailBound X := by
  let f : ℕ → Matrix (Fin k) (Fin k) ℝ := fun n => expCoeff (t • X) n
  have hs := (NormedSpace.expSeries_summable' (𝕂 := ℝ) (t • X)).sum_add_tsum_nat_add 2
  have hexp : NormedSpace.exp (t • X) =
      (∑ n ∈ Finset.range 2, f n) + ∑' n : ℕ, f (n + 2) := by
    calc
      NormedSpace.exp (t • X) = ∑' n : ℕ, f n := by
        rw [NormedSpace.exp_eq_tsum ℝ]
        rfl
      _ = (∑ n ∈ Finset.range 2, f n) + ∑' n : ℕ, f (n + 2) := hs.symm
  have hprefix : (∑ n ∈ Finset.range 2, f n) = 1 + t • X := by
    simp [f, expCoeff, Finset.sum_range_succ]
  have hrem : NormedSpace.exp (t • X) - 1 - t • X = ∑' n : ℕ, f (n + 2) := by
    rw [hexp, hprefix]
    abel
  have htailSummable : Summable fun n => ‖f (n + 2)‖ := by
    exact (summable_nat_add_iff 2).2 (expCoeff_summable (t • X))
  have hnorm : ‖∑' n : ℕ, f (n + 2)‖ ≤ ∑' n : ℕ, ‖f (n + 2)‖ :=
    norm_tsum_le_tsum_norm htailSummable
  have hcoeff : ∀ n : ℕ,
      ‖f (n + 2)‖ ≤ t ^ 2 * ‖expCoeff X (n + 2)‖ := by
    intro n
    change ‖expCoeff (t • X) (n + 2)‖ ≤ t ^ 2 * ‖expCoeff X (n + 2)‖
    have hrewrite : expCoeff (t • X) (n + 2) = t ^ (n + 2) • expCoeff X (n + 2) := by
      simp [expCoeff, smul_pow, smul_smul, mul_comm]
    rw [hrewrite, norm_smul, Real.norm_eq_abs, abs_pow]
    have habs : |t| ^ (n + 2) ≤ t ^ 2 := by
      rw [pow_add]
      have hsmall : |t| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
      have heq : |t| ^ 2 = t ^ 2 := by nlinarith [sq_abs t]
      nlinarith
    exact mul_le_mul_of_nonneg_right habs (norm_nonneg _)
  have hcompare : (∑' n : ℕ, ‖f (n + 2)‖) ≤
      ∑' n : ℕ, t ^ 2 * ‖expCoeff X (n + 2)‖ :=
    htailSummable.tsum_le_tsum hcoeff (by
      exact ((summable_nat_add_iff 2).2 (expCoeff_summable X)).mul_left (t ^ 2))
  have hmul : (∑' n : ℕ, t ^ 2 * ‖expCoeff X (n + 2)‖) =
      t ^ 2 * expTailBound X := by
    rw [((summable_nat_add_iff 2).2 (expCoeff_summable X)).tsum_mul_left]
    rfl
  rw [hrem]
  exact hnorm.trans (hcompare.trans_eq hmul)

end

end SAP.P005a.WH.W2.P.T9_L4

theorem SAP.P005a.WH.W2.T9_L4_proof : SAP.P005a.WH.W2.T9_L4 := by
  intro k A B
  let K := fun X : Matrix (Fin k) (Fin k) ℝ => SAP.P005a.WH.W2.P.T9_L4.expTailBound X
  let C := K (A + B) + (‖A‖ * ‖B‖ + K A + K B + ‖A‖ * K B + K A * ‖B‖ + K A * K B)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C, K]
    have h1 := SAP.P005a.WH.W2.P.T9_L4.expTailBound_nonneg (A + B)
    have h2 := SAP.P005a.WH.W2.P.T9_L4.expTailBound_nonneg A
    have h3 := SAP.P005a.WH.W2.P.T9_L4.expTailBound_nonneg B
    positivity
  · intro t ht
    let a : Matrix (Fin k) (Fin k) ℝ := t • A
    let b : Matrix (Fin k) (Fin k) ℝ := t • B
    let ra : Matrix (Fin k) (Fin k) ℝ := NormedSpace.exp a - 1 - a
    let rb : Matrix (Fin k) (Fin k) ℝ := NormedSpace.exp b - 1 - b
    let rs : Matrix (Fin k) (Fin k) ℝ := NormedSpace.exp (t • (A + B)) - 1 - t • (A + B)
    have habs : |t| ≤ 1 := ht
    have hKA : 0 ≤ K A := SAP.P005a.WH.W2.P.T9_L4.expTailBound_nonneg A
    have hKB : 0 ≤ K B := SAP.P005a.WH.W2.P.T9_L4.expTailBound_nonneg B
    have hKS : 0 ≤ K (A + B) := SAP.P005a.WH.W2.P.T9_L4.expTailBound_nonneg (A + B)
    have hta : ‖a‖ ≤ |t| * ‖A‖ := by simp [a, norm_smul]
    have htb : ‖b‖ ≤ |t| * ‖B‖ := by simp [b, norm_smul]
    have hra : ‖ra‖ ≤ t ^ 2 * K A := by
      simpa [ra, a, K] using SAP.P005a.WH.W2.P.T9_L4.exp_remainder_bound A t ht
    have hrb : ‖rb‖ ≤ t ^ 2 * K B := by
      simpa [rb, b, K] using SAP.P005a.WH.W2.P.T9_L4.exp_remainder_bound B t ht
    have hrs : ‖rs‖ ≤ t ^ 2 * K (A + B) := by
      simpa [rs, K] using SAP.P005a.WH.W2.P.T9_L4.exp_remainder_bound (A + B) t ht
    have hident : NormedSpace.exp (t • (A + B)) - NormedSpace.exp a * NormedSpace.exp b =
        rs - (a * b + ra + rb + a * rb + ra * b + ra * rb) := by
      dsimp [rs, ra, rb, a, b]
      rw [smul_add]
      noncomm_ring
    have hmain : ‖NormedSpace.exp (t • (A + B)) - NormedSpace.exp a * NormedSpace.exp b‖ ≤
        ‖rs‖ + (‖a * b‖ + ‖ra‖ + ‖rb‖ + ‖a * rb‖ + ‖ra * b‖ + ‖ra * rb‖) := by
      rw [hident]
      calc
        ‖rs - (a * b + ra + rb + a * rb + ra * b + ra * rb)‖ ≤
            ‖rs‖ + ‖a * b + ra + rb + a * rb + ra * b + ra * rb‖ := norm_sub_le _ _
        _ ≤ ‖rs‖ + (‖a * b‖ + ‖ra‖ + ‖rb‖ + ‖a * rb‖ + ‖ra * b‖ + ‖ra * rb‖) := by
          apply add_le_add_right
          calc
            ‖a * b + ra + rb + a * rb + ra * b + ra * rb‖ ≤
                ‖a * b + ra + rb + a * rb + ra * b‖ + ‖ra * rb‖ := norm_add_le _ _
            _ ≤ (‖a * b + ra + rb + a * rb‖ + ‖ra * b‖) + ‖ra * rb‖ := by
              gcongr
              exact norm_add_le _ _
            _ ≤ ((‖a * b + ra + rb‖ + ‖a * rb‖) + ‖ra * b‖) + ‖ra * rb‖ := by
              gcongr
              exact norm_add_le _ _
            _ ≤ (((‖a * b + ra‖ + ‖rb‖) + ‖a * rb‖) + ‖ra * b‖) + ‖ra * rb‖ := by
              gcongr
              exact norm_add_le _ _
            _ ≤ (((‖a * b‖ + ‖ra‖ + ‖rb‖) + ‖a * rb‖) + ‖ra * b‖) + ‖ra * rb‖ := by
              gcongr
              exact norm_add_le _ _
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    have hmulAB : ‖a * b‖ ≤ t ^ 2 * (‖A‖ * ‖B‖) := by
      calc
        ‖a * b‖ ≤ ‖a‖ * ‖b‖ := norm_mul_le _ _
        _ ≤ (|t| * ‖A‖) * (|t| * ‖B‖) := mul_le_mul hta htb (norm_nonneg _) (by positivity)
        _ = t ^ 2 * (‖A‖ * ‖B‖) := by rw [← sq_abs]; ring
    have hmulArb : ‖a * rb‖ ≤ t ^ 2 * (‖A‖ * K B) := by
      calc
        ‖a * rb‖ ≤ ‖a‖ * ‖rb‖ := norm_mul_le _ _
        _ ≤ (|t| * ‖A‖) * (t ^ 2 * K B) := mul_le_mul hta hrb (norm_nonneg _) (by positivity)
        _ ≤ t ^ 2 * (‖A‖ * K B) := by
          calc
            (|t| * ‖A‖) * (t ^ 2 * K B) ≤ (1 * ‖A‖) * (t ^ 2 * K B) := by gcongr
            _ = t ^ 2 * (‖A‖ * K B) := by ring
    have hmulRab : ‖ra * b‖ ≤ t ^ 2 * (K A * ‖B‖) := by
      calc
        ‖ra * b‖ ≤ ‖ra‖ * ‖b‖ := norm_mul_le _ _
        _ ≤ (t ^ 2 * K A) * (|t| * ‖B‖) := mul_le_mul hra htb (norm_nonneg _) (by positivity)
        _ ≤ t ^ 2 * (K A * ‖B‖) := by
          calc
            (t ^ 2 * K A) * (|t| * ‖B‖) ≤ (t ^ 2 * K A) * (1 * ‖B‖) := by gcongr
            _ = t ^ 2 * (K A * ‖B‖) := by ring
    have hmulR : ‖ra * rb‖ ≤ t ^ 2 * (K A * K B) := by
      calc
        ‖ra * rb‖ ≤ ‖ra‖ * ‖rb‖ := norm_mul_le _ _
        _ ≤ (t ^ 2 * K A) * (t ^ 2 * K B) := mul_le_mul hra hrb (norm_nonneg _) (by positivity)
        _ ≤ t ^ 2 * (K A * K B) := by
          have hle : t ^ 2 ≤ 1 := by
            rw [← sq_abs t]
            exact pow_le_one₀ (abs_nonneg t) habs
          calc
            (t ^ 2 * K A) * (t ^ 2 * K B) = t ^ 2 * (t ^ 2 * (K A * K B)) := by ring
            _ ≤ t ^ 2 * (K A * K B) := by
              apply mul_le_mul_of_nonneg_left _ ht2
              calc
                t ^ 2 * (K A * K B) ≤ 1 * (K A * K B) := mul_le_mul_of_nonneg_right hle (by positivity)
                _ = K A * K B := by ring
    have hsum : ‖rs‖ + (‖a * b‖ + ‖ra‖ + ‖rb‖ + ‖a * rb‖ + ‖ra * b‖ + ‖ra * rb‖) ≤ C * t ^ 2 := by
      dsimp [C, K]
      have hK1 := hKS
      have hK2 := hKA
      have hK3 := hKB
      rw [mul_comm C (t ^ 2)]
      nlinarith [hrs, hmulAB, hra, hrb, hmulArb, hmulRab, hmulR, hK1, hK2, hK3]
    simpa [a, b] using hmain.trans hsum
