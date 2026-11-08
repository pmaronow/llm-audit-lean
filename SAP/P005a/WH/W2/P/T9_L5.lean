import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2.P.T9_L5

noncomputable section

open Filter
open scoped Matrix.Norms.Operator Topology

lemma norm_exp_bound {k : ℕ} (hk : 0 < k) (X : Matrix (Fin k) (Fin k) ℝ) :
    ‖NormedSpace.exp X‖ ≤ Real.exp ‖X‖ := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hs : Summable (fun n : ℕ => ‖((↑n.factorial : ℝ)⁻¹) • X ^ n‖) :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) X
  have ht : Summable (fun n : ℕ => ((↑n.factorial : ℝ)⁻¹) • ‖X‖ ^ n) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (x := ‖X‖)).summable
  have hterm (n : ℕ) :
      ‖((↑n.factorial : ℝ)⁻¹) • X ^ n‖ ≤ ((↑n.factorial : ℝ)⁻¹) • ‖X‖ ^ n := by
    have hn : 0 ≤ (↑n.factorial : ℝ)⁻¹ := by positivity
    have hqn : ‖(↑n.factorial : ℝ)⁻¹‖ = (↑n.factorial : ℝ)⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
    rw [norm_smul, hqn]
    calc
      (↑n.factorial : ℝ)⁻¹ * ‖X ^ n‖ ≤ (↑n.factorial : ℝ)⁻¹ * ‖X‖ ^ n :=
        mul_le_mul_of_nonneg_left (norm_pow_le X n) hn
      _ = (↑n.factorial : ℝ)⁻¹ • ‖X‖ ^ n := by rw [smul_eq_mul]
  calc
    ‖NormedSpace.exp X‖ = ‖∑' n : ℕ, ((↑n.factorial : ℝ)⁻¹) • X ^ n‖ := by
      rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
    _ ≤ ∑' n : ℕ, ‖((↑n.factorial : ℝ)⁻¹) • X ^ n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, ((↑n.factorial : ℝ)⁻¹) • ‖X‖ ^ n := hs.tsum_le_tsum hterm ht
    _ = Real.exp ‖X‖ := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ)]

lemma norm_pow_le_of_norm_le {R : Type} [NormedRing R] [NormOneClass R] (x : R) (n : ℕ) {K : ℝ}
    (hx : ‖x‖ ≤ K) : ‖x ^ n‖ ≤ K ^ n := by
  exact (norm_pow_le x n).trans (pow_le_pow_left₀ (norm_nonneg x) hx n)

lemma norm_pow_sub_pow_le {R : Type} [NormedRing R] [NormOneClass R] (x y : R) (n : ℕ) {K : ℝ}
    (hx : ‖x‖ ≤ K) (hy : ‖y‖ ≤ K) (hK : 1 ≤ K) :
    ‖x ^ n - y ^ n‖ ≤ (n : ℝ) * K ^ n * ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow : ‖x ^ n‖ ≤ K ^ n := norm_pow_le_of_norm_le x n hx
      calc
        ‖x ^ (n + 1) - y ^ (n + 1)‖ = ‖x ^ n * (x - y) + (x ^ n - y ^ n) * y‖ := by
          congr 1
          rw [pow_succ, pow_succ]
          noncomm_ring
        _ ≤ ‖x ^ n * (x - y)‖ + ‖(x ^ n - y ^ n) * y‖ := norm_add_le _ _
        _ ≤ ‖x ^ n‖ * ‖x - y‖ + ‖x ^ n - y ^ n‖ * ‖y‖ := by
          exact add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ K * K ^ n * ‖x - y‖ + ((n : ℝ) * K ^ n * ‖x - y‖) * K := by
          have hkp : K ^ n ≤ K * K ^ n := by
            calc K ^ n = 1 * K ^ n := by ring
                 _ ≤ K * K ^ n := mul_le_mul_of_nonneg_right hK (pow_nonneg (le_trans zero_le_one hK) n)
          apply add_le_add
          · exact (mul_le_mul_of_nonneg_right (le_trans hpow hkp) (norm_nonneg _))
          · have hc : 0 ≤ (n : ℝ) * K ^ n * ‖x - y‖ := by positivity
            calc
              ‖x ^ n - y ^ n‖ * ‖y‖ ≤ ((n : ℝ) * K ^ n * ‖x - y‖) * ‖y‖ :=
                mul_le_mul_of_nonneg_right ih (norm_nonneg _)
              _ ≤ ((n : ℝ) * K ^ n * ‖x - y‖) * K :=
                mul_le_mul_of_nonneg_left hy hc
        _ = ((n + 1 : ℕ) : ℝ) * K ^ (n + 1) * ‖x - y‖ := by
          rw [pow_succ]
          push_cast
          ring_nf

lemma dyadic_tendsto_zero : Tendsto (fun j : ℕ => ((2 : ℝ)^j)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun j : ℕ => ((1 / 2 : ℝ)^j)) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  convert h using 1 <;> simp [one_div, inv_pow]


end

end SAP.P005a.WH.W2.P.T9_L5

open SAP.P005a.WH.W2.P.T9_L5
open Filter
open scoped Matrix.Norms.Operator Topology

theorem SAP.P005a.WH.W2.T9_L5_proof : SAP.P005a.WH.W2.T9_L5 := by
  intro hsplit k A B
  by_cases hk0 : k = 0
  · subst k
    letI : Subsingleton (Matrix (Fin 0) (Fin 0) ℝ) := by infer_instance
    have hconst :
        (fun j : ℕ =>
          (NormedSpace.exp (((2 : ℝ)^j)⁻¹ • A) *
            NormedSpace.exp (((2 : ℝ)^j)⁻¹ • B))^(2^j)) =
        fun _ : ℕ => NormedSpace.exp (A+B) := by
      funext j
      exact Subsingleton.elim _ _
    rw [hconst]
    exact tendsto_const_nhds
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    let t : ℕ → ℝ := fun j => ((2 : ℝ)^j)⁻¹
    let m : ℕ → ℕ := fun j => 2^j
    let M : ℝ := ‖A‖ + ‖B‖
    let K : ℕ → ℝ := fun j => Real.exp (t j * M)
    let U : ℕ → Matrix (Fin k) (Fin k) ℝ := fun j =>
      NormedSpace.exp (t j • A) * NormedSpace.exp (t j • B)
    let V : ℕ → Matrix (Fin k) (Fin k) ℝ := fun j =>
      NormedSpace.exp (t j • (A+B))
    have ht : Tendsto t atTop (nhds 0) := by
      simpa [t] using dyadic_tendsto_zero
    have htpos (j : ℕ) : 0 < t j := by
      dsimp [t]
      positivity
    have htle (j : ℕ) : t j ≤ 1 := by
      dsimp [t]
      exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))
    have hmcast (j : ℕ) : (m j : ℝ) * t j = 1 := by
      dsimp [m, t]
      rw [Nat.cast_pow]
      exact mul_inv_cancel₀ (pow_ne_zero j (by norm_num : (2 : ℝ) ≠ 0))
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hKone (j : ℕ) : 1 ≤ K j := by
      apply (Real.one_le_exp_iff).2
      exact mul_nonneg (le_of_lt (htpos j)) hM
    have hU (j : ℕ) : ‖U j‖ ≤ K j := by
      dsimp [U, K]
      calc
        ‖NormedSpace.exp (t j • A) * NormedSpace.exp (t j • B)‖ ≤
            ‖NormedSpace.exp (t j • A)‖ * ‖NormedSpace.exp (t j • B)‖ := norm_mul_le _ _
        _ ≤ Real.exp ‖t j • A‖ * Real.exp ‖t j • B‖ := by
          exact mul_le_mul (norm_exp_bound hk _) (norm_exp_bound hk _)
            (norm_nonneg _) (Real.exp_nonneg _)
        _ = Real.exp (t j * M) := by
          rw [← Real.exp_add]
          congr 1
          simp [norm_smul, Real.norm_eq_abs, abs_of_pos (htpos j), M]
          ring
    have hV (j : ℕ) : ‖V j‖ ≤ K j := by
      dsimp [V, K]
      calc
        ‖NormedSpace.exp (t j • (A+B))‖ ≤ Real.exp ‖t j • (A+B)‖ :=
          norm_exp_bound hk _
        _ ≤ Real.exp (t j * M) := by
          apply Real.exp_le_exp.mpr
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (htpos j)]
          dsimp [M]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (le_of_lt (htpos j))
    obtain ⟨C, hC0, hC⟩ := hsplit k A B
    have htcond (j : ℕ) : |t j| ≤ 1 := by
      rw [abs_of_pos (htpos j)]
      exact htle j
    have hlocal (j : ℕ) : ‖V j - U j‖ ≤ C * (t j)^2 := by
      exact hC (t j) (htcond j)
    have hunsplit (j : ℕ) : V j ^ (m j) = NormedSpace.exp (A+B) := by
      rw [← Matrix.exp_nsmul]
      congr 1
      dsimp [V, m, t]
      simp only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_pow,
        Nat.cast_ofNat, mul_inv_cancel₀ (pow_ne_zero j (by norm_num : (2 : ℝ) ≠ 0)),
        one_smul]
    have hKpow (j : ℕ) : (K j)^(m j) = Real.exp M := by
      dsimp [K]
      rw [← Real.exp_nat_mul]
      congr 1
      calc
        (m j : ℝ) * (t j * M) = ((m j : ℝ) * t j) * M := by ring
        _ = M := by rw [hmcast]; ring
    have hbound (j : ℕ) :
        ‖U j ^ (m j) - NormedSpace.exp (A+B)‖ ≤ (C * Real.exp M) * t j := by
      rw [← hunsplit j]
      calc
        ‖U j ^ (m j) - V j ^ (m j)‖ ≤
            (m j : ℝ) * (K j)^(m j) * ‖U j - V j‖ :=
          norm_pow_sub_pow_le (U j) (V j) (m j) (hU j) (hV j) (hKone j)
        _ ≤ (m j : ℝ) * (K j)^(m j) * (C * (t j)^2) :=
          mul_le_mul_of_nonneg_left (by simpa [norm_sub_rev] using hlocal j)
            (by positivity)
        _ = (C * Real.exp M) * t j := by
          rw [hKpow j]
          calc
            (m j : ℝ) * Real.exp M * (C * (t j)^2) =
                C * Real.exp M * (((m j : ℝ) * t j) * t j) := by ring
            _ = (C * Real.exp M) * t j := by rw [hmcast]; ring
    have herror : Tendsto (fun j : ℕ => ‖U j^(m j) - NormedSpace.exp (A+B)‖)
        atTop (nhds 0) := by
      apply squeeze_zero (fun j => norm_nonneg _) hbound
      simpa using (ht.const_mul (C * Real.exp M))
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa [U, m, t] using herror

