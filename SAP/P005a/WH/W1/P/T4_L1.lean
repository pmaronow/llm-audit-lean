import SAP.P005a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W1.P.T4_L1

end SAP.P005a.WH.W1.P.T4_L1

theorem SAP.P005a.WH.W1.T4_L1_proof : SAP.P005a.WH.W1.T4_L1 := by
  intro N s p κ D K hN hs hsN hp hps hκ hD hK
  dsimp only
  have hNpos : 0 < N := by linarith
  have hNm1 : 0 < N - 1 := by linarith
  have hNge1 : 1 ≤ N := by linarith
  have hNsub : 0 ≤ N - s := by linarith
  have hdenA : 0 < s * (N - 1) := mul_pos hs hNm1
  have hdenPA : 0 < p * (N - 1) := mul_pos hp hNm1
  have hdenB : 0 < s ^ 3 * (N - 1) := by positivity
  have hdenPB : 0 < p ^ 3 * N * (N - 1) := by positivity
  have hAcore : p * (N - s) ≤ s := by
    calc
      p * (N - s) ≤ p * N := mul_le_mul_of_nonneg_left (by linarith) hp.le
      _ ≤ s := hps
  have hA : 2 * (N - s) / (s * (N - 1)) ≤ 2 / (p * (N - 1)) := by
    apply (div_le_div_iff₀ hdenA hdenPA).2
    have hmul := mul_le_mul_of_nonneg_right hAcore (show 0 ≤ 2 * (N - 1) by positivity)
    nlinarith [hmul]
  have hcube : p ^ 3 * N ^ 3 ≤ s ^ 3 := by
    have h := pow_le_pow_left₀ (mul_nonneg hp.le hNpos.le) hps 3
    simpa [mul_pow] using h
  have hNpow : N ^ 2 ≤ N ^ 3 := by
    calc
      N ^ 2 = N ^ 2 * 1 := by ring
      _ ≤ N ^ 2 * N := mul_le_mul_of_nonneg_left hNge1 (by positivity)
      _ = N ^ 3 := by ring
  have hpcubeN2 : p ^ 3 * N ^ 2 ≤ p ^ 3 * N ^ 3 :=
    mul_le_mul_of_nonneg_left hNpow (by positivity)
  have hBcore : (N - s) * p ^ 3 * N ^ 2 ≤ s ^ 3 := by
    calc
      (N - s) * p ^ 3 * N ^ 2 = (N - s) * (p ^ 3 * N ^ 2) := by ring
      _ ≤ N * (p ^ 3 * N ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = p ^ 3 * N ^ 3 := by ring
      _ ≤ s ^ 3 := hcube
  have hB : 2 * (N - s) * N / (s ^ 3 * (N - 1)) ≤
      2 / (p ^ 3 * N * (N - 1)) := by
    apply (div_le_div_iff₀ hdenB hdenPB).2
    have hmul := mul_le_mul_of_nonneg_right hBcore
      (show 0 ≤ 2 * (N - 1) by positivity)
    nlinarith [hmul]
  have hNratio : N / (N - 1) ≤ 2 := by
    rw [div_le_iff₀ hNm1]
    nlinarith
  have hNlinear : N ≤ 2 * (N - 1) := (div_le_iff₀ hNm1).mp hNratio
  have hAnon : 0 ≤ 2 * (N - s) / (s * (N - 1)) :=
    div_nonneg (by positivity) hdenA.le
  have hBnonneg : 0 ≤ 2 * (N - s) * N / (s ^ 3 * (N - 1)) :=
    div_nonneg (by positivity) hdenB.le
  have hAterm : 2 * (N - s) / (s * (N - 1)) * N ^ 2 * κ ^ 2 * K ≤
      4 * K * (N * κ ^ 2) / p := by
    calc
      _ ≤ (2 / (p * (N - 1))) * N ^ 2 * κ ^ 2 * K := by
        gcongr
      _ = (2 * (N / (N - 1)) * (N * κ ^ 2 * K)) / p := by
        field_simp [ne_of_gt hp, ne_of_gt hNm1]
      _ ≤ (4 * (N * κ ^ 2 * K)) / p := by
        apply div_le_div_of_nonneg_right _ hp.le
        calc
          2 * (N / (N - 1)) * (N * κ ^ 2 * K) = (N / (N - 1)) * (2 * (N * κ ^ 2 * K)) := by ring
          _ ≤ 2 * (2 * (N * κ ^ 2 * K)) :=
            mul_le_mul_of_nonneg_right hNratio (by positivity)
          _ = 4 * (N * κ ^ 2 * K) := by ring
      _ = 4 * K * (N * κ ^ 2) / p := by ring
  have hNratioCoeff : 2 / (N - 1) ≤ 4 / N := by
    apply (div_le_div_iff₀ hNm1 hNpos).2
    nlinarith [hNlinear]
  have hBterm : 2 * (N - s) * N / (s ^ 3 * (N - 1)) * N * κ * D * K ≤
      4 * K * κ * D / (p ^ 3 * N) := by
    calc
      _ ≤ (2 / (p ^ 3 * N * (N - 1))) * N * κ * D * K := by
        gcongr
      _ = ((2 / (N - 1)) * (κ * D * K)) / p ^ 3 := by
        field_simp [ne_of_gt hp, ne_of_gt hNpos, ne_of_gt hNm1]
      _ ≤ ((4 / N) * (κ * D * K)) / p ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hNratioCoeff (by positivity)
      _ = 4 * K * κ * D / (p ^ 3 * N) := by
        field_simp [ne_of_gt hp, ne_of_gt hNpos]
  have hAterm' : 2 * (N - s) / (s * (N - 1)) * N ^ 2 * κ ^ 2 * K ≤
      (4 * K * (1 / p)) * (N * κ ^ 2) := by
    calc
      _ ≤ 4 * K * (N * κ ^ 2) / p := hAterm
      _ = (4 * K * (1 / p)) * (N * κ ^ 2) := by ring
  have hBterm' : 2 * (N - s) * N / (s ^ 3 * (N - 1)) * N * κ * D * K ≤
      (4 * K * (1 / p ^ 3)) * (κ * D / N) := by
    calc
      _ ≤ 4 * K * κ * D / (p ^ 3 * N) := hBterm
      _ = (4 * K * (1 / p ^ 3)) * (κ * D / N) := by
        field_simp [ne_of_gt hp, ne_of_gt hNpos]
  have hcross₁ : 0 ≤ (4 * K * (1 / p)) * (κ * D / N) := by positivity
  have hcross₂ : 0 ≤ (4 * K * (1 / p ^ 3)) * (N * κ ^ 2) := by positivity
  refine ⟨hA, hB, ?_, ?_⟩
  · exact add_nonneg (by positivity) (by positivity)
  · calc
      _ ≤ (4 * K * (1 / p)) * (N * κ ^ 2) +
          (4 * K * (1 / p ^ 3)) * (κ * D / N) := add_le_add hAterm' hBterm'
      _ ≤ (4 * K * (1 / p + 1 / p ^ 3)) * (N * κ ^ 2 + κ * D / N) := by
        nlinarith [hcross₁, hcross₂]
