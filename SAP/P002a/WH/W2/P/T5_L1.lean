import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace SAP.P002a.WH.W2.P.T5_L1

theorem rigidity {n : ℕ} (q : Fin n → ℝ) (A : ℝ) (hn : 2 ≤ n)
    (_hA : 0 ≤ A)
    (hthreshold : A^2 < ((n : ℝ)-1)/(n : ℝ))
    (hbound : SAP.P002a.fourthNorm q ≤
      A * Real.sqrt ((∑ i, q i^2)/((n : ℝ)-1))) :
    ∀ i, q i = 0 := by
  let N : ℝ := n
  let S2 : ℝ := ∑ i, q i^2
  let S4 : ℝ := ∑ i, q i^4
  have hN : 2 ≤ N := by dsimp [N]; exact_mod_cast hn
  have hNpos : 0 < N := by linarith
  have hdpos : 0 < N - 1 := by linarith
  have hS2non : 0 ≤ S2 := by
    dsimp [S2]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  have hS4non : 0 ≤ S4 := by
    dsimp [S4]
    exact Finset.sum_nonneg fun i _ => by positivity
  have hCS : S2^2 ≤ N*S4 := by
    simpa [S2, S4, N] using AronowAudit.P002.fourth_moment_CS n q
  have hroot : Real.sqrt (Real.sqrt (S4/N)) ≤
      A * Real.sqrt (S2/(N-1)) := by
    simpa [SAP.P002a.fourthNorm, SAP.P002a.mean, S2, S4, N] using hbound
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg (Real.sqrt (S4/N))) hroot 4
  have hleft : (Real.sqrt (Real.sqrt (S4/N)))^4 = S4/N := by
    calc
      _ = ((Real.sqrt (Real.sqrt (S4/N)))^2)^2 := by ring
      _ = (Real.sqrt (S4/N))^2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = S4/N := Real.sq_sqrt (div_nonneg hS4non hNpos.le)
  have hright : (A * Real.sqrt (S2/(N-1)))^4 =
      A^4*S2^2/(N-1)^2 := by
    rw [mul_pow]
    have hs : (Real.sqrt (S2/(N-1)))^4 = (S2/(N-1))^2 := by
      calc
        _ = ((Real.sqrt (S2/(N-1)))^2)^2 := by ring
        _ = (S2/(N-1))^2 := by
          rw [Real.sq_sqrt (div_nonneg hS2non hdpos.le)]
    rw [hs]
    field_simp [ne_of_gt hdpos]
  rw [hleft, hright] at hp
  have hpow : S4/N ≤ A^4*S2^2/(N-1)^2 := hp
  let t : ℝ := (N-1)/N
  have htpos : 0 < t := by dsimp [t]; exact div_pos hdpos hNpos
  have hA2 : A^2 < t := by
    simpa [t, N] using hthreshold
  have hA4 : A^4 < t^2 := by
    calc
      A^4 = A^2*A^2 := by ring
      _ ≤ A^2*t := mul_le_mul_of_nonneg_left (le_of_lt hA2) (sq_nonneg A)
      _ < t*t := mul_lt_mul_of_pos_right hA2 htpos
      _ = t^2 := by ring
  have hA4scaled : N^2*A^4 < (N-1)^2 := by
    calc
      N^2*A^4 = A^4*N^2 := by ring
      _ < t^2*N^2 := mul_lt_mul_of_pos_right hA4 (sq_pos_of_pos hNpos)
      _ = (N-1)^2 := by
        dsimp [t]
        field_simp [ne_of_gt hNpos]
  have hpow' := (div_le_div_iff₀ hNpos (sq_pos_of_pos hdpos)).mp hpow
  have hCSmul := mul_le_mul_of_nonneg_right hCS (sq_nonneg (N-1))
  have hpowmul := mul_le_mul_of_nonneg_left hpow' hNpos.le
  have hcombine : (N-1)^2*S2^2 ≤ N^2*A^4*S2^2 := by
    calc
      (N-1)^2*S2^2 = S2^2*(N-1)^2 := by ring
      _ ≤ (N*S4)*(N-1)^2 := hCSmul
      _ = N*(S4*(N-1)^2) := by ring
      _ ≤ N*(A^4*S2^2*N) := hpowmul
      _ = N^2*A^4*S2^2 := by ring
  have hS2zero : S2 = 0 := by
    by_contra hne
    have hS2pos : 0 < S2 := lt_of_le_of_ne hS2non (Ne.symm hne)
    have hstrict := mul_lt_mul_of_pos_right hA4scaled (sq_pos_of_pos hS2pos)
    nlinarith
  intro i
  have hsum : (∑ j, q j^2) = 0 := by simpa [S2] using hS2zero
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => sq_nonneg (q j))).mp hsum i (Finset.mem_univ i)
  nlinarith [sq_nonneg (q i)]

end SAP.P002a.WH.W2.P.T5_L1

theorem SAP.P002a.WH.W2.T5_L1_proof : SAP.P002a.WH.W2.T5_L1 := by
  intro n q A hn hA hthreshold hbound
  exact SAP.P002a.WH.W2.P.T5_L1.rigidity q A hn hA hthreshold hbound
