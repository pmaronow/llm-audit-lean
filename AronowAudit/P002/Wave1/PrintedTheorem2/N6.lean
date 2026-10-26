import AronowAudit.P002.Wave1.PrintedTheorem2Blueprint

namespace AronowAudit.P002.Wave1.PrintedTheorem2
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Chebyshev for the second raw moment and Markov for the squared first moment. -/
theorem n6_proof : N6 := by
  intro hMSE hDet hProb n P hcenter hQlo hfour h1 h0
  let Q : ℝ := mean (fun i => P.x i 0 ^ 2)
  let f1 : ℝ := ((n : ℝ) - P.pop.n1) /
    ((P.pop.n1 : ℝ) * ((n : ℝ) - 1))
  let f0 : ℝ := (P.pop.n1 : ℝ) /
    (((n : ℝ) - P.pop.n1) * ((n : ℝ) - 1))
  have hn : 2 ≤ n := by omega
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hN1 : 0 < (n : ℝ) - 1 := by linarith
  have hM : 0 < (P.pop.n1 : ℝ) := by
    exact_mod_cast (by omega : 0 < P.pop.n1)
  have hMN : (P.pop.n1 : ℝ) < n := by
    exact_mod_cast (by omega : P.pop.n1 < n)
  have hK : 0 < (n : ℝ) - P.pop.n1 := by linarith
  have hf1 : 0 ≤ f1 := div_nonneg hK.le (mul_pos hM hN1).le
  have hf0 : 0 ≤ f0 := div_nonneg hM.le (mul_pos hK hN1).le
  have hQ : (1/4 : ℝ) ≤ Q := hQlo
  have hQpos : 0 < Q := by linarith
  have hhalf : 0 < Q / 2 := by positivity
  have hmeanx : mean (fun i => P.x i 0) = 0 := by
    simp only [mean, hcenter, zero_div]
  have hUniv : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hgm (q : Fin n → ℝ) :
      groupMean (Finset.univ : Finset (Fin n)) q = mean q := by
    simp only [groupMean, mean, Finset.card_univ, Fintype.card_fin]
  have hpow (i : Fin n) : (P.x i 0 ^ 2) ^ 2 = P.x i 0 ^ 4 := by ring
  have hraw : (∑ i, (P.x i 0 ^ 2 - Q) ^ 2) / (n : ℝ) =
      mean (fun i => P.x i 0 ^ 4) - Q ^ 2 := by
    have h := square_centering Finset.univ (fun i => P.x i 0 ^ 2) 0 hUniv
    simpa only [hgm, sub_zero, hpow, Q, mean] using h
  have hvarbound : (∑ i, (P.x i 0 ^ 2 - Q) ^ 2) / (n : ℝ) ≤ 4 := by
    rw [hraw]
    nlinarith only [hfour, sq_nonneg Q]
  have hmu1 : expectation P.pop (fun S =>
      (groupMean S (fun i => P.x i 0)) ^ 2) = f1 * Q := by
    simpa only [f1, Q, mean, hcenter, zero_div, sub_zero] using
      (hMSE n P.pop (fun i => P.x i 0) h1 h0).1
  have hmu0 : expectation P.pop (fun S =>
      (groupMean Sᶜ (fun i => P.x i 0)) ^ 2) = f0 * Q := by
    simpa only [f0, Q, mean, hcenter, zero_div, sub_zero] using
      (hMSE n P.pop (fun i => P.x i 0) h1 h0).2
  have hsecond (T : Finset (Fin n) → Finset (Fin n)) (f : ℝ) (hf : 0 ≤ f)
      (hE : expectation P.pop (fun S =>
          (groupMean (T S) (fun i => P.x i 0 ^ 2) - Q) ^ 2) =
        f * ((∑ i, (P.x i 0 ^ 2 - Q) ^ 2) / (n : ℝ))) :
      expectation P.pop (fun S =>
        (groupMean (T S) (fun i => P.x i 0 ^ 2) - Q) ^ 2) ≤ 4 * f := by
    calc
      _ = f * ((∑ i, (P.x i 0 ^ 2 - Q) ^ 2) / (n : ℝ)) := hE
      _ ≤ f * 4 := mul_le_mul_of_nonneg_left hvarbound hf
      _ = 4 * f := mul_comm _ _
  have hnu1 : expectation P.pop (fun S =>
      (groupMean S (fun i => P.x i 0 ^ 2) - Q) ^ 2) ≤ 4 * f1 :=
    hsecond (fun S => S) f1 hf1
      (hMSE n P.pop (fun i => P.x i 0 ^ 2) h1 h0).1
  have hnu0 : expectation P.pop (fun S =>
      (groupMean Sᶜ (fun i => P.x i 0 ^ 2) - Q) ^ 2) ≤ 4 * f0 :=
    hsecond (fun S => Sᶜ) f0 hf0
      (hMSE n P.pop (fun i => P.x i 0 ^ 2) h1 h0).2
  rcases hProb n P.pop with ⟨_, hmono, hunion, _, hMarkov⟩
  -- This argument uses the arm map only through its moments and nonemptiness.
  have harm (T : Finset (Fin n) → Finset (Fin n)) (f : ℝ) (hf : 0 ≤ f)
      (hT : ∀ S ∈ assignments P.pop, (T S).Nonempty)
      (hmu : expectation P.pop (fun S =>
          (groupMean (T S) (fun i => P.x i 0)) ^ 2) = f * Q)
      (hnu : expectation P.pop (fun S =>
          (groupMean (T S) (fun i => P.x i 0 ^ 2) - Q) ^ 2) ≤ 4 * f) :
      probability P.pop (fun S => (gram P.x (T S)).det = 0) ≤ 258 * f := by
    let u : Finset (Fin n) → ℝ := fun S => groupMean (T S) (fun i => P.x i 0)
    let v : Finset (Fin n) → ℝ := fun S => groupMean (T S) (fun i => P.x i 0 ^ 2)
    have hinc : ∀ S ∈ assignments P.pop, (gram P.x (T S)).det = 0 →
        (Q / 2) ^ 2 ≤ (v S - Q) ^ 2 ∨ Q / 2 ≤ (u S) ^ 2 := by
      intro S hS hsing
      by_cases hu : Q / 2 ≤ (u S) ^ 2
      · exact Or.inr hu
      · apply Or.inl
        have hu' : (u S) ^ 2 < Q / 2 := lt_of_not_ge hu
        have heq : v S = (u S) ^ 2 := by
          have hd := hDet n P.x (T S) (hT S hS)
          rw [hsing] at hd
          exact sub_eq_zero.mp hd.symm
        have hvlt : v S < Q / 2 := heq.trans_lt hu'
        have hgap : Q / 2 ≤ Q - v S := by linarith
        have hs := pow_le_pow_left₀ hhalf.le hgap 2
        nlinarith only [hs]
    have hmu' : expectation P.pop (fun S => (u S) ^ 2) = f * Q := hmu
    have hnu' : expectation P.pop (fun S => (v S - Q) ^ 2) ≤ 4 * f := hnu
    have htailv : probability P.pop (fun S => (Q / 2) ^ 2 ≤ (v S - Q) ^ 2) ≤
        expectation P.pop (fun S => (v S - Q) ^ 2) / (Q / 2) ^ 2 :=
      hMarkov (fun S => (v S - Q) ^ 2) ((Q / 2) ^ 2) (sq_pos_of_pos hhalf)
        (fun S _ => sq_nonneg (v S - Q))
    have htailu : probability P.pop (fun S => Q / 2 ≤ (u S) ^ 2) ≤
        expectation P.pop (fun S => (u S) ^ 2) / (Q / 2) :=
      hMarkov (fun S => (u S) ^ 2) (Q / 2) hhalf (fun S _ => sq_nonneg (u S))
    have hprob : probability P.pop (fun S => (gram P.x (T S)).det = 0) ≤
        expectation P.pop (fun S => (v S - Q) ^ 2) / (Q / 2) ^ 2 +
          expectation P.pop (fun S => (u S) ^ 2) / (Q / 2) := by
      calc
        _ ≤ probability P.pop
            (fun S => (Q / 2) ^ 2 ≤ (v S - Q) ^ 2 ∨ Q / 2 ≤ (u S) ^ 2) :=
          hmono _ _ hinc
        _ ≤ probability P.pop (fun S => (Q / 2) ^ 2 ≤ (v S - Q) ^ 2) +
            probability P.pop (fun S => Q / 2 ≤ (u S) ^ 2) := hunion _ _
        _ ≤ _ := add_le_add htailv htailu
    have hcoef : 4 / (Q / 2) ^ 2 + 2 ≤ (258 : ℝ) := by
      have hlow : (1/8 : ℝ) ≤ Q / 2 := by linarith
      have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/8) hlow 2
      have hd : 4 / (Q / 2) ^ 2 ≤ (256 : ℝ) := by
        apply (div_le_iff₀ (sq_pos_of_pos hhalf)).mpr
        nlinarith only [hs]
      linarith
    have hfrac : (4 * f) / (Q / 2) ^ 2 + (f * Q) / (Q / 2) =
        f * (4 / (Q / 2) ^ 2 + 2) := by
      field_simp [ne_of_gt hQpos, ne_of_gt hhalf]
      <;> ring
    calc
      probability P.pop (fun S => (gram P.x (T S)).det = 0) ≤
          expectation P.pop (fun S => (v S - Q) ^ 2) / (Q / 2) ^ 2 +
            expectation P.pop (fun S => (u S) ^ 2) / (Q / 2) := hprob
      _ ≤ (4 * f) / (Q / 2) ^ 2 +
          expectation P.pop (fun S => (u S) ^ 2) / (Q / 2) :=
        add_le_add (div_le_div_of_nonneg_right hnu' (sq_nonneg (Q / 2))) le_rfl
      _ = f * (4 / (Q / 2) ^ 2 + 2) := by rw [hmu', hfrac]
      _ ≤ f * 258 := mul_le_mul_of_nonneg_left hcoef hf
      _ = 258 * f := mul_comm _ _
  constructor
  · apply harm (fun S => S) f1 hf1 ?_ hmu1 hnu1
    intro S hS
    apply Finset.card_pos.mp
    have hcard : S.card = P.pop.n1 := (Finset.mem_powersetCard.mp hS).2
    omega
  · apply harm (fun S => Sᶜ) f0 hf0 ?_ hmu0 hnu0
    intro S hS
    apply Finset.card_pos.mp
    have hcard : S.card = P.pop.n1 := (Finset.mem_powersetCard.mp hS).2
    rw [Finset.card_compl, Fintype.card_fin, hcard]
    omega

end
end AronowAudit.P002.Wave1.PrintedTheorem2
