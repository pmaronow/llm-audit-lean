import AronowAudit.P005.P005_Formalization

namespace AronowAudit.P005.Wave1

noncomputable section
open scoped BigOperators Matrix
open AronowAudit.P005 Finset Filter
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

/-- P005-T17(e): the corrected deterministic contraction is O(kappa/n),
including sequences with zero or varying covariate dimension. -/
theorem corrected_contraction_order (d m : ℕ → ℕ)
    (P : (n : ℕ) → AronowAudit.P005.Population n (d n)) (h :
      (∀ n, 3 ≤ n → d n ≤ n ∧ 0 < m n ∧ m n < n) ∧
      (∃ K : ℝ, 0 ≤ K ∧ ∀ n, 3 ≤ n →
        AronowAudit.P005.popMean (fun i => (P n).yT i^2) ≤ K ∧
        AronowAudit.P005.popMean (fun i => (P n).yC i^2) ≤ K ∧
        ∀ k, AronowAudit.P005.popMean (fun i => (P n).x i k^2) ≤ K) ∧
      (∀ᶠ n in Filter.atTop, AronowAudit.P005.standardized (P n)) ∧
      (∃ lo hi : ℝ, 0 < lo ∧ lo < hi ∧ hi < 1 ∧
        ∀ n, 3 ≤ n → lo < AronowAudit.P005.pT n (m n) ∧ AronowAudit.P005.pT n (m n) < hi)) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => 1/(AronowAudit.P005.pT n (m n)*AronowAudit.P005.pC n (m n)*n*(n-1)) *
        AronowAudit.P005.popMean (fun i => AronowAudit.P005.leverage (P n) i *
          (AronowAudit.P005.commonResidual (P n) (m n) (P n).yT i-AronowAudit.P005.commonResidual (P n) (m n) (P n).yC i)^2))
      (fun n => AronowAudit.P005.kappa (P n)/n) := by
  rcases h with ⟨hsize, ⟨K,hK,hym⟩, hstd, ⟨lo,hi,hlo,hlohi,hhi,halloc⟩⟩
  let L := lo*(1-hi)
  have hL : 0 < L := mul_pos hlo (sub_pos.mpr hhi)
  apply Asymptotics.IsBigO.of_bound (8*K/L)
  filter_upwards [Filter.eventually_ge_atTop (3 : ℕ)] with n hn
  have hnNat : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ)-1 := by linarith
  have n0 : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have n1 : (n : ℝ)-1 ≠ 0 := ne_of_gt hn1
  have hp := halloc n hn
  have hpt : 0 < pT n (m n) := lt_trans hlo hp.1
  have hsum : pT n (m n)+pC n (m n) = 1 := by
    dsimp [pT,pC]
    field_simp [n0]
    <;> ring
  have hpcLower : 1-hi ≤ pC n (m n) := by linarith [hp.2]
  have hpc : 0 < pC n (m n) := lt_of_lt_of_le (sub_pos.mpr hhi) hpcLower
  have pt0 := ne_of_gt hpt
  have pc0 := ne_of_gt hpc
  have hκ : 0 ≤ kappa (P n) := by
    have hu := leverage_le_maximum (P n) hnNat ⟨0,hnNat⟩
    have hl := leverage_nonneg (P n) ⟨0,hnNat⟩
    nlinarith
  let δ := fun i => commonResidual (P n) (m n) (P n).yT i-commonResidual (P n) (m n) (P n).yC i
  have hQ : popMean (fun i => δ i^2) ≤ 4*K :=
    common_residual_difference_second_moment (P n) hnNat K (hym n hn).1 (hym n hn).2.1
  have hQ0 : 0 ≤ popMean (fun i => leverage (P n) i*δ i^2) :=
    mean_nonneg _ _ (fun i _ => mul_nonneg (leverage_nonneg (P n) i) (sq_nonneg _))
  have hweighted : popMean (fun i => leverage (P n) i*δ i^2) ≤
      ((n : ℝ)*kappa (P n))*popMean (fun i => δ i^2) := by
    calc
      _ ≤ popMean (fun i => ((n : ℝ)*kappa (P n))*δ i^2) := by
        apply mean_mono
        intro i hi
        exact mul_le_mul_of_nonneg_right (leverage_le_maximum (P n) hnNat i) (sq_nonneg _)
      _ = _ := mean_mul _ _ _
  have hden : L*((n : ℝ)/2) ≤ pT n (m n)*pC n (m n)*(n-1) := by
    have hproduct : L ≤ pT n (m n)*pC n (m n) :=
      mul_le_mul (le_of_lt hp.1) hpcLower (le_of_lt (sub_pos.mpr hhi)) (le_of_lt hpt)
    have hhalf : (n : ℝ)/2 ≤ n-1 := by linarith
    exact mul_le_mul hproduct hhalf (by positivity) (le_of_lt (mul_pos hpt hpc))
  have hcoeff : kappa (P n)/(pT n (m n)*pC n (m n)*(n-1)) ≤
      2/L * (kappa (P n)/n) := by
    calc
      _ ≤ kappa (P n)/(L*((n : ℝ)/2)) :=
        div_le_div_of_nonneg_left hκ (by positivity) hden
      _ = _ := by field_simp [n0,ne_of_gt hL] <;> ring
  have hf0 : 0 ≤ 1/(pT n (m n)*pC n (m n)*n*(n-1))*
      popMean (fun i => leverage (P n) i*δ i^2) := mul_nonneg (by positivity) hQ0
  have hf : 1/(pT n (m n)*pC n (m n)*n*(n-1))*
      popMean (fun i => leverage (P n) i*δ i^2) ≤ (8*K/L)*(kappa (P n)/n) := by
    calc
      _ ≤ 1/(pT n (m n)*pC n (m n)*n*(n-1))*
          (((n : ℝ)*kappa (P n))*popMean (fun i => δ i^2)) :=
        mul_le_mul_of_nonneg_left hweighted (by positivity)
      _ = kappa (P n)/(pT n (m n)*pC n (m n)*(n-1))*popMean (fun i => δ i^2) := by
        field_simp [n0,n1,pt0,pc0]
        <;> ring
      _ ≤ kappa (P n)/(pT n (m n)*pC n (m n)*(n-1))*(4*K) :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
      _ ≤ (2/L*(kappa (P n)/n))*(4*K) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = _ := by ring
  change ‖1/(pT n (m n)*pC n (m n)*n*(n-1))*
      popMean (fun i => leverage (P n) i*δ i^2)‖ ≤ (8*K/L)*‖kappa (P n)/n‖
  simpa only [Real.norm_eq_abs, abs_of_nonneg hf0,
    abs_of_nonneg (div_nonneg hκ (le_of_lt hn'))] using hf

end
end AronowAudit.P005.Wave1
