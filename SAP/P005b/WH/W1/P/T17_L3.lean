import SAP.P005b.WH.W1.Leaves
import AronowAudit.P005.Wave1.Gap.GP005B5
import AronowAudit.P005.Wave1.Lib.FiniteDesignOrderTailC

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P005b.WH.W1.P.T17_L3

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
open SAP.P005b SAP.P005b.Bridge

theorem second_moment_zero_on_support {n m : ℕ} (hmn : m ≤ n)
    (F : Finset (Fin n) → ℝ)
    (hF : expectation m (fun S => F S ^ 2) = 0) :
    ∀ S ∈ design n m, F S = 0 := by
  classical
  have hcardN : 0 < (design n m).card := by
    simpa only [design, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin] using Nat.choose_pos hmn
  have hcard : ((design n m).card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardN)
  have hsum : (∑ S ∈ design n m, F S ^ 2) = 0 := by
    unfold expectation at hF
    field_simp [hcard] at hF
    simpa using hF
  intro S hS
  have hle : F S ^ 2 ≤ ∑ T ∈ design n m, F T ^ 2 := by
    exact Finset.single_le_sum (fun T _ => sq_nonneg (F T)) hS
  rw [hsum] at hle
  nlinarith [sq_nonneg (F S)]

end
end SAP.P005b.WH.W1.P.T17_L3

namespace SAP.P005b.WH.W1

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
open SAP.P005b SAP.P005b.Bridge

theorem T17_L3_proof : SAP.P005b.WH.W1.T17_L3 := by
  classical
  intro d m P hstanding hvariance hemean
  rcases hstanding with ⟨hsize, ⟨K, hK, hy⟩, hstd, ⟨lo, hi, hlo, hlohi, hhi, halloc⟩⟩
  let L : ℝ := lo * (1 - hi)
  let C : ℝ := 8 * K / L + 16 * K
  have hL : 0 < L := by
    dsimp [L]
    exact mul_pos hlo (by linarith)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hevent : ∀ᶠ n in atTop,
      3 ≤ n ∧ standardized (P n) ∧
        variance (m n) (wholeW1Star (P n) (m n)) ≤
          kappa (P n)/(pT n (m n)*pC n (m n)*(n-1)) *
            popMean (fun i => wholeW1Delta (P n) (m n) i^2) ∧
        (expectation (m n) (wholeW1Star (P n) (m n)))^2 ≤
          ((n : ℝ)*kappa (P n)*d n/(n-1)^2) *
            popMean (fun i => wholeW1Delta (P n) (m n) i^2) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ), hstd, hvariance, hemean]
      with n hn hs hv hm
    exact ⟨hn, hs, hv, hm⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  intro ε hε
  let M : ℝ := (C + 1) / ε + 1
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hMone : 1 ≤ M := by
    dsimp [M]
    have : 0 ≤ (C + 1) / ε := div_nonneg (by linarith) hε.le
    linarith
  have hEm : C + 1 < ε * M := by
    dsimp [M]
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hε)]
    nlinarith
  have hMle : M ≤ M ^ 2 := by nlinarith [sq_nonneg (M - 1)]
  have hCM : C < ε * M ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hMle hε.le
    linarith
  refine ⟨M, hM, N, ?_⟩
  intro n hn
  obtain ⟨hn3, hPn, hv, hm⟩ := hN n hn
  have hsizeN := hsize n hn3
  have hallocN := halloc n hn3
  have hstdN := hPn.2
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnm : m n ≤ n := Nat.le_of_lt (hsizeN.2.2)
  have hkappa_nonneg : 0 ≤ kappa (P n) := by
    have hlow := (AronowAudit.P005.kappa_bounds (toProject (P n)) (by omega) hPn.2).1
    have : (d n : ℝ) / n ≤ kappa (P n) := hlow
    exact le_trans (div_nonneg (Nat.cast_nonneg _) hnR.le) this
  have hdelta : 0 ≤ popMean (fun i => wholeW1Delta (P n) (m n) i ^ 2) :=
    AronowAudit.P005.mean_nonneg _ _ (fun _ _ => sq_nonneg _)
  obtain ⟨lo_n, hi_n⟩ := hallocN
  have hpT : lo ≤ pT n (m n) := le_of_lt lo_n
  have hpClo : 1 - hi ≤ pC n (m n) := by
    have hsum : pT n (m n) + pC n (m n) = 1 := by
      dsimp [pT, pC]
      field_simp [ne_of_gt hnR]
      ring
    linarith
  have hpC : 0 < pC n (m n) := by
    have : 0 < 1 - hi := by linarith
    exact lt_of_lt_of_le this hpClo
  have hdenprod : L ≤ pT n (m n) * pC n (m n) := by
    dsimp [L]
    calc
      lo * (1 - hi) ≤ lo * pC n (m n) :=
        mul_le_mul_of_nonneg_left hpClo hlo.le
      _ ≤ pT n (m n) * pC n (m n) :=
        mul_le_mul_of_nonneg_right hpT hpC.le
  have hnR3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hnhalf : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by nlinarith
  have hden : 0 < pT n (m n) * pC n (m n) * ((n : ℝ) - 1) :=
    mul_pos (mul_pos (lt_trans hlo lo_n) hpC) (by linarith)
  have hdenlower : L * ((n : ℝ) / 2) ≤
      pT n (m n) * pC n (m n) * ((n : ℝ) - 1) := by
    have hprod_nonneg : 0 ≤ pT n (m n) * pC n (m n) :=
      le_trans (le_of_lt hL) hdenprod
    calc
      L * ((n : ℝ) / 2) ≤ (pT n (m n) * pC n (m n)) * ((n : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hdenprod (by positivity)
      _ ≤ (pT n (m n) * pC n (m n)) * ((n : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hnhalf hprod_nonneg
      _ = _ := by ring
  have hdeltaBound : popMean (fun i => wholeW1Delta (P n) (m n) i ^ 2) ≤ 4 * K := by
    have h := AronowAudit.P005.common_residual_difference_second_moment
      (m := m n) (toProject (P n)) (by omega) K (hy n hn3).1 (hy n hn3).2.1
    change popMean (fun i =>
      (commonResidual (P n) (m n) (P n).yT i -
        commonResidual (P n) (m n) (P n).yC i) ^ 2) ≤ 4 * K at h
    simpa only [wholeW1Delta] using h
  have hqnonneg : 0 ≤ kappa (P n) * d n / n := by positivity
  by_cases hqzero : kappa (P n) * d n / n = 0
  · have hkzero : kappa (P n) = 0 := by
      by_cases hd0 : d n = 0
      · have hlev : ∀ i, leverage (P n) i = 0 := by
          intro i
          simp [leverage, dot, hd0]
        have hupper : kappa (P n) ≤ 0 := by
          unfold kappa
          apply csSup_le
          · exact ⟨_, Set.mem_range_self (⟨0, by omega⟩ : Fin n)⟩
          · rintro r ⟨i, rfl⟩
            simp [hlev]
        linarith
      · have hdlow : (1 : ℝ) ≤ d n := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd0)
        have hprod : kappa (P n) * (d n : ℝ) = 0 := by
          rcases (div_eq_zero_iff).mp hqzero with hprod | hdenzero
          · exact hprod
          · exact (ne_of_gt hnR hdenzero).elim
        nlinarith
    have hvarzero : variance (m n) (wholeW1Star (P n) (m n)) ≤ 0 := by
      simpa [hkzero] using hv
    have hmeanzero : (expectation (m n) (wholeW1Star (P n) (m n))) ^ 2 ≤ 0 := by
      simpa [hkzero] using hm
    have hvarnonneg : 0 ≤ variance (m n) (wholeW1Star (P n) (m n)) :=
      AronowAudit.P005.Wave1.t4_variance_nonneg _ _
    have hsecondzero :
        expectation (m n) (fun S => wholeW1Star (P n) (m n) S ^ 2) = 0 := by
      have hid := AronowAudit.P005.Wave1.t4_variance_eq hnm (wholeW1Star (P n) (m n))
      have hnonneg := AronowAudit.P005.Wave1.t4_expectation_nonneg
        (m := m n) (fun S => wholeW1Star (P n) (m n) S ^ 2)
        (fun _ _ => sq_nonneg _)
      have hidLocal : variance (m n) (wholeW1Star (P n) (m n)) =
          expectation (m n) (fun S => wholeW1Star (P n) (m n) S ^ 2) -
            (expectation (m n) (wholeW1Star (P n) (m n))) ^ 2 := by
        simpa only [Bridge.variance_eq, Bridge.expectation_eq] using hid
      have hnonnegLocal :
          0 ≤ expectation (m n) (fun S => wholeW1Star (P n) (m n) S ^ 2) := by
        simpa only [Bridge.expectation_eq] using hnonneg
      have hle : expectation (m n) (fun S => wholeW1Star (P n) (m n) S ^ 2) ≤ 0 := by
        nlinarith [hidLocal, hvarzero, hmeanzero]
      linarith
    have hzero := SAP.P005b.WH.W1.P.T17_L3.second_moment_zero_on_support
      hnm (wholeW1Star (P n) (m n)) hsecondzero
    have htail : probability (m n)
        (fun S => |wholeW1Star (P n) (m n) S| > M *
          Real.sqrt (kappa (P n) * d n / n)) < ε := by
      have hsub : ∀ S ∈ design n (m n),
          |wholeW1Star (P n) (m n) S| > M *
            Real.sqrt (kappa (P n) * d n / n) → False := by
        intro S hS hbad
        have hF := hzero S hS
        simp [hF, hqzero] at hbad
      have hfilter : (design n (m n)).filter
          (fun S => |wholeW1Star (P n) (m n) S| >
            M * Real.sqrt (kappa (P n) * d n / n)) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro S hS hbad
        exact hsub S hS hbad
      calc
        probability (m n) (fun S => |wholeW1Star (P n) (m n) S| >
            M * Real.sqrt (kappa (P n) * d n / n)) = 0 := by
          unfold probability
          rw [hfilter]
          simp
        _ < ε := hε
    simpa using htail
  · have hqpos : 0 < kappa (P n) * d n / n := lt_of_le_of_ne hqnonneg (Ne.symm hqzero)
    let q : ℝ := kappa (P n) * d n / n
    let r : ℝ := Real.sqrt q
    have hrpos : 0 < r := Real.sqrt_pos.2 (by simpa [q] using hqpos)
    have hrsq : r ^ 2 = q := Real.sq_sqrt (by simpa [q] using hqnonneg)
    have hvariance_bound :
        variance (m n) (wholeW1Star (P n) (m n)) ≤
          (8 * K / L) * (kappa (P n) / n) := by
      have hratio :
          kappa (P n) /
              (pT n (m n) * pC n (m n) * ((n : ℝ) - 1)) *
              popMean (fun i => wholeW1Delta (P n) (m n) i ^ 2) ≤
            (8 * K / L) * (kappa (P n) / n) := by
        have hdivle := div_le_div_of_nonneg_left hkappa_nonneg
          (mul_pos hL (by positivity)) hdenlower
        calc
          _ ≤ (kappa (P n) / (L * ((n : ℝ) / 2))) * (4 * K) := by
            apply le_trans (mul_le_mul_of_nonneg_right hdivle hdelta)
            exact mul_le_mul_of_nonneg_left hdeltaBound (by positivity)
          _ = (8 * K / L) * (kappa (P n) / n) := by
            field_simp [ne_of_gt hL, ne_of_gt hnR]
            <;> ring
      exact le_trans hv hratio
    have hmean_bound :
        (expectation (m n) (wholeW1Star (P n) (m n))) ^ 2 ≤
          16 * K * (kappa (P n) * d n / n) := by
      have hnum : 0 ≤ (n : ℝ) * kappa (P n) * d n := by positivity
      have hn2 : ((n : ℝ) / 2) ^ 2 ≤ ((n : ℝ) - 1) ^ 2 := by
        have hleft : 0 ≤ (n : ℝ) / 2 := by positivity
        have hright : 0 ≤ (n : ℝ) - 1 := by linarith
        exact (sq_le_sq₀ hleft hright).2 hnhalf
      have hdenmean : 0 < ((n : ℝ) / 2) ^ 2 := by positivity
      have hdivmean := div_le_div_of_nonneg_left hnum hdenmean hn2
      calc
        (expectation (m n) (wholeW1Star (P n) (m n))) ^ 2 ≤
            ((n : ℝ) * kappa (P n) * d n / (((n : ℝ) - 1) ^ 2)) *
              popMean (fun i => wholeW1Delta (P n) (m n) i ^ 2) := hm
        _ ≤ ((n : ℝ) * kappa (P n) * d n / (((n : ℝ) / 2) ^ 2)) * (4 * K) := by
          apply le_trans (mul_le_mul_of_nonneg_right hdivmean hdelta)
          exact mul_le_mul_of_nonneg_left hdeltaBound (by positivity)
        _ = 16 * K * (kappa (P n) * d n / n) := by
          field_simp [ne_of_gt hnR]
          <;> ring
    have hvariance_to_rate :
        variance (m n) (wholeW1Star (P n) (m n)) ≤
          (8 * K / L) * (kappa (P n) * d n / n) := by
      have hκd : kappa (P n) / n ≤ kappa (P n) * d n / n := by
        apply div_le_div_of_nonneg_right _ hnR.le
        have hdcast : (1 : ℝ) ≤ d n := by
          have hdne : d n ≠ 0 := by
            intro hd
            have hdcast : (d n : ℝ) = 0 := by exact_mod_cast hd
            have hqbad : kappa (P n) * (d n : ℝ) / n = 0 := by
              rw [hdcast]
              simp
            exact (ne_of_gt hqpos) hqbad
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hdne)
        nlinarith [mul_le_mul_of_nonneg_left hdcast hkappa_nonneg]
      exact le_trans hvariance_bound
        (mul_le_mul_of_nonneg_left hκd (by positivity))
    have hsecond_bound :
        expectation (m n) (fun S => wholeW1Star (P n) (m n) S ^ 2) ≤ C * q := by
      have hid := AronowAudit.P005.Wave1.t4_variance_eq hnm (wholeW1Star (P n) (m n))
      have hq : kappa (P n) * d n / n = q := rfl
      dsimp [C]
      have hidLocal : variance (m n) (wholeW1Star (P n) (m n)) =
          expectation (m n) (fun S => wholeW1Star (P n) (m n) S ^ 2) -
            (expectation (m n) (wholeW1Star (P n) (m n))) ^ 2 := by
        simpa only [Bridge.variance_eq, Bridge.expectation_eq] using hid
      have hsecondEq :
          expectation (m n) (fun S => wholeW1Star (P n) (m n) S ^ 2) =
            variance (m n) (wholeW1Star (P n) (m n)) +
              (expectation (m n) (wholeW1Star (P n) (m n))) ^ 2 := by
        linarith [hidLocal]
      rw [hsecondEq]
      calc
        variance (m n) (wholeW1Star (P n) (m n)) +
            (expectation (m n) (wholeW1Star (P n) (m n))) ^ 2 ≤
          (8 * K / L) * (kappa (P n) * d n / n) +
            16 * K * (kappa (P n) * d n / n) :=
          add_le_add hvariance_to_rate hmean_bound
        _ = C * q := by dsimp [C, q]; ring
    have hthreshold : 0 < (M * r) ^ 2 := by positivity
    have htailmono :
        probability (m n) (fun S =>
          |wholeW1Star (P n) (m n) S| > M * Real.sqrt (kappa (P n) * d n / n)) ≤
        probability (m n) (fun S =>
          (M * r) ^ 2 < wholeW1Star (P n) (m n) S ^ 2) := by
      apply AronowAudit.P005.Wave1.tailC_probability_mono
      intro S hS hbad
      have hsq := (sq_lt_sq₀ (le_of_lt (mul_pos hM hrpos))
        (abs_nonneg (wholeW1Star (P n) (m n) S))).2 (by
          simpa [r, q] using hbad)
      simpa only [sq_abs] using hsq
    have hmarkov := AronowAudit.P005.Wave1.finite_markov
      (m := m n)
      (fun S => wholeW1Star (P n) (m n) S ^ 2)
      (fun _ _ => sq_nonneg _) ((M * r) ^ 2) hthreshold
    have hratio : (C * q) / ((M * r) ^ 2) < ε := by
      have hdenpos : 0 < (M * r) ^ 2 := hthreshold
      have hdenEq : (M * r) ^ 2 = M ^ 2 * q := by
        rw [mul_pow, hrsq]
      rw [hdenEq]
      apply (div_lt_iff₀ (mul_pos (sq_pos_of_pos hM) hqpos)).2
      have hpos : 0 < ε * M ^ 2 - C := sub_pos.mpr hCM
      have := mul_pos hqpos hpos
      nlinarith
    have htail :
        probability (m n) (fun S =>
          |wholeW1Star (P n) (m n) S| > M * Real.sqrt (kappa (P n) * d n / n)) < ε := by
      calc
        _ ≤ probability (m n) (fun S => (M * r) ^ 2 <
          wholeW1Star (P n) (m n) S ^ 2) := htailmono
        _ ≤ expectation (m n) (fun S => wholeW1Star (P n) (m n) S ^ 2) /
          ((M * r) ^ 2) := hmarkov
        _ ≤ (C * q) / ((M * r) ^ 2) := div_le_div_of_nonneg_right hsecond_bound
          (by positivity)
        _ < ε := hratio
    simpa [q, r] using htail

end
end SAP.P005b.WH.W1
