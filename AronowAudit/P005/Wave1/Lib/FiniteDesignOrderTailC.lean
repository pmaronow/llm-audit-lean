import AronowAudit.P005.P005_Formalization

/-! Probability and stochastic-order calculus on P005's varying finite designs. -/

namespace AronowAudit.P005.Wave1

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

theorem finite_markov {n m : ℕ} (F : Finset (Fin n) → ℝ)
    (hF : ∀ S ∈ design n m, 0 ≤ F S) (u : ℝ) (hu : 0 < u) :
    probability m (fun S => u < F S) ≤ expectation m F / u := by
  classical
  have hsum : (((design n m).filter (fun S => u < F S)).card : ℝ) * u ≤
      ∑ S ∈ design n m, F S := by
    calc
      _ = ∑ S ∈ design n m, if u < F S then u else 0 := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro S hS
        by_cases hSu : u < F S
        · simpa only [if_pos hSu] using hSu.le
        · simpa only [if_neg hSu] using hF S hS
  apply (le_div_iff₀ hu).mpr
  change (((((design n m).filter (fun S => u < F S)).card : ℝ) /
    ((design n m).card : ℝ)) * u) ≤
      (∑ S ∈ design n m, F S) / ((design n m).card : ℝ)
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

theorem tailC_probability_nonneg {n m : ℕ} (E : Finset (Fin n) → Prop) :
    0 ≤ probability m E := by
  classical
  unfold probability
  positivity

theorem tailC_probability_union_bound {n m : ℕ}
    (E F G : Finset (Fin n) → Prop)
    (h : ∀ S ∈ design n m, E S → F S ∨ G S) :
    probability m E ≤ probability m F + probability m G := by
  classical
  have hs : (design n m).filter E ⊆
      (design n m).filter F ∪ (design n m).filter G := by
    intro S hS
    obtain ⟨hSd, hSE⟩ := Finset.mem_filter.mp hS
    rcases h S hSd hSE with hF | hG
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hSd, hF⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hSd, hG⟩)
  have hc : ((design n m).filter E).card ≤
      ((design n m).filter F).card + ((design n m).filter G).card :=
    (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hc' : (((design n m).filter E).card : ℝ) ≤
      ((design n m).filter F).card + ((design n m).filter G).card := by
    exact_mod_cast hc
  unfold probability
  rw [← add_div]
  exact div_le_div_of_nonneg_right hc' (Nat.cast_nonneg _)

theorem tailC_probability_mono {n m : ℕ} (E F : Finset (Fin n) → Prop)
    (h : ∀ S ∈ design n m, E S → F S) : probability m E ≤ probability m F := by
  classical
  unfold probability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show (design n m).filter E ⊆
      (design n m).filter F from fun S hS => by
    obtain ⟨hd, he⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨hd, h S hd he⟩)

theorem tailC_order_combine (m : ℕ → ℕ)
    (U V R : (n : ℕ) → Finset (Fin n) → ℝ) (r a b : ℕ → ℝ)
    (hU : stochasticO m U r) (hV : stochasticO m V r)
    (B : ℝ) (hB : 0 < B)
    (htail : ∀ᶠ n in atTop, ∀ S ∈ design n (m n),
      R n S = a n * U n S - b n * V n S ∧ |a n| ≤ B ∧ |b n| ≤ B) :
    stochasticO m R r := by
  classical
  intro ε hε
  obtain ⟨M₁, hM₁, n₁, h₁⟩ := hU (ε/2) (by linarith)
  obtain ⟨M₂, hM₂, n₂, h₂⟩ := hV (ε/2) (by linarith)
  obtain ⟨n₃, h₃⟩ := eventually_atTop.1 htail
  refine ⟨B * (M₁ + M₂), mul_pos hB (add_pos hM₁ hM₂),
    max n₁ (max n₂ n₃), ?_⟩
  intro n hn
  have hn₁ : n₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : n₂ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₃ : n₃ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hp := tailC_probability_union_bound
    (fun S => |R n S| > B * (M₁ + M₂) * r n)
    (fun S => |U n S| > M₁ * r n) (fun S => |V n S| > M₂ * r n) (by
      intro S hS hbad
      obtain ⟨hid, ha, hb⟩ := h₃ n hn₃ S hS
      by_contra hnot
      push Not at hnot
      have hbound : |R n S| ≤ B * (M₁ + M₂) * r n := by
        rw [hid]
        calc
          |a n * U n S - b n * V n S| ≤ |a n * U n S| + |b n * V n S| :=
            abs_sub _ _
          _ = |a n| * |U n S| + |b n| * |V n S| := by rw [abs_mul, abs_mul]
          _ ≤ B * |U n S| + B * |V n S| :=
            add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
              (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
          _ ≤ B * (M₁ * r n) + B * (M₂ * r n) :=
            add_le_add (mul_le_mul_of_nonneg_left hnot.1 hB.le)
              (mul_le_mul_of_nonneg_left hnot.2 hB.le)
          _ = B * (M₁ + M₂) * r n := by ring
      exact (not_lt_of_ge hbound) hbad)
  exact lt_of_le_of_lt hp (by linarith [h₁ n hn₁, h₂ n hn₂])

/-- Finite Chebyshev on the actual complete-randomization support. -/
theorem tailC_finite_chebyshev {n m : ℕ} (F : Finset (Fin n) → ℝ)
    (u : ℝ) (hu : 0 < u) :
    probability m (fun S => u < |F S - expectation m F|) ≤ variance m F / u^2 := by
  calc
    _ ≤ probability m (fun S => u^2 < (F S - expectation m F)^2) := by
      apply tailC_probability_mono
      intro S _ hS
      have hh := (sq_lt_sq₀ hu.le (abs_nonneg (F S - expectation m F))).2 hS
      simpa only [sq_abs] using hh
    _ ≤ _ := finite_markov (m := m) (fun S => (F S - expectation m F)^2)
      (fun _ _ => sq_nonneg _) (u^2) (sq_pos_of_pos hu)

/-- Deterministic domination of rates preserves stochastic order. -/
theorem tailC_order_rate_mono (m : ℕ → ℕ)
    (U : (n : ℕ) → Finset (Fin n) → ℝ) (r q : ℕ → ℝ)
    (hU : stochasticO m U r) (B : ℝ) (hB : 0 < B)
    (hbound : ∀ᶠ n in atTop, r n ≤ B * q n) :
    stochasticO m U q := by
  intro ε hε
  obtain ⟨M, hM, n₀, htail⟩ := hU ε hε
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 hbound
  refine ⟨M * B, mul_pos hM hB, max n₀ n₁, ?_⟩
  intro n hn
  have hnb : r n ≤ B * q n := hn₁ n ((le_max_right _ _).trans hn)
  have hthreshold : M * r n ≤ (M * B) * q n := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hnb hM.le
  exact lt_of_le_of_lt
    (tailC_probability_mono _ _ (fun S _ hS => lt_of_le_of_lt hthreshold hS))
    (htail n ((le_max_left _ _).trans hn))

/-- Products of tight processes on the changing finite sample spaces. -/
theorem order_product (m : ℕ → ℕ)
    (U V : (n : ℕ) → Finset (Fin n) → ℝ) (r q : ℕ → ℝ)
    (hU : stochasticO m U r) (hV : stochasticO m V q)
    (hr : ∀ᶠ n in atTop, 0 ≤ r n)
    (hq : ∀ᶠ n in atTop, 0 ≤ q n) :
    stochasticO m (fun n S => U n S * V n S) (fun n => r n * q n) := by
  classical
  intro ε hε
  obtain ⟨M₁, hM₁, n₁, h₁⟩ := hU (ε/2) (by linarith)
  obtain ⟨M₂, hM₂, n₂, h₂⟩ := hV (ε/2) (by linarith)
  obtain ⟨n₃, h₃⟩ := eventually_atTop.1 (hr.and hq)
  refine ⟨M₁ * M₂, mul_pos hM₁ hM₂, max n₁ (max n₂ n₃), ?_⟩
  intro n hn
  have hn₁ : n₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : n₂ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₃ : n₃ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  obtain ⟨hrn, _hqn⟩ := h₃ n hn₃
  have hp := tailC_probability_union_bound (m := m n)
    (fun S => |U n S * V n S| > (M₁ * M₂) * (r n * q n))
    (fun S => |U n S| > M₁ * r n) (fun S => |V n S| > M₂ * q n) (by
      intro S _ hbad
      by_contra hnot
      push Not at hnot
      have hbound : |U n S * V n S| ≤ (M₁ * M₂) * (r n * q n) := by
        rw [abs_mul]
        calc
          _ ≤ (M₁ * r n) * (M₂ * q n) :=
            mul_le_mul hnot.1 hnot.2 (abs_nonneg _) (mul_nonneg hM₁.le hrn)
          _ = _ := by ring
      exact (not_lt_of_ge hbound) hbad)
  exact lt_of_le_of_lt hp (by linarith [h₁ n hn₁, h₂ n hn₂])

theorem small_scale_littleO (m : ℕ → ℕ)
    (R : (n : ℕ) → Finset (Fin n) → ℝ) (κ : ℕ → ℝ)
    (hR : stochasticO m R (fun n => Real.sqrt (κ n/n)))
    (hκpos : ∀ᶠ n in atTop, 0 ≤ κ n)
    (hκ : Tendsto κ atTop (nhds 0)) :
    stochasticLittleO m R (fun n => Real.sqrt (1/(n : ℝ))) := by
  classical
  intro δ hδ
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n =>
      lt_of_lt_of_le ha (tailC_probability_nonneg _))
  · intro ε hε
    obtain ⟨M, hM, n₀, hMtail⟩ := hR ε hε
    have hsqrt : Tendsto (fun n => Real.sqrt (κ n)) atTop (nhds 0) := by
      simpa only [Real.sqrt_zero] using hκ.sqrt
    have hsmall : ∀ᶠ n in atTop, Real.sqrt (κ n) < δ/M :=
      (tendsto_order.1 hsqrt).2 _ (div_pos hδ hM)
    filter_upwards [hsmall, hκpos, eventually_ge_atTop n₀] with n hnsmall hnκ hn₀
    have hprod : M * Real.sqrt (κ n) ≤ δ := by
      have hh := (lt_div_iff₀ hM).1 hnsmall
      nlinarith
    have hrate : Real.sqrt (κ n/n) =
        Real.sqrt (κ n) * Real.sqrt (1/(n : ℝ)) := by
      rw [← Real.sqrt_mul hnκ]
      congr 1
      ring
    have hthreshold : M * Real.sqrt (κ n/n) ≤ δ * Real.sqrt (1/(n : ℝ)) := by
      rw [hrate, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hprod (Real.sqrt_nonneg _)
    exact lt_of_le_of_lt
      (tailC_probability_mono _ _ (fun S _ hS => lt_of_le_of_lt hthreshold hS))
      (hMtail n hn₀)

end
end AronowAudit.P005.Wave1
