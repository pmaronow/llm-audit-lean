import SAP.P039.Defs.WholeW1
import SAP.P039.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.WH.W1
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory

theorem witness_tail_comparisons : WitnessTailComparisons := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)
  have hp := Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num)
  have hb : 247 * Real.sqrt (13 : ℝ) < 900 := by
    by_contra h
    have hh : (900 / 247 : ℝ) ≤ Real.sqrt 13 := by linarith
    have hh' := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 900 / 247) hp.le).2 hh
    nlinarith
  have hq : (3 * Real.sqrt (3 : ℝ) / 2) / Real.sqrt 3 = 3 / 2 := by
    field_simp
  have ha : Real.arctan (3 / 2 : ℝ) = Real.pi / 4 + Real.arctan (1 / 5) := by
    have h := Real.arctan_add (x := (1 : ℝ)) (y := (1 / 5 : ℝ)) (by norm_num)
    norm_num [Real.arctan_one] at h
    exact h.symm
  have ht := Real.arctan_lt_self (show (0 : ℝ) < 1 / 5 by norm_num)
  have hc : 2 / Real.pi < (2 / 3 : ℝ) := by
    apply (div_lt_div_iff₀ Real.pi_pos (by norm_num)).2
    nlinarith [Real.pi_gt_three]
  have hm : 2 / Real.pi * (Real.arctan (1 / 5) + 6 / 13) <
      (2 / 3 : ℝ) * (1 / 5 + 6 / 13) := by
    calc
      _ ≤ 2 / Real.pi * ((1 / 5 : ℝ) + 6 / 13) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ < _ := mul_lt_mul_of_pos_right hc (by norm_num)
  refine ⟨by norm_num, by norm_num, by norm_num, hb, hq, ha, ht,
    Real.pi_gt_three, by norm_num, ?_, by norm_num⟩
  rw [show studentThreeTail (3 * Real.sqrt 3 / 2) =
    1 / 2 - 2 / Real.pi * (Real.arctan (1 / 5) + 6 / 13) from
      AronowAudit.P039.residual_test_five_percent_disagreement.2.2.1]
  linarith

/-- Rational certificates for the decimal enclosures; the only transcendental
input still needed is a fifth-order alternating bound for arctan at one fifth. -/
theorem witness_tail_decimals
    (ha : (1 / 5 : ℝ) - (1 / 5 : ℝ) ^ 3 / 3 ≤ Real.arctan (1 / 5))
    (hb : Real.arctan (1 / 5 : ℝ) ≤
      (1 / 5 : ℝ) - (1 / 5 : ℝ) ^ 3 / 3 + (1 / 5 : ℝ) ^ 5 / 5) :
    (0.03985 : ℝ) ≤ studentFourTail 3 ∧ studentFourTail 3 < 0.03995 ∧
    (0.08045 : ℝ) ≤ studentThreeTail (3 * Real.sqrt 3 / 2) ∧
    studentThreeTail (3 * Real.sqrt 3 / 2) < 0.08055 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)
  have hp := Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num)
  have hlo : (3.60555 : ℝ) ≤ Real.sqrt 13 := by nlinarith
  have hhi : Real.sqrt (13 : ℝ) < 3.60556 := by nlinarith
  have hfour := AronowAudit.P039.residual_test_five_percent_disagreement.1
  have hthree := AronowAudit.P039.residual_test_five_percent_disagreement.2.2.1
  change studentFourTail 3 = _ at hfour
  change studentThreeTail _ = _ at hthree
  rw [hfour, hthree]
  have hlo' : 45 / (13 * Real.sqrt 13) ≤ (1 - 0.03985 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have hhi' : (1 - 0.03995 : ℝ) < 45 / (13 * Real.sqrt 13) := by
    apply (lt_div_iff₀ (by positivity)).2
    nlinarith
  have hπlo := Real.pi_gt_d6
  have hπhi := Real.pi_lt_d6
  have hangle : 0 ≤ Real.arctan (1 / 5 : ℝ) + 6 / 13 := by linarith
  have hpl : 2 * (Real.arctan (1 / 5) + 6 / 13) / Real.pi ≤
      (1 / 2 - 0.08045 : ℝ) := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith
  have hpu : (1 / 2 - 0.08055 : ℝ) <
      2 * (Real.arctan (1 / 5) + 6 / 13) / Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).2
    nlinarith
  refine ⟨by linarith, by linarith, ?_, ?_⟩ <;>
    rw [div_mul_eq_mul_div] <;> linarith

theorem rmsq_ratio (S₁ S₂ : ℝ) (h₁ : 0 < S₁) (h₂ : 0 < S₂) :
    Real.sqrt (S₁ / 14) / Real.sqrt (S₂ / 13) =
      Real.sqrt (13 / 14 : ℝ) * (Real.sqrt (S₁ / 17) / Real.sqrt (S₂ / 17)) := by
  rw [← Real.sqrt_div (by positivity), ← Real.sqrt_div (by positivity),
    ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

theorem alternative_rmsq : AlternativeRMSQStatement := by
  have hp : 0 < Real.sqrt (13 / 14 : ℝ) := by positivity
  have hu : Real.sqrt (13 / 14 : ℝ) < 1 := by
    apply (Real.sqrt_lt' (by norm_num)).2
    norm_num
  have hsm : (7141 / 7512 : ℝ) * Real.sqrt (13 / 14 : ℝ) < 7141 / 7512 := by
    nlinarith
  refine ⟨hp, hu, hsm, ?_⟩
  intro Z₁ Z₂ q y hspan h₁ h₂
  dsimp only
  have hn := Bridge.nested_geometry Z₁ Z₂ q hspan h₁ h₂ (by decide) (by decide)
  dsimp only at hn
  obtain ⟨_, _, _, _, _, _, _, hout⟩ := hn
  have hpos : ∀ {p : ℕ} (A : Matrix (Fin 17) (Fin p) ℝ),
      (0 : ℝ) < wholeRMSQ A y → 0 < olsSSE A y := by
    intro p A h
    have h' := Real.sqrt_pos.mp h
    linarith
  have hbound (hs₁ : 0 < olsSSE (fullDesign Z₁ q) y)
      (hs₂ : 0 < olsSSE (fullDesign Z₂ q) y) :
      olsResidualStandardError (fullDesign Z₁ q) y /
          olsResidualStandardError (fullDesign Z₂ q) y =
        Real.sqrt (13 / 14 : ℝ) *
          (wholeRMSQ (fullDesign Z₁ q) y / wholeRMSQ (fullDesign Z₂ q) y) ∧
      (Real.sqrt (olsSESquared (fullDesign Z₂ q) y 3) ≤ 0.965 →
        wholeRMSQ (fullDesign Z₁ q) y ≤ 4.625 →
        4.695 ≤ wholeRMSQ (fullDesign Z₂ q) y →
        Real.sqrt (olsSESquared (fullDesign Z₁ q) y 2) ≤
          (7141 / 7512 : ℝ) * Real.sqrt (13 / 14 : ℝ)) := by
    have hr : olsResidualStandardError (fullDesign Z₁ q) y /
        olsResidualStandardError (fullDesign Z₂ q) y =
        Real.sqrt (13 / 14 : ℝ) *
          (wholeRMSQ (fullDesign Z₁ q) y / wholeRMSQ (fullDesign Z₂ q) y) := by
      unfold olsResidualStandardError wholeRMSQ
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      exact rmsq_ratio _ _ hs₁ hs₂
    refine ⟨hr, ?_⟩
    intro hse₂ hm₁ hm₂
    have hh : Real.sqrt (olsSESquared (fullDesign Z₁ q) y 2) ≤
        Real.sqrt (olsSESquared (fullDesign Z₂ q) y 3) *
          (olsResidualStandardError (fullDesign Z₁ q) y /
            olsResidualStandardError (fullDesign Z₂ q) y) := by
      convert (hout y hs₁ hs₂).2.2.2 using 1 <;>
        norm_num [olsResidualStandardError] <;> ring
    have hh' : Real.sqrt (olsSESquared (fullDesign Z₁ q) y 2) ≤
        (Real.sqrt (olsSESquared (fullDesign Z₂ q) y 3) *
          wholeRMSQ (fullDesign Z₁ q) y / wholeRMSQ (fullDesign Z₂ q) y) *
            Real.sqrt (13 / 14 : ℝ) := by
      rw [hr] at hh
      convert hh using 1
      ring
    have ha := Bridge.rounded_bound
      (Real.sqrt (olsSESquared (fullDesign Z₂ q) y 3) *
        wholeRMSQ (fullDesign Z₁ q) y / wholeRMSQ (fullDesign Z₂ q) y)
      _ _ _ hse₂ (Real.sqrt_nonneg _) hm₁ hm₂ (le_refl _)
    exact hh'.trans (mul_le_mul_of_nonneg_right ha hp.le)
  refine ⟨hbound, ?_⟩
  intro hse₁ hse₂ hm₁ hm₂
  have hs₁ := hpos _ (by linarith [hm₁.1])
  have hs₂ := hpos _ (by linarith [hm₂.1])
  have hh := (hbound hs₁ hs₂).2 hse₂.2 hm₁.2 hm₂.1
  linarith [hse₁.1]

/-- Positivity and a six-sigma lower bound for all three fixed income statistics. -/
theorem table_income_statistics :
    6 < |olsT tableA1 tableTwoOutcome 1| ∧
    6 < |olsT tableA2 tableTwoOutcome 1| ∧
    6 < |olsT tableA3 tableTwoOutcome 1| := by
  have h := Bridge.corrected_table_cells
  obtain ⟨_, _, _, _, ha, _, _, _, _, hsa, hsa', _, hb, _, hsb, hsb',
    _, hc, _, _, _, hsc, hsc'⟩ := h
  have scalar (b s : ℝ) (hb : 6.365 ≤ b) (hs : 0 < s) (hsu : s < 1.015) :
      6 < |b / s| := by
    have ht : 6 < b / s := (lt_div_iff₀ hs).2 (by linarith)
    exact ht.trans_le (le_abs_self _)
  unfold olsT
  exact ⟨scalar _ _ (by linarith) (by linarith) (by linarith),
    scalar _ _ hb (by linarith) (by linarith),
    scalar _ _ (by linarith) (by linarith) hsc'⟩

/-- Fourth-moment Markov at six, applied directly to the actual Student measure.
The finite upper bound also certifies that the probability's toReal is legitimate. -/
theorem student_six_tail (ν : ℕ) (t : ℝ)
    (hi : Integrable (fun s : ℝ => s ^ 4) (studentLaw ν)) (ht : 6 ≤ t) :
    studentTailProbability ν t ≤ (∫ s : ℝ, s ^ 4 ∂studentLaw ν) / 6 ^ 4 := by
  have hh := (hi.div_const ((6 : ℝ) ^ 4)).measure_le_integral
    (ae_of_all _ (fun s : ℝ => by positivity))
    (s := {s : ℝ | t ≤ |s|}) (by
      intro s hs
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) (ht.trans hs) 4
      have hp' : (6 : ℝ) ^ 4 ≤ s ^ 4 := by
        simpa only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs] using hp
      exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 6 ^ 4)).2 (by simpa using hp'))
  have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun s : ℝ => by positivity)), integral_div] at hh'
  exact hh'

/-- The full fit cannot have larger SSE than the line fitted to first-stage residuals. -/
theorem residual_sse_bound {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ)
    (x y : Fin n → ℝ) (hZ : FullColumnRank Z)
    (h1 : ∃ c, Z *ᵥ c = fun _ => 1) (hx : ¬ ∃ c, Z *ᵥ c = x) (hn : k + 1 < n) :
    olsSSE (fullDesign Z x) y ≤ olsSSE (residualLine x) (residualMaker Z *ᵥ y) := by
  have h := Bridge.T4_correspondence.1 Z x y hZ h1 hx hn
  dsimp only [LinearResidualConclusion] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsr, _, _, hsf,
    _, _, _, _, _, hle, _⟩ := h
  rw [hsr, hsf]
  exact hle

theorem scaled_student_ne {n k : ℕ} (hn : k + 1 < n) (hk : 2 ≤ k) :
    (studentLaw (n - k - 1)).map
      (fun t => Real.sqrt (((n : ℝ) - 2) / ((n : ℝ) - k - 1)) * t) ≠ studentLaw (n - 2) := by
  have hν : 0 < n - k - 1 := by omega
  have hlt : n - k - 1 < n - 2 := by omega
  have hc : ((n - k - 1 : ℕ) : ℝ) = (n : ℝ) - k - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n - k), Nat.cast_sub (by omega : k ≤ n)]
    norm_num
  have hc' : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  have h := AronowAudit.P039.StudentCompletion.scaled_ratioLaw_ne hν hlt
  change (studentLaw (n - k - 1)).map
    (fun t => Real.sqrt (((n - 2 : ℕ) : ℝ) / ((n - k - 1 : ℕ) : ℝ)) * t) ≠ _ at h
  rwa [hc, hc'] at h

end SAP.P039.WH.W1
