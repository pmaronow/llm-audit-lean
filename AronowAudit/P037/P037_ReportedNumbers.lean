import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp

/-!
Exact arithmetic for P037-T3, T6, T12, T13. Empirical inputs are printed
estimates, not assertions about the true treatment effect. Fractions use
composition units 0.20 = 20%. No numerical assertion about the normal integral
is assumed: T3 explicitly quantifies over a critical value in [1.9, 2].
-/
namespace AronowAudit.P037
set_option autoImplicit false

/-- Main p. 568: “P values using robust SEs under a normal approximation”.
Under a one-coefficient, two-sided Wald interpretation, the statistic is
the absolute estimate / SE. -/
noncomputable def waldRatio (estimate se : ℝ) : ℝ := |estimate| / se

/-- SI Table S6 p. 41 prints -0.06 (0.03). Strict interior rounding bins
avoid any convention for a tie at half a hundredth. -/
def printsTableS6 (estimate se : ℝ) : Prop :=
  estimate < 0 ∧ 11/200 < |estimate| ∧ |estimate| < 13/200 ∧
  1/40 < se ∧ se < 7/200

/-- P037-T3(i): the main p. 569 significance sentence and the 2018
Correction p. E3598 nonsignificance sentence cannot describe one P value. -/
theorem significance_claims_incompatible (p : ℝ) :
    ¬ (p < 1/20 ∧ 1/20 ≤ p) := by
  exact not_lt_of_ge (show (1:ℝ)/20 ≤ 1/20 from le_rfl) ∘
    (fun h => lt_of_le_of_lt h.2 h.1)

/-- P037-T3(ii)--(iv): two exact estimates and SEs print identically,
yet give opposite rejection decisions for every critical value in [1.9,2].
Membership of the actual normal quantile in that interval is an explicit
premise, not a proved normal-integral calculation. -/
theorem rounded_wald_opposite_decisions (c : ℝ)
    (hc : 19/10 ≤ c ∧ c ≤ 2) :
    printsTableS6 (-57/1000) (7/250) ∧
    printsTableS6 (-57/1000) (17/500) ∧
    waldRatio (-57/1000) (7/250) = 57/28 ∧
    waldRatio (-57/1000) (17/500) = 57/34 ∧
    waldRatio (-57/1000) (17/500) < c ∧
    c < waldRatio (-57/1000) (7/250) := by
  norm_num [printsTableS6, waldRatio]
  constructor <;> linarith [hc.1, hc.2]

/-- P037-T3(v): every statistic in the rounding bins lies in (11/7,13/5).
The quotient of the displayed decimals is exactly 2. -/
theorem wald_rounding_envelope (estimate se : ℝ)
    (h : printsTableS6 estimate se) :
    11/7 < waldRatio estimate se ∧ waldRatio estimate se < 13/5 ∧
    (6/100:ℝ)/(3/100) = 2 := by
  rcases h with ⟨_, h1, h2, h3, h4⟩
  have hs : 0 < se := by linarith
  constructor
  · rw [waldRatio, lt_div_iff₀ hs]
    nlinarith
  constructor
  · rw [waldRatio, div_lt_iff₀ hs]
    nlinarith
  · norm_num

/-- P037-T3(v): the open interval (11/7,13/5) is the exact attainable
range, not merely an outer bound. Here `a` is the absolute estimate. -/
theorem wald_envelope_attainable (z : ℝ) (hz : 11/7 < z ∧ z < 13/5) :
    ∃ a se : ℝ, 11/200 < a ∧ a < 13/200 ∧
      1/40 < se ∧ se < 7/200 ∧ a / se = z := by
  have hz0 : 0 < z := by linarith
  let lo := max (1/40:ℝ) ((11/200)/z)
  let hi := min (7/200:ℝ) ((13/200)/z)
  have hcross1 : (1/40:ℝ) < (13/200)/z := by
    rw [lt_div_iff₀ hz0]; linarith [hz.2]
  have hcross2 : (11/200:ℝ)/z < 7/200 := by
    rw [div_lt_iff₀ hz0]; linarith [hz.1]
  have hcross3 : (11/200:ℝ)/z < (13/200)/z := by
    exact div_lt_div_of_pos_right (by norm_num) hz0
  have hlohi : lo < hi := by
    exact max_lt (lt_min (by norm_num) hcross1) (lt_min hcross2 hcross3)
  let se := (lo + hi)/2
  have hlose : lo < se := by dsimp [se]; linarith
  have hsehi : se < hi := by dsimp [se]; linarith
  have hs1 : (1/40:ℝ) < se := lt_of_le_of_lt (le_max_left _ _) hlose
  have hs2 : se < (7/200:ℝ) := lt_of_lt_of_le hsehi (min_le_left _ _)
  have hs3 : (11/200:ℝ)/z < se := lt_of_le_of_lt (le_max_right _ _) hlose
  have hs4 : se < (13/200:ℝ)/z := lt_of_lt_of_le hsehi (min_le_right _ _)
  have hse0 : 0 < se := by linarith
  refine ⟨z*se, se, ?_, ?_, hs1, hs2, ?_⟩
  · have := (div_lt_iff₀ hz0).mp hs3; nlinarith
  · have := (lt_div_iff₀ hz0).mp hs4; nlinarith
  · field_simp

/-- Main p. 571: "from 2,695 events to 2,012 events across the 11,938
students". Relative reduction on one common adjustment basis is
(control - treated) / control. -/
noncomputable def relativeReduction (control treated : ℝ) : ℝ :=
  (control - treated) / control

/-- P037-T6(i),(ii),(iv),(vi): the published totals imply a reduction
rounding to 25%, a per-student decrease rounding to 0.06, and a control
level above 0.225; they do not imply a 30% relative decrease. -/
theorem corrected_reduction_arithmetic :
    (2695:ℕ)-2012 = 683 ∧
    relativeReduction 2695 2012 = 683/2695 ∧
    (49/200:ℝ) < 683/2695 ∧ (683/2695:ℝ) < 51/200 ∧
    (683/2695:ℝ) < 59/200 ∧ (683/2695:ℝ) ≠ 3/10 ∧
    (6830:ℕ) ≠ 8085 ∧
    (11/200:ℝ) ≤ 683/11938 ∧ (683/11938:ℝ) < 13/200 ∧
    (9/40:ℝ) < 2695/11938 ∧ (2695/11938:ℝ) < 23/100 ∧
    (3/10:ℝ)-1/4 = 1/20 ∧ (1/20:ℝ)/(3/10) = 1/6 := by
  norm_num [relativeReduction]

/-- P037-T6(iii): even allowing half-unit rounding of both estimated
event totals keeps the relative reduction strictly inside the 25% bin. -/
theorem rounded_totals_reduction (A B : ℝ)
    (ha : 5389/2 ≤ A ∧ A ≤ 5391/2)
    (hb : 4023/2 ≤ B ∧ B ≤ 4025/2) :
    1364/5389 ≤ 1-B/A ∧ 1-B/A ≤ 1368/5391 ∧
    (49/200:ℝ) < 1364/5389 ∧ (1368/5391:ℝ) < 51/200 := by
  have hA : 0 < A := by linarith [ha.1]
  have hl : B/A ≤ (4025:ℝ)/5389 := by
    rw [div_le_iff₀ hA]; nlinarith [ha.1, hb.2]
  have hu : (4023:ℝ)/5391 ≤ B/A := by
    rw [le_div_iff₀ hA]; nlinarith [ha.2, hb.1]
  constructor
  · linarith
  constructor
  · linarith
  · norm_num

/-- P037-T6(v): the original 30% is the exact ratio of rounded numbers.
Even the full rounding bins for those numbers cannot give 25% to a
whole percent; the correction uses another (adjusted) denominator. -/
theorem mixed_basis_cannot_round_to_25 (e m : ℝ)
    (he : 11/200 ≤ e ∧ e ≤ 13/200)
    (hm : 39/200 ≤ m ∧ m ≤ 41/200) :
    (3/50:ℝ)/(1/5) = 3/10 ∧ 11/41 ≤ e/m ∧ (51/200:ℝ) < e/m := by
  have hm0 : 0 < m := by linarith [hm.1]
  have hl : (11/41:ℝ) ≤ e/m := by
    rw [le_div_iff₀ hm0]; nlinarith [he.1, hm.2]
  exact ⟨by norm_num, hl, lt_of_lt_of_le (by norm_num) hl⟩

/-- SI p. 6, repaired per P037-T12: "scaled linearly between 40 and 64
seed-eligible students, rounding to the nearest 4". For integer school
size this integer division is exactly floor(10+3(n-200)/175+1/2), times 4.
The constant branches use the correction's explicit endpoints. -/
def seedEligibleCount (n : ℕ) : ℕ :=
  if n ≤ 200 then 40 else if 550 ≤ n then 64 else
    4 * (10 + (6 * (n-200) + 175) / 350)

/-- P037-T12(i): the interior interpolation never lands on a rounding
tie for integer sizes. The equality is the half-integer equation after
multiplying by 350; its two sides have opposite parity. -/
theorem seed_interpolation_no_tie (n k : ℤ) :
    350*k ≠ 3500 + 6*(n-200) - 175 := by omega

/-- P037-T12(ii): the repaired rule stays between 40 and 64, is a
multiple of four, and is nondecreasing at every integer school size. -/
theorem seed_count_bounds_monotone :
    (∀ n, 40 ≤ seedEligibleCount n ∧ seedEligibleCount n ≤ 64 ∧
      4 ∣ seedEligibleCount n) ∧
    Monotone seedEligibleCount := by
  constructor
  · intro n
    unfold seedEligibleCount
    split_ifs with h1 h2
    · norm_num
    · norm_num
    · constructor
      · omega
      constructor
      · omega
      · exact dvd_mul_right _ _
  · intro n m hnm
    unfold seedEligibleCount
    split_ifs <;> omega

/-- P037-T12(iii),(iv): the stated cap branch applies from size 550;
rounding already attains 64 from size 521. Exact endpoint predictions
and the three published-rule examples are included. -/
theorem seed_count_cap_and_examples :
    (∀ n, seedEligibleCount n = 64 ↔ 521 ≤ n) ∧
    (∀ n, 550 ≤ n → seedEligibleCount n = 64) ∧
    (40+24*((200:ℝ)-200)/350 = 40) ∧
    (40+24*((550:ℝ)-200)/350 = 64) ∧
    seedEligibleCount 100 = 40 ∧ seedEligibleCount 200 = 40 ∧
    seedEligibleCount 375 = 52 := by
  constructor
  · intro n; unfold seedEligibleCount; split_ifs <;> omega
  constructor
  · intro n hn
    have hn0 : ¬ n ≤ 200 := by omega
    simp [seedEligibleCount, hn0, hn]
  · norm_num [seedEligibleCount]

/-- P037-T12(v): eligible shares under the repaired rule vary with
school size; "designed to represent 15%" is a design aim. -/
theorem seed_count_shares :
    (seedEligibleCount 100:ℝ)/100 = 2/5 ∧
    (seedEligibleCount 200:ℝ)/200 = 1/5 ∧
    (seedEligibleCount 375:ℝ)/375 = 52/375 ∧
    (seedEligibleCount 550:ℝ)/550 = 64/550 ∧
    (seedEligibleCount 715:ℝ)/715 = 64/715 := by
  norm_num [seedEligibleCount]

/-- SI Eqs. (4),(6) and Table S7 p. 42: "the average causal effect of
treatment at a given composition ... is τ₀ + βc". This is the fitted
effect formula; its causal reading needs the restrictions in P037-T2. -/
noncomputable def compositionEffect (intercept slope c : ℝ) : ℝ :=
  intercept + slope*c

/-- P037-T13(i),(iv): Table S7's coefficients give -0.13 at 20%; the
two printed outcome levels 0.20 and 0.08 give a 60% reduction exactly. -/
theorem composition_prediction_printed_arithmetic :
    compositionEffect (4/100) (-85/100) (1/5) = -13/100 ∧
    relativeReduction (1/5) (8/100) = 3/5 := by
  norm_num [compositionEffect, relativeReduction]

/-- P037-T13(ii),(iii),(v): rounding intervals for Table S7 and the
explicit Fig. 2D control-level hypothesis put the prediction in
[0.086,0.099]. Thus it cannot print as 0.08; 0.095 is in the interval.
The relative-reduction interval includes both 57% and 60%. -/
theorem composition_prediction_intervals (t b m : ℝ)
    (ht : 35/1000 ≤ t ∧ t ≤ 45/1000)
    (hb : -855/1000 ≤ b ∧ b ≤ -845/1000)
    (hm : 222/1000 ≤ m ∧ m ≤ 223/1000) :
    -136/1000 ≤ compositionEffect t b (1/5) ∧
    compositionEffect t b (1/5) ≤ -124/1000 ∧
    86/1000 ≤ m + compositionEffect t b (1/5) ∧
    m + compositionEffect t b (1/5) ≤ 99/1000 ∧
    ¬ (75/1000 ≤ m + compositionEffect t b (1/5) ∧
       m + compositionEffect t b (1/5) ≤ 85/1000) ∧
    (86/1000:ℝ) ≤ 95/1000 ∧ (95/1000:ℝ) ≤ 99/1000 ∧
    124/223 ≤ -compositionEffect t b (1/5)/m ∧
    -compositionEffect t b (1/5)/m ≤ 68/111 ∧
    (124/223:ℝ) ≤ 57/100 ∧ (57/100:ℝ) ≤ 68/111 ∧
    (124/223:ℝ) ≤ 3/5 ∧ (3/5:ℝ) ≤ 68/111 := by
  have hl : -136/1000 ≤ compositionEffect t b (1/5) := by
    dsimp [compositionEffect]; linarith [ht.1, hb.1]
  have hu : compositionEffect t b (1/5) ≤ -124/1000 := by
    dsimp [compositionEffect]; linarith [ht.2, hb.2]
  have hp : 86/1000 ≤ m + compositionEffect t b (1/5) := by linarith [hm.1]
  have hpu : m + compositionEffect t b (1/5) ≤ 99/1000 := by linarith [hm.2]
  have hm0 : 0 < m := by linarith [hm.1]
  refine ⟨hl, hu, hp, hpu, ?_, by norm_num, by norm_num, ?_, ?_, by norm_num⟩
  · rintro ⟨_, h⟩; linarith
  · rw [le_div_iff₀ hm0]; nlinarith [hm.2]
  · rw [div_le_iff₀ hm0]; nlinarith [hm.1]

end AronowAudit.P037

