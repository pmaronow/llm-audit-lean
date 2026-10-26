import Mathlib

namespace AronowAudit.P039

set_option autoImplicit false

open scoped BigOperators

/-- Quarterly RDI growth, numbered 1 through 16. The paper says that growth from
"every quarter of a presidential term" enters, p. 128 (PDF p. 3). Only those
sixteen coordinates of this function are used; all other coordinates are ignored. -/
abbrev QuarterGrowth := ℕ → ℝ

/-- The implemented weighted numerator. The paper assigns quarter 16 weight
"1/3 * λ^0", quarter 15 "λ^1", and quarter 14 "λ^2", p. 128.
The correction to p. 136 and Table 2 restricts the earlier quarters to 2--15.
The normalization and exclusion of Q1 come from the deposited scripts, T1. -/
noncomputable def incomeNumerator (decay : ℝ) (h : QuarterGrowth) : ℝ :=
  (1 / 3 : ℝ) * h 16 + ∑ k ∈ Finset.range 14, decay ^ (k + 1) * h (15 - k)

/-- Implemented normalization, `1/3 + λ + ... + λ^14`, deposited scripts as
transcribed in target T1; this denominator is not printed in the paper. -/
noncomputable def incomeDenominator (decay : ℝ) : ℝ :=
  (1 / 3 : ℝ) + ∑ k ∈ Finset.range 14, decay ^ (k + 1)

/-- Corrected predictor "uses quarters 2--16 ... quarter 1 is excluded", T2's
correction to pp. 128, 136 and Table 2: the normalized weighted numerator. -/
noncomputable def incomeGrowth (decay : ℝ) (h : QuarterGrowth) : ℝ :=
  incomeNumerator decay h / incomeDenominator decay

/-- All-sixteen-quarter numerator of the printed "quarters 1--16" description
(p. 136, Table 2), continuing p. 128's weights through exponent 15, note 5. -/
noncomputable def describedNumerator (decay : ℝ) (h : QuarterGrowth) : ℝ :=
  (1 / 3 : ℝ) * h 16 + ∑ k ∈ Finset.range 15, decay ^ (k + 1) * h (15 - k)

/-- Normalization of the all-sixteen-quarter description,
extending the script's denominator by λ^15; not a printed formula (T1). -/
noncomputable def describedDenominator (decay : ℝ) : ℝ :=
  (1 / 3 : ℝ) + ∑ k ∈ Finset.range 15, decay ^ (k + 1)

/-- Normalized all-sixteen-quarter variable of T1; the printed description
fixes the numerator's weights, whereas the denominator extends the script's denominator by λ^15. -/
noncomputable def describedGrowth (decay : ℝ) (h : QuarterGrowth) : ℝ :=
  describedNumerator decay h / describedDenominator decay

/-- T1(ii), T2(ii): the missing first-quarter term is exactly λ^15 h₁. -/
theorem missing_quarter_numerator (decay : ℝ) (h : QuarterGrowth) :
    describedNumerator decay h = incomeNumerator decay h + decay ^ 15 * h 1 := by
  unfold describedNumerator incomeNumerator
  rw [Finset.sum_range_succ]
  norm_num
  ring

/-- T1(ii), T2(ii): adding Q1 also adds exactly λ^15 to the normalization. -/
theorem missing_quarter_denominator (decay : ℝ) :
    describedDenominator decay = incomeDenominator decay + decay ^ 15 := by
  unfold describedDenominator incomeDenominator
  rw [Finset.sum_range_succ]
  norm_num
  ring

/-- T1(i), T2(i): the implemented numerator and normalized predictor are
unchanged whenever growth in quarters 2--16 is unchanged. -/
theorem income_ignores_quarter_one (decay : ℝ) (h h' : QuarterGrowth)
    (heq : ∀ q, 2 ≤ q → q ≤ 16 → h q = h' q) :
    incomeNumerator decay h = incomeNumerator decay h' ∧ incomeGrowth decay h = incomeGrowth decay h' := by
  have hn : incomeNumerator decay h = incomeNumerator decay h' := by
    unfold incomeNumerator
    rw [heq 16 (by omega) (by omega)]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [heq (15 - k) (by have := Finset.mem_range.mp hk; omega) (by omega)]
  exact ⟨hn, by unfold incomeGrowth; rw [hn]⟩

/-- T2(i): for every nonnegative decay, the denominator is at least 1/3
and is strictly positive. No upper bound of 1 on λ is needed. -/
theorem income_denominators_positive (decay : ℝ) (hdecay : 0 ≤ decay) :
    (1 / 3 : ℝ) ≤ incomeDenominator decay ∧ 0 < incomeDenominator decay ∧
    0 < describedDenominator decay := by
  have hs : 0 ≤ ∑ k ∈ Finset.range 14, decay ^ (k + 1) :=
    Finset.sum_nonneg (fun k _ => pow_nonneg hdecay _)
  have hd : (1 / 3 : ℝ) ≤ incomeDenominator decay := by
    unfold incomeDenominator
    linarith
  have hp : 0 < incomeDenominator decay := by linarith
  refine ⟨hd, hp, ?_⟩
  rw [missing_quarter_denominator]
  exact add_pos_of_pos_of_nonneg hp (pow_nonneg hdecay _)

/-- T2(ii): exact difference between the sixteen-quarter description and
the corrected fifteen-quarter predictor, for every h and λ ≥ 0. -/
theorem income_growth_difference (decay : ℝ) (h : QuarterGrowth) (hdecay : 0 ≤ decay) :
    describedGrowth decay h - incomeGrowth decay h =
      decay ^ 15 * (h 1 - incomeGrowth decay h) / describedDenominator decay := by
  obtain ⟨_, hd, he⟩ := income_denominators_positive decay hdecay
  unfold describedGrowth incomeGrowth
  rw [missing_quarter_numerator, missing_quarter_denominator] at *
  field_simp
  <;> nlinarith

/-- T2(ii): the two normalized variables agree exactly when λ = 0 or
first-quarter growth equals the implemented predictor. -/
theorem income_growth_equality_iff (decay : ℝ) (h : QuarterGrowth) (hdecay : 0 ≤ decay) :
    describedGrowth decay h = incomeGrowth decay h ↔ decay = 0 ∨ h 1 = incomeGrowth decay h := by
  rw [← sub_eq_zero, income_growth_difference decay h hdecay,
    div_eq_zero_iff]
  have hd := (income_denominators_positive decay hdecay).2.2.ne'
  simp only [hd, or_false, mul_eq_zero, pow_eq_zero_iff (by decide : 15 ≠ 0),
    sub_eq_zero]

/-- T2(iii), corrected note 5: at zero decay the predictor is the election
quarter alone; at unit decay Q16 retains its factor 1/3 and Q2--15 have weight 1.
The earlier-quarter sum is indexed in reverse chronological order. -/
theorem income_endpoint_values (h : QuarterGrowth) :
    incomeDenominator 0 = (1 / 3 : ℝ) ∧ incomeGrowth 0 h = h 16 ∧
    incomeDenominator 1 = (43 / 3 : ℝ) ∧
    incomeGrowth 1 h = (3 / 43 : ℝ) *
      ((1 / 3 : ℝ) * h 16 + ∑ k ∈ Finset.range 14, h (15 - k)) ∧
    (0 : ℝ) ^ 0 = 1 ∧ (∀ k : ℕ, (1 : ℝ) ^ k = 1) ∧
    (∀ k : ℕ, 1 ≤ k → (0 : ℝ) ^ k = 0) := by
  norm_num [incomeDenominator, incomeGrowth, incomeNumerator]
  constructor
  · ring
  · intro k hk
    omega

/-- The exact witness of T1(iii),(iv): h₁=1 and h₂=...=h₁₆=0. This is
a synthetic construction, not election-level data printed in the paper. -/
noncomputable def firstQuarterOnly : QuarterGrowth := fun q => if q = 1 then 1 else 0

/-- T1(iii): λ=1/2 is admissible and yields zero for the implemented variable,
but the described numerator is 1/32768 and normalized value is 3/131069 > 0. -/
theorem income_counterexample_half :
    0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 ∧
    firstQuarterOnly 1 = 1 ∧ (∀ q, 2 ≤ q → q ≤ 16 → firstQuarterOnly q = 0) ∧
    incomeNumerator (1 / 2) firstQuarterOnly = 0 ∧
    incomeGrowth (1 / 2) firstQuarterOnly = 0 ∧
    describedNumerator (1 / 2) firstQuarterOnly = (1 / 32768 : ℝ) ∧
    describedDenominator (1 / 2) = (131069 / 98304 : ℝ) ∧
    describedGrowth (1 / 2) firstQuarterOnly = (3 / 131069 : ℝ) ∧
    0 < describedGrowth (1 / 2) firstQuarterOnly ∧
    describedGrowth (1 / 2) firstQuarterOnly ≠ incomeGrowth (1 / 2) firstQuarterOnly := by
  norm_num [firstQuarterOnly, incomeGrowth, describedGrowth, incomeNumerator,
    describedNumerator, incomeDenominator, describedDenominator, Finset.sum_range_succ]
  intro q hq _
  simp [show q ≠ 1 by omega]

/-- T1(iv): the same exact witness at λ=0.9 has the stated large rational
numerator, denominator and strictly positive normalized value. -/
theorem income_counterexample_nine_tenths :
    0 < (9 / 10 : ℝ) ∧ (9 / 10 : ℝ) < 1 ∧
    incomeNumerator (9 / 10) firstQuarterOnly = 0 ∧
    incomeGrowth (9 / 10) firstQuarterOnly = 0 ∧
    describedNumerator (9 / 10) firstQuarterOnly = (205891132094649 / 10 ^ 15 : ℝ) ∧
    describedDenominator (9 / 10) = (22440939433444477 / (3 * 10 ^ 15) : ℝ) ∧
    describedGrowth (9 / 10) firstQuarterOnly = (617673396283947 / 22440939433444477 : ℝ) ∧
    0 < describedGrowth (9 / 10) firstQuarterOnly ∧
    describedGrowth (9 / 10) firstQuarterOnly ≠ incomeGrowth (9 / 10) firstQuarterOnly := by
  norm_num [firstQuarterOnly, incomeGrowth, describedGrowth, incomeNumerator,
    describedNumerator, incomeDenominator, describedDenominator, Finset.sum_range_succ]

end AronowAudit.P039

