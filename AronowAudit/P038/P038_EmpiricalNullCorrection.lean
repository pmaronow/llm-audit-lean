import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
P038: Zhang and Aronow (2016), *Driving fatalities on US presidential election
days: a reanalysis*, target P038-T1, parts (i)--(iv).

The result below is conditional on the tail counts read from the published
figure. It does not certify those pixel readings or the unavailable FARS data.
All decimal values are represented by exact rational expressions in ℝ.
The reference RR function is unrestricted outside the window being considered.
-/

namespace AronowAudit.P038


/-- Reference Tuesdays: Methods, PDF p. 2, "the 100 Tuesdays before and after"
and "these 200 RRs"; footnote 2, PDF p. 3, "the surrounding 12, 25 and 50
Tuesdays". The footnote windows use the same number on each side. Integer week
zero is excluded, so this is exactly W_m = {w : 1 ≤ |w| ≤ m}. -/
def referenceWeeks (m : ℕ) : Finset ℤ :=
  (Finset.Icc (-(m : ℤ)) (m : ℤ)).erase 0

/-- Strictly more extreme according to Fig. 1's caption, PDF p. 2:
"black dashed lines indicate RR and 1/RR for presidential election days" and
"The proportion of red dots outside black dashed lines is equivalent to the
reported non-parametric P value". This uses the smaller and larger threshold
even when the election-day RR is below one. Boundary ties are excluded. -/
def moreExtreme (electionRR referenceRR : ℝ) : Prop :=
  referenceRR < min electionRR (1 / electionRR) ∨
    max electionRR (1 / electionRR) < referenceRR

/-- The reference weeks whose RRs lie outside the dashed lines (Fig. 1 caption,
PDF p. 2, "red dots outside black dashed lines"). The RR threshold and the
function of reference RRs stay fixed when the reference window changes. -/
noncomputable def tailWeeks (R : ℝ) (r : ℤ → ℝ) (m : ℕ) : Finset ℤ := by
  classical
  exact (referenceWeeks m).filter (fun w => moreExtreme R (r w))

/-- k_m, the count used in the proportion: Methods, PDF p. 2, "the proportion
of RRs more extreme"; equivalently the number of outside points in Fig. 1. -/
noncomputable def tailCount (R : ℝ) (r : ℤ → ℝ) (m : ℕ) : ℕ :=
  (tailWeeks R r m).card

/-- P_m: Methods, PDF p. 2, "non-parametric two-tailed P values computed as
the proportion of RRs more extreme". There are 2m reference Tuesdays, and
the election-day observation is excluded. All windows considered here have m ≥ 1. -/
noncomputable def empiricalP (R : ℝ) (r : ℤ → ℝ) (m : ℕ) : ℝ :=
  (tailCount R r m : ℝ) / (2 * (m : ℝ))

/-- Two-decimal rounding as explicitly specified in target P038-T1:
v - 1/200 ≤ x < v + 1/200. Footnote 2 (PDF p. 3) prints two-decimal P values
without stating a tie rule. This half-open convention comes from the target;
none of the values considered here lies at a rounding boundary. -/
def roundsTo (x v : ℝ) : Prop := v - 1 / 200 ≤ x ∧ x < v + 1 / 200

/-- The alternative (k_m + 1)/(2m + 1) discussed in P038-N005's derivation,
"Counting the election point as an additional extreme observation". This
is an alternative convention for checking reconciliation, not the paper's
reference-only empirical P value. The paper's rule is `empiricalP`. -/
noncomputable def electionDayAdjustedP (R : ℝ) (r : ℤ → ℝ) (m : ℕ) : ℝ :=
  ((tailCount R r m + 1 : ℕ) : ℝ) / (2 * (m : ℝ) + 1)

/-- Membership in the reference window, spelling out the exclusion of week
zero in Methods (PDF p. 2) and target P038-T1's W_m. -/
theorem mem_referenceWeeks (m : ℕ) (w : ℤ) :
    w ∈ referenceWeeks m ↔ w ≠ 0 ∧ -(m : ℤ) ≤ w ∧ w ≤ (m : ℤ) := by
  simp [referenceWeeks]


/-- Shortening the footnote 2 window only removes reference Tuesdays; it
never changes the election-day threshold or the reference RR statistic. -/
theorem referenceWeeks_mono {m n : ℕ} (h : m ≤ n) :
    referenceWeeks m ⊆ referenceWeeks n := by
  intro w hw
  rw [mem_referenceWeeks] at hw ⊢
  exact ⟨hw.1, by omega, by omega⟩

/-- A tail week belongs to W_m and satisfies the caption's strict outside
rule (Fig. 1, PDF p. 2), rather than an assumed list of tail observations. -/
theorem mem_tailWeeks (R : ℝ) (r : ℤ → ℝ) (m : ℕ) (w : ℤ) :
    w ∈ tailWeeks R r m ↔ w ∈ referenceWeeks m ∧ moreExtreme R (r w) := by
  classical
  simp [tailWeeks]


/-- P038-T1(iii): k_m ≤ k_n whenever m ≤ n. This follows by inclusion of
the reference windows while keeping R and every r_w fixed (footnote 2). -/
theorem tailCount_mono (R : ℝ) (r : ℤ → ℝ) {m n : ℕ} (h : m ≤ n) :
    tailCount R r m ≤ tailCount R r n := by
  classical
  apply Finset.card_le_card
  intro w hw
  rw [mem_tailWeeks] at hw ⊢
  exact ⟨referenceWeeks_mono h hw.1, hw.2⟩

/-- Restricting the same reference RR family to a smaller window restricts
the tail set. This is the finite-set lemma behind P038-T1(iii). -/
theorem tailWeeks_restrict (R : ℝ) (r : ℤ → ℝ) {m n : ℕ} (h : m ≤ n) :
    tailWeeks R r m = (tailWeeks R r n).filter (fun w => w ∈ referenceWeeks m) := by
  classical
  ext w
  simp only [Finset.mem_filter, mem_tailWeeks]
  constructor
  · rintro ⟨hw, he⟩
    exact ⟨⟨referenceWeeks_mono h hw, he⟩, hw⟩
  · rintro ⟨⟨_, he⟩, hw⟩
    exact ⟨hw, he⟩

/-- P038-T1(ii), footnote 2, PDF p. 3: k/50 equals 0.06 exactly when k=3,
rounds to 0.06 exactly when k=3, and rounds to 0.04 exactly when k=2.
The equality characterization of 0.04 is included too. These integer facts
hold even without restricting k to the attainable range 0,...,50. -/
theorem integer_count_characterization (k : ℤ) :
    ((k : ℝ) / 50 = 6 / 100 ↔ k = 3) ∧
    (roundsTo ((k : ℝ) / 50) (6 / 100) ↔ k = 3) ∧
    (roundsTo ((k : ℝ) / 50) (4 / 100) ↔ k = 2) ∧
    ((k : ℝ) / 50 = 4 / 100 ↔ k = 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro h
      have hk : (k : ℝ) = 3 := by linarith
      exact_mod_cast hk
    · rintro rfl
      norm_num
  · constructor
    · rintro ⟨hl, hu⟩
      have hl' : (2 : ℝ) < (k : ℝ) := by linarith
      have hu' : (k : ℝ) < (4 : ℝ) := by linarith
      have hlz : (2 : ℤ) < k := by exact_mod_cast hl'
      have huz : k < (4 : ℤ) := by exact_mod_cast hu'
      omega
    · rintro rfl
      norm_num [roundsTo]
  · constructor
    · rintro ⟨hl, hu⟩
      have hl' : (1 : ℝ) < (k : ℝ) := by linarith
      have hu' : (k : ℝ) < (3 : ℝ) := by linarith
      have hlz : (1 : ℤ) < k := by exact_mod_cast hl'
      have huz : k < (3 : ℤ) := by exact_mod_cast hu'
      omega
    · rintro rfl
      norm_num [roundsTo]
  · constructor
    · intro h
      have hk : (k : ℝ) = 2 := by linarith
      exact_mod_cast hk
    · rintro rfl
      norm_num

/-- The same P038-T1(ii) characterization specialized to natural tail
counts; it does not enumerate any of the 50 reference observations. -/
theorem natural_count_characterization (k : ℕ) :
    ((k : ℝ) / 50 = 6 / 100 ↔ k = 3) ∧
    (roundsTo ((k : ℝ) / 50) (6 / 100) ↔ k = 3) ∧
    (roundsTo ((k : ℝ) / 50) (4 / 100) ↔ k = 2) ∧
    ((k : ℝ) / 50 = 4 / 100 ↔ k = 2) := by
  have h3 : (k : ℤ) = 3 ↔ k = 3 := by omega
  have h2 : (k : ℤ) = 2 ↔ k = 2 := by omega
  simpa only [Int.cast_natCast, h3, h2] using
    integer_count_characterization (k : ℤ)

/-- P038-T1(ii)'s consequence for the actual empirical P value: the printed
0.06 requires three tail points, and the figure-based 0.04 requires two,
whether the values are treated as exact or rounded (footnote 2, PDF p. 3). -/
theorem p25_count_characterization (R : ℝ) (r : ℤ → ℝ) :
    (empiricalP R r 25 = 6 / 100 ↔ tailCount R r 25 = 3) ∧
    (roundsTo (empiricalP R r 25) (6 / 100) ↔ tailCount R r 25 = 3) ∧
    (roundsTo (empiricalP R r 25) (4 / 100) ↔ tailCount R r 25 = 2) ∧
    (empiricalP R r 25 = 4 / 100 ↔ tailCount R r 25 = 2) := by
  have h := natural_count_characterization (tailCount R r 25)
  norm_num [empiricalP] at h ⊢
  exact h

/-- P038-T1(i), the conditional figure-based correction to footnote 2,
PDF p. 3: every positive election RR and positive reference RR family with
exactly two outside points has P_25 = 2/50 = 1/25 = 0.04. Its discrepancy
from the printed 0.06 is 1/50, one tail point. The count is a hypothesis. -/
theorem figure_based_correction (R : ℝ) (r : ℤ → ℝ)
    (_hR : 0 < R) (_hr : ∀ w ∈ referenceWeeks 25, 0 < r w)
    (hcount : tailCount R r 25 = 2) :
    empiricalP R r 25 = 2 / 50 ∧
    empiricalP R r 25 = 1 / 25 ∧
    empiricalP R r 25 = 4 / 100 ∧
    6 / 100 - empiricalP R r 25 = 1 / 50 := by
  norm_num [empiricalP, hcount]

/-- P038-T1(iii): if the 25-week tail set is exactly {-14,7}, as in
P038-N005's reading of Fig. 1's top panel (PDF p. 2), the 12-week count is one and
the 25-week count is two. The set read from the raster is an explicit
hypothesis, not an axiom or a conclusion established from FARS counts. -/
theorem figure_tail_counts (R : ℝ) (r : ℤ → ℝ)
    (hfigure : tailWeeks R r 25 = {-14, 7}) :
    tailCount R r 12 = 1 ∧ tailCount R r 25 = 2 := by
  classical
  have h12 : tailWeeks R r 12 = {7} := by
    rw [tailWeeks_restrict R r (m := 12) (n := 25) (by norm_num), hfigure]
    norm_num [referenceWeeks, Finset.filter_insert, Finset.filter_singleton]
  constructor
  · simp [tailCount, h12]
  · norm_num [tailCount, hfigure]


/-- Complete corrected-statement target P038-T1, parts (i)--(iv), attached
to footnote 2 (PDF p. 3), Fig. 1 and Methods (PDF p. 2). Part (i) quantifies
over all positive reference RRs in W_25; the remaining RR-dependent clauses
retain the target's positive RRs throughout W_100. Two tails imply P_25=0.04; 0.06
requires exactly three tails (also after rounding); tail counts are nested;
the figure-tail hypothesis {-14,7} yields P_12=1/24 and P_25=0.04; and
including election day cannot reconcile both printed values. The theorem
leaves the figure reading conditional and does not choose which published
output reflects the unavailable final data. -/
theorem corrected_election_hours_window :
    (∀ (R : ℝ) (r : ℤ → ℝ), 0 < R →
      (∀ w ∈ referenceWeeks 25, 0 < r w) → tailCount R r 25 = 2 →
      empiricalP R r 25 = 2 / 50 ∧
      empiricalP R r 25 = 1 / 25 ∧
      empiricalP R r 25 = 4 / 100 ∧
      6 / 100 - empiricalP R r 25 = 1 / 50) ∧
    (∀ k : ℤ, 0 ≤ k → k ≤ 50 →
      ((k : ℝ) / 50 = 6 / 100 ↔ k = 3) ∧
      (roundsTo ((k : ℝ) / 50) (6 / 100) ↔ k = 3) ∧
      (roundsTo ((k : ℝ) / 50) (4 / 100) ↔ k = 2) ∧
      ((k : ℝ) / 50 = 4 / 100 ↔ k = 2)) ∧
    (∀ (R : ℝ) (r : ℤ → ℝ), 0 < R →
      (∀ w ∈ referenceWeeks 100, 0 < r w) →
    (empiricalP R r 25 = 6 / 100 ↔ tailCount R r 25 = 3) ∧
    (roundsTo (empiricalP R r 25) (6 / 100) ↔ tailCount R r 25 = 3) ∧
    (roundsTo (empiricalP R r 25) (4 / 100) ↔ tailCount R r 25 = 2) ∧
    (empiricalP R r 25 = 4 / 100 ↔ tailCount R r 25 = 2) ∧
    (∀ m n : ℕ, 1 ≤ m → m ≤ n → n ≤ 100 →
      tailCount R r m ≤ tailCount R r n) ∧
    (tailWeeks R r 25 = {-14, 7} →
      tailCount R r 12 = 1 ∧ tailCount R r 25 = 2 ∧
      empiricalP R r 12 = 1 / 24 ∧
      (35 / 1000 : ℝ) ≤ empiricalP R r 12 ∧
      empiricalP R r 12 < 45 / 1000 ∧
      roundsTo (empiricalP R r 12) (4 / 100) ∧
      empiricalP R r 25 = 4 / 100 ∧
      ¬ roundsTo (empiricalP R r 25) (6 / 100) ∧
      electionDayAdjustedP R r 25 = 3 / 51 ∧
      electionDayAdjustedP R r 25 = 1 / 17 ∧
      (55 / 1000 : ℝ) ≤ electionDayAdjustedP R r 25 ∧
      electionDayAdjustedP R r 25 < 65 / 1000 ∧
      roundsTo (electionDayAdjustedP R r 25) (6 / 100) ∧
      electionDayAdjustedP R r 12 = 2 / 25 ∧
      electionDayAdjustedP R r 12 = 8 / 100 ∧
      ¬ roundsTo (electionDayAdjustedP R r 12) (4 / 100) ∧
      ¬ (roundsTo (empiricalP R r 12) (4 / 100) ∧
          roundsTo (empiricalP R r 25) (6 / 100)) ∧
      ¬ (roundsTo (electionDayAdjustedP R r 12) (4 / 100) ∧
          roundsTo (electionDayAdjustedP R r 25) (6 / 100)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro R r hR hr hcount
    exact figure_based_correction R r hR hr hcount
  · intro k _hk0 _hk50
    exact integer_count_characterization k
  · intro R r _hR _hr
    obtain ⟨heq6, hround6, hround4, heq4⟩ := p25_count_characterization R r
    refine ⟨heq6, hround6, hround4, heq4, ?_, ?_⟩
    · intro m n _hm hmn _hn
      exact tailCount_mono R r hmn
    · intro hfigure
      obtain ⟨h12, h25⟩ := figure_tail_counts R r hfigure
      norm_num [empiricalP, electionDayAdjustedP, h12, h25, roundsTo]

end AronowAudit.P038

