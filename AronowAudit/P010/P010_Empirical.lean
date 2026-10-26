import Mathlib

namespace AronowAudit.P010

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Section 3, p. 577: “90 percent/90 percent, 90 percent/70 percent,
90 percent/45 percent.” `Fin 3` indexes these arms in that order.
P010-N011: the displayed aggregate counts are inputs to the calculations. -/
def armN : Fin 3 → ℕ := ![544, 538, 533]

/-- Figure 2, pp. 578–579 and 585, P010-N011: aggregate failure counts.
Passing counts and binary success counts are used below. -/
def armFailures : Fin 3 → ℕ := ![35, 182, 40]
/-- Figure 2 reconstruction, T1/T2: subjects who “pass the manipulation
check” (p. 578), counted as arm size minus failures. -/
def armPassers (a : Fin 3) : ℕ := armN a - armFailures a
/-- Figure 2, p. 585, T1/T2: binary “preference” successes among passers. -/
def preferenceOnes : Fin 3 → ℕ := ![61, 162, 327]
/-- Figure 2, p. 585, T1/T2: binary “approval” successes among passers. -/
def approvalOnes : Fin 3 → ℕ := ![192, 188, 324]

/-- Figure 2, p. 585: the empirical failure proportion in each arm,
computed as failures divided by arm size using exact rational arithmetic. -/
def empiricalFailure (a : Fin 3) : ℚ := (armFailures a : ℚ) / armN a
/-- Proposition 1's “sum” of other-arm failure proportions over the focal
passing proportion (p. 575), evaluated on the Figure 2 input counts. -/
def empiricalTrim (a : Fin 3) : ℚ :=
  (∑ b : Fin 3, if b ≠ a then empiricalFailure b else 0) / (1 - empiricalFailure a)

/-- Authors' deposited helper, specified by target T1: sorted one-based index
`j` is retained below iff `j/n < 1-trim`, and above iff `j/n > trim`.
The strict inequalities give `ceil(n*(1-trim))-1` and `n-floor(n*trim)`.
For these data each count is positive and at most n. -/
def lowerRetained (a : Fin 3) : ℕ :=
  (⌈(armPassers a : ℚ) * (1 - empiricalTrim a)⌉ - 1).toNat
/-- T1/T2 deposited helper's upper-tail rule “j/n > trim”; the retained count
is the complement of its integer cutoff. -/
def upperRetained (a : Fin 3) : ℕ :=
  armPassers a - (⌊(armPassers a : ℚ) * empiricalTrim a⌋).toNat

/-- Figure 2, Panels D–E: “Panel D presents ... lower bounds ... Panel E ...
upper bounds” (p. 585). For n sorted binary observations with k ones, a lower
tail of m has `m-(n-k)` ones (truncated at zero); an upper tail has `min m k`
ones. This is the exact whole-observation helper, not fractional trimming. -/
def empiricalBounds (ones : Fin 3 → ℕ) (a : Fin 3) : ℚ × ℚ :=
  ((lowerRetained a - (armPassers a - ones a) : ℕ) / (lowerRetained a : ℚ),
   (min (upperRetained a) (ones a) : ℕ) / (upperRetained a : ℚ))
/-- Figure 2, Panels D–E, p. 585: the “bounds” interval of real mean values
between the exact reconstructed empirical endpoints. -/
noncomputable def empiricalInterval (ones : Fin 3 → ℕ) (a : Fin 3) : Set ℝ :=
  Set.Icc ((empiricalBounds ones a).1 : ℝ) ((empiricalBounds ones a).2 : ℝ)

/-- Fractional trimming, T2(d), P010-N011: the union-bound lower
mass of always-passers, equal to one minus the sum of arm failure proportions. -/
def empiricalAlwaysMass : ℚ := 1 - ∑ a : Fin 3, empiricalFailure a
/-- Corrected T2(d), P010-N011: “fractional trimming” of the
binary preference distribution at union-bound retained mass q. -/
def fractionalBounds (a : Fin 3) : ℚ × ℚ :=
  let az : ℚ := (preferenceOnes a : ℚ) / armN a
  (max 0 ((az - ∑ b : Fin 3, if b ≠ a then empiricalFailure b else 0) /
    empiricalAlwaysMass), min 1 (az / empiricalAlwaysMass))

/-- The counts, trimming proportions, and endpoints in T1 and T2 are exact
consequences of the input counts and the helper's strict cutoff convention. -/
theorem empirical_exact_certificate :
    (∀ a : Fin 3, armPassers a = (![509,356,493] : Fin 3 → ℕ) a) ∧
    (∀ a : Fin 3, empiricalTrim a =
      (![32239072/72978893,10871635/51611456,31403827/72143648] : Fin 3 → ℚ) a) ∧
    (∀ a : Fin 3, lowerRetained a = (![284,281,278] : Fin 3 → ℕ) a) ∧
    (∀ a : Fin 3, upperRetained a = (![285,282,279] : Fin 3 → ℕ) a) ∧
    (∀ a : Fin 3, empiricalBounds preferenceOnes a =
      (![(0,61/285),(87/281,27/47),(56/139,1)] : Fin 3 → ℚ × ℚ) a) ∧
    (∀ a : Fin 3, empiricalBounds approvalOnes a =
      (![(0,64/95),(113/281,2/3),(109/278,1)] : Fin 3 → ℚ × ℚ) a) := by
  norm_num [Fin.forall_fin_succ, empiricalTrim, empiricalFailure, armN,
    armFailures, armPassers, lowerRetained, upperRetained, empiricalBounds,
    preferenceOnes, approvalOnes, Fin.sum_univ_succ]

/-- Strict lower-tail membership reduces to an integer index cutoff when
its rational threshold lies between the m-th and (m+1)-st observations. -/
theorem rational_lower_cutoff (n m j : ℕ) (c : ℚ)
    (hlo : (m : ℚ)/n < c) (hhi : c ≤ ((m:ℚ)+1)/n) :
    ((j:ℚ)/n < c ↔ j ≤ m) := by
  constructor
  · intro h
    by_contra hn
    have hn' : m+1 ≤ j := by omega
    have hq : (m:ℚ)+1 ≤ j := by exact_mod_cast hn'
    have hh : ((m:ℚ)+1)/n ≤ (j:ℚ)/n := div_le_div_of_nonneg_right hq (Nat.cast_nonneg n)
    exact (not_lt_of_ge (hhi.trans hh)) h
  · intro h
    have hq : (j:ℚ) ≤ m := by exact_mod_cast h
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right hq (Nat.cast_nonneg n)) hlo

/-- Strict upper-tail membership reduces to the complementary integer cutoff
under the deposited helper rule (P010-N011). -/
theorem rational_upper_cutoff (n m j : ℕ) (c : ℚ)
    (hlo : (m:ℚ)/n ≤ c) (hhi : c < ((m:ℚ)+1)/n) :
    (c < (j:ℚ)/n ↔ m < j) := by
  constructor
  · intro h
    by_contra hn
    have hn' : j ≤ m := by omega
    have hq : (j:ℚ) ≤ m := by exact_mod_cast hn'
    exact (not_lt_of_ge ((div_le_div_of_nonneg_right hq (Nat.cast_nonneg n)).trans hlo)) h
  · intro h
    have hn' : m+1 ≤ j := by omega
    have hq : (m:ℚ)+1 ≤ j := by exact_mod_cast hn'
    exact lt_of_lt_of_le hhi (div_le_div_of_nonneg_right hq (Nat.cast_nonneg n))

/-- The retained counts really implement `j/n < 1-trim` and `j/n > trim`
for every one-based passer index; thus no floor convention has been assumed
in place of the deposited helper (T1/T2). -/
theorem empirical_cutoff_certificate (a : Fin 3) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j ≤ armPassers a) :
    (((j : ℚ) / armPassers a < 1 - empiricalTrim a) ↔ j ≤ lowerRetained a) ∧
    (((j : ℚ) / armPassers a > empiricalTrim a) ↔ armPassers a - upperRetained a < j) := by
  fin_cases a <;>
    norm_num [empiricalTrim, empiricalFailure, armN, armFailures, armPassers,
      lowerRetained, upperRetained, Fin.sum_univ_succ] <;>
    constructor
  all_goals first
    | (apply rational_lower_cutoff <;> norm_num)
    | (apply rational_upper_cutoff <;> norm_num)

/-- T1, Section 3, pp. 578–579, counterexample to overlap of all treatment
bounds for both outcomes: preference arm 90–90 is disjoint from each other
arm, so both pairwise overlap and a common intersection fail. -/
theorem empirical_overlap_counterexample :
    Disjoint (empiricalInterval preferenceOnes 0) (empiricalInterval preferenceOnes 1) ∧
    Disjoint (empiricalInterval preferenceOnes 0) (empiricalInterval preferenceOnes 2) ∧
    ¬ (∀ a b : Fin 3, ∃ x : ℝ,
      x ∈ empiricalInterval preferenceOnes a ∧ x ∈ empiricalInterval preferenceOnes b) ∧
    ¬ (∃ x : ℝ, ∀ a : Fin 3, x ∈ empiricalInterval preferenceOnes a) := by
  have hb := empirical_exact_certificate.2.2.2.2.1
  have h01 : Disjoint (empiricalInterval preferenceOnes 0) (empiricalInterval preferenceOnes 1) := by
    rw [Set.disjoint_left]
    intro x hx hy
    norm_num [empiricalInterval, hb, Set.mem_Icc] at hx hy
    linarith
  have h02 : Disjoint (empiricalInterval preferenceOnes 0) (empiricalInterval preferenceOnes 2) := by
    rw [Set.disjoint_left]
    intro x hx hy
    norm_num [empiricalInterval, hb, Set.mem_Icc] at hx hy
    linarith
  refine ⟨h01, h02, ?_, ?_⟩
  · intro h
    obtain ⟨x,hx,hy⟩ := h 0 1
    exact Set.disjoint_left.mp h01 hx hy
  · rintro ⟨x,hx⟩
    exact Set.disjoint_left.mp h01 (hx 0) (hx 1)

/-- T2, corrected Section 3 interpretation, pp. 578–579: approval has the
common witness 1/2; preference arms 2 and 3 overlap at 1/2, while arm 1 lies
strictly below both. Both estimated difference lower endpoints are positive.
The same separation holds under exact fractional trimming (part d). -/
theorem empirical_overlap_corrected :
    (∀ a : Fin 3, (1/2 : ℝ) ∈ empiricalInterval approvalOnes a) ∧
    (1/2 : ℝ) ∈ empiricalInterval preferenceOnes 1 ∧
    (1/2 : ℝ) ∈ empiricalInterval preferenceOnes 2 ∧
    (empiricalBounds preferenceOnes 0).2 < (empiricalBounds preferenceOnes 1).1 ∧
    (empiricalBounds preferenceOnes 0).2 < (empiricalBounds preferenceOnes 2).1 ∧
    (empiricalBounds preferenceOnes 1).1 - (empiricalBounds preferenceOnes 0).2 = 7654/80085 ∧
    (empiricalBounds preferenceOnes 2).1 - (empiricalBounds preferenceOnes 0).2 = 7481/39615 ∧
    (0 : ℚ) < 7654/80085 ∧ (0 : ℚ) < 7481/39615 ∧
    empiricalAlwaysMass = 40739821/77997088 ∧ 0 < empiricalAlwaysMass ∧
    (∀ a : Fin 3, fractionalBounds a =
      (![(0,8745997/40739821),(12614477/40739821,23486112/40739821),
        (16448045/40739821,1)] : Fin 3 → ℚ × ℚ) a) ∧
    (fractionalBounds 1).1 - (fractionalBounds 0).2 = 3868480/40739821 ∧
    (fractionalBounds 2).1 - (fractionalBounds 0).2 = 7702048/40739821 ∧
    (0 : ℚ) < 3868480/40739821 ∧ (0 : ℚ) < 7702048/40739821 := by
  have hp := empirical_exact_certificate.2.2.2.2.1
  have ha := empirical_exact_certificate.2.2.2.2.2
  simp only [empiricalInterval, hp, ha]
  norm_num [Fin.forall_fin_succ, empiricalAlwaysMass,
    fractionalBounds, empiricalFailure, preferenceOnes, armN, armFailures,
    Fin.sum_univ_succ]

end AronowAudit.P010
