import SAP.P003b.WH.W2.Counting
import SAP.P003b.WH.W2.Numerical
import SAP.P003b.WH.W2.Cost

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W2
open scoped BigOperators
open SAP.P003b.Bridge
attribute [local instance 0] Classical.propDecidable
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

/-- Realize all prescribed stratum counts on the actual fixed labels.
Prove by realizing each Counts on
Fin total with neyman_exists_table, transporting to the fibers X=false/true
using Fintype.equivOfCardEq, and joining the two tables. Transport filter
cards by the equivalences; empty fibers need no positivity assumption.
The reverse inclusions use countsOn_total and corrected_stratum_count_mem.
Expected proof size: 150-250 lines. -/
def T19_L1 : Prop :=
  ∀ (n : ℕ) (X : Fin n → Bool),
    wholeStratumImage X = stratifiedCounts (wholeStratumSize X false) (wholeStratumSize X true)

/-- The labeled balanced witness has the announced observations and counts.
Split each label according to treatment membership and the two values of Y.
Finite filter partitions give the arm totals and the 10/01 counts; the 11/00
filters are empty. Sum the observed-success indicators to identify the
Neyman estimator. No randomization assumption or nonempty stratum is needed
for the counting identities; the estimator equality is requested only when
both arms are nonempty. Expected proof size: 80-160 lines. -/
def T30_L1 : Prop :=
  ∀ (n : ℕ) (Y : Fin n → Bool) (z : Finset (Fin n)),
    let o := wholeObservedCounts Y z
    let w := wholeBalancedWitness Y z
    o.total = n ∧ o.a+o.b = z.card ∧ o.c+o.d = n-z.card ∧
    wholeAgrees w Y z ∧ tableCounts w = wholeBalancedVector o ∧
    (0 < z.card → z.card < n → tableEstimator w z = estimate o)

/-- Arithmetic implementation of the minimum feasible base.
Prove B.2-B.3 from glp0032b2_possible_iff by eliminating the single imputation
coordinate (integer max/min inequalities). The lower bound is nonnegative
and obeys every coordinate guard when the interval is nonempty. It gives
the minimum b, hence agrees with first_on_line_spec/minimum_b_spec; an empty
interval or failed guard gives no possible point. Split off integer
feasibility before using toNat or natural subtraction.
Expected proof size: 180-300 lines. -/
def T36_L1 : Prop :=
  ∀ (o : Counts) (x : ℤ) (j : ℕ), wholeFastBase o x j = firstOnLine o x j

/-- Direct generation of the legal reuse interval.
For a selected base, B.3 says that possible b values are all integers from
its minimum b through wholeLineUpper. Increasing b by k is reuseVector;
its endpoint also enforces k<=v.a and k<=v.d. Show pointwise membership
and use the increasing, duplicate-free order of both lists to obtain list
equality. Derive the necessary integer interval characterization as an
auxiliary from glp0032b2_possible_iff (or share that auxiliary with T36_L1).
Expected proof size: 120-240 lines. -/
def T36_L2 : Prop :=
  ∀ (o v : Counts) (x : ℤ) (j : ℕ), firstOnLine o x j = some v →
    wholeCostReuse o x j v = reuseLine o v

theorem T19_assembly (h1 : T19_L1) : T19WholeStatement := by
  have hinfo (n : ℕ) (X : Fin n → Bool) :
      (wholeStratumImage X).card =
        (wholeStratumSize X false+3).choose 3 * (wholeStratumSize X true+3).choose 3 := by
    rw [h1 n X, stratum_card]
  refine ⟨rows_independent,?_,?_,?_,stratum_order,?_,four_order,?_⟩
  · rintro ⟨⟨a,b⟩,s⟩
    cases s <;> norm_num [wholeStratumRow]
  · intro n X
    have hs := stratum_sizes X
    refine ⟨hs,?_,h1 n X,hinfo n X,?_,unstratified_image n,four_card n,tables_card n⟩
    · intro w
      have h₀ := countsOn_total (Finset.univ.filter fun i => X i = false) w
      have h₁ := countsOn_total (Finset.univ.filter fun i => X i = true) w
      exact ⟨h₀,h₁,(congrArg₂ (·+·) h₀ h₁).trans hs⟩
    · rw [h1 n X]
      have h := (AronowAudit.P003.Wave1.corrected_stratum_count_proof
        (wholeStratumSize X false) (wholeStratumSize X true)).2.2.1
      simpa only [stratified_card_eq,hs,Nat.cast_add,Nat.cast_ofNat] using h
  · intro n
    exact ⟨totalEight_mem n,totalEight_card n,(AronowAudit.P003.Wave1.corrected_stratum_count_eight_sum n).symm⟩
  · apply polynomial_order _ 7 (fun _ => by positivity)
    intro n
    rw [totalEight_card n]
    exact composition_bound 7 n n le_rfl
  · intro X h₀ h₁
    refine ⟨by norm_num [tables_card],?_,?_,?_,?_⟩
    · rw [hinfo, h₀, h₁]
      decide +kernel
    · rw [totalEight_card]
      decide +kernel
    · rw [totalEight_mem]
      rfl
    · rintro ⟨w,hw⟩
      have ht := countsOn_total (Finset.univ.filter fun i => X i = false) w
      change (wholeStratumCounts X w).1.total = wholeStratumSize X false at ht
      rw [hw,h₀] at ht
      norm_num [Counts.total] at ht

theorem T25_assembly : T25WholeStatement := by
  refine ⟨?_,balanced_j,example_candidates,?_,?_,example_unique,?_,example_maxima,
    example_j,example_interval,example_endpoints,example_printed,?_,?_⟩
  · intro o α _ _ _
    exact ⟨j_eq_accepted o α,j_subset o α⟩
  · exact ⟨by norm_num [tauQ,Counts.effect,Counts.total],by decide +kernel,by decide +kernel⟩
  · exact ⟨by norm_num [tauQ,Counts.effect,Counts.total],by decide +kernel,by decide +kernel⟩
  · exact ⟨by decide +kernel,by norm_num [tauQ,Counts.effect,Counts.total],by decide +kernel⟩
  · rw [example_interval]
    norm_num
  · rw [example_interval, example_candidates]
    norm_num

theorem T20_assembly : T20WholeStatement := by
  refine ⟨?_,retained20,?_,minimum_line,?_,?_,?_⟩
  · intro n m _hm
    exact ⟨assignmentEquiv n m,fun _ => rfl,uniform_equiv (assignmentEquiv n m)⟩
  · intro n a b c j v x
    omega
  · intro o u v α ho hu hv hd
    have hp := minimum_pvalue o u v ho hu hv hd
    refine ⟨hp,fun h => lt_of_le_of_lt ?_ h⟩
    exact_mod_cast hp
  · intro b k h
    have h₁ := congrArg (fun v : ℤ × ℤ × ℤ × ℤ => v.1) h
    have h₂ := congrArg (fun v : ℤ × ℤ × ℤ × ℤ => v.2.1) h
    dsimp [wholeSignedLine] at h₁ h₂
    omega
  · refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,?_,?_⟩ <;>
      norm_num [wholeT20Table, wholeT20Assignment, tableEstimator, bit, Fin.sum_univ_two]

theorem T30_assembly (h1 : T30_L1) : T30WholeStatement := by
  constructor
  · intro o α ho hα
    have hv := balanced_vector o ho
    have hm := balanced_membership o α ho hα
    exact ⟨hv.1,hv.2.1,hv.2.2,hm.1,hm.2.1,⟨estimate o,hm.1⟩,hm.2.2⟩
  · intro m Y z α hm hα
    have hl := h1 (2*m) Y z.val
    dsimp only at hl ⊢
    let o := wholeObservedCounts Y z.val
    let w := wholeBalancedWitness Y z.val
    have ha : o.a+o.b = m := hl.2.1.trans z.property
    have hc : o.c+o.d = m := by rw [hl.2.2.1,z.property]; omega
    have ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d := ⟨by omega,by omega⟩
    have hv := balanced_vector o ho
    have hmem := balanced_membership o α ho hα
    have hcounts : tableCounts w = wholeBalancedVector o := hl.2.2.2.2.1
    have ht : tableTau w = tau (wholeBalancedVector o) := by
      have h := (AronowAudit.P003.corrected_sate w (by omega : 0 < 2*m)).2.2.2
      change tableTau w = tau (tableCounts w) at h
      exact h.trans (congrArg tau hcounts)
    have hte : tableTau w = estimate o := ht.trans hv.2.1
    have hprob : uniformProb (fun z' : Assignment (2*m) m =>
        |tableEstimator w z'.val-tableTau w| ≥ |estimate o-tableTau w|) = 1 := by
      have hpos : 0 < Fintype.card (Assignment (2*m) m) := Fintype.card_pos_iff.mpr ⟨z⟩
      have hcard : (Fintype.card (Assignment (2*m) m) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hpos)
      simp only [uniformProb,hte,sub_self,abs_zero,ge_iff_le,abs_nonneg,
        Finset.filter_true,Finset.card_univ]
      exact div_self hcard
    exact ⟨hl.1,ha,hc,hl.2.2.2.1,hcounts,ht,hte,
      hl.2.2.2.2.2 (by rw [z.property]; exact hm) (by rw [z.property]; omega),
      hprob,by rw [hcounts]; exact hv.2.2,hmem.1,hmem.2.1,
      ⟨estimate o,hmem.1⟩,hmem.2.2⟩

theorem T36_assembly (h1 : T36_L1) (h2 : T36_L2) : T36WholeStatement := by
  refine ⟨h1,h2,cost_finite,?_⟩
  intro full c₀ c₁ c₂ hc
  exact ⟨cost_joint full c₀ c₁ c₂ hc,cost_schedule full c₀ c₁ c₂ hc⟩

end
end SAP.P003b.WH.W2
