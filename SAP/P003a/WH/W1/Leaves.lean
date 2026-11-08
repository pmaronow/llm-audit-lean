import SAP.P003a.WH.W1.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

namespace SAP.P003a.WH.W1

open SAP.P003a.Bridge
open scoped BigOperators

/-- The ten attained maxima over the 42 possible vectors. Prove finite certificates
for each effect fiber, then extract an attaining vector and its universal bound.
Use possibleTables, pValue and exact kernel reduction; no supremum of an empty set
is involved. Expected proof: at most 120 lines. -/
def T21_L1 : Prop :=
  ∀ dp ∈ w1FootnoteMaxima, w1MaxP ⟨1,6,0,2⟩ dp.1 dp.2

/-- Soundness and completeness of the corrected ordered traversal. Use
corrected_general_loop for completeness, first_on_line_spec for each base, and
the possibility filter and coordinate bounds of w1ReuseLine for positive k.
List.finRange has every slot, including the total-zero case. At most 180 lines. -/
def T22_L1 : Prop :=
  ∀ o u, (∃ s ∈ w1Traversal true o, reuseVector s.base s.k = u) ↔ Possible o u

/-- Unfolding the finite accumulation gives precisely the slot-indexed output
formula. Expand flatMap and line membership, separate k=0 from k>0, and use
first_on_line_spec to certify the base case. Keep w1ReusedSamples unchanged:
this is the actual correlated update, for arbitrary R and realized seeds.
AronowAudit.P003.generalSet supplies the identical declarative donor model.
Expected proof: at most 180 lines, with no probability theorem. -/
def T22_L2 : Prop :=
  ∀ (m K : ℕ) (α : ℝ) (θ : Counts → ℝ) (R : Counts → Counts → ℝ) (o : Counts)
    (initial : (Fin (o.total+1) × Fin (o.total+1)) → Fin K → Assignment o.total m)
    (seeds : (Fin (o.total+1) × Fin (o.total+1)) → Fin o.total → Fin K →
      (Fin o.total.factorial × Fin o.total.factorial)),
    w1GeneralOutput true α θ R o initial seeds = w1GeneralFormula α θ R o initial seeds

/-- Instrumentation erases to the existing corrected search, records whole effect
blocks, and preserves chronological table-test indices. Induct on fuel and the
runTests list, using T7_runTests_cost and GLP0032B6_search_reply. Transport
T7_upperRun_budget across the four-field bridge to obtain termination and the
fresh-slot bound. Empty compatibility blocks consume no slot. At most 300 lines. -/
def T23_L1 : Prop :=
  (∀ (fuel : ℕ) (o : Counts) (reject : Counts → ℕ → Bool)
    (k₁ k₂ a b : ℤ) (idx : ℕ),
    let s := w1EffectSearch fuel o reject a b idx;
    s.value = (adaptiveSearch fuel true o k₁ k₂ reject a b idx).value ∧
    s.tests = (adaptiveSearch fuel true o k₁ k₂ reject a b idx).trace ∧
    (∀ q ∈ s.queries,
      q.rejected = !(runTests reject q.start (candidates o q.x)).compatible) ∧
    (∀ i, i < s.tests.length →
      (s.tests[i]!).2 = reject (s.tests[i]!).1 (idx+i))) ∧
  (∀ (o : Counts) (reject : Counts → ℕ → Bool)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d),
    let s := w1EffectUpperRun o reject;
    s.value.isSome ∧ s.tests.length ≤ w1TestBudget o.total)

/-- Bracket invariant for stateful decisions: every rejection cuts off the return
and every subsequent query. Induct on fuel, splitting the compatibility bit;
the midpoint is strictly interior when b>a+1. The invariant holds even when
fuel runs out; the return assertions are conditional on some A. Use the
argument of sentinel_search_invariants and List.pairwise_cons. At most 180 lines. -/
def T23_L2 : Prop :=
  ∀ (fuel : ℕ) (o : Counts) (reject : Counts → ℕ → Bool)
    (a b : ℤ) (idx : ℕ) (hab : a < b),
    let s := w1EffectSearch fuel o reject a b idx;
    (∀ A, s.value = some A → a ≤ A ∧ A < b ∧
      ∀ q ∈ s.queries, q.rejected = true → A < q.x) ∧
    s.queries.Pairwise (fun q r => q.rejected = true → r.x < q.x)

/-- The explicit labeled population, critical assignment, missing entry and mask
transport. Finite Boolean calculations handle the critical assignment. For all
assignments use neyman_event_pushforward; equality of the critical treated state
forces the treated set to be precisely {11,12,13}, since both have size three.
This identifies the labeled missingness rule with badMask. At most 250 lines. -/
def T1_L1 : Prop := w1BadRealization

/-- The real critical hulls, completion-union witness, D.5 and the two actual D.7
tails. Use real_extrema_of_intervalQ and interval_eq_Icc for the certified
rational endpoints; insert the true binary completion into the labeled union.
Use neyman_pValue_pushforward for both tails, with no possibility assumption
for the upper completion, and missing_critical_tail_counterexample for 83/380.
Expected proof: at most 250 lines. -/
def T1_L2 : Prop := w1BadCritical

/-- Finite constrained maximum over tables possible for (0,3,10,7). Specialize
possible_table_facts to total twenty, so tau>=-3/20 is effect>=-3. Certify the
universal tail-count bound 248 and equality at exactly the two displayed vectors
by reducing the finite possibleTables list in the kernel. Divide by choose(20,3).
Expected proof: at most 100 lines. -/
def T1_L3 : Prop :=
  ∀ v, Possible ⟨0,3,10,7⟩ v → (-3/20 : ℚ) ≤ tauQ v →
    pValue v ⟨0,3,10,7⟩ ≤ 248/1140 ∧
    (pValue v ⟨0,3,10,7⟩ = 248/1140 ↔ v = ⟨8,0,3,9⟩ ∨ v = ⟨9,0,3,8⟩)

/-- The complete ten-row diagnostic, including labeled multiplicities. Use
bad_random_states_certificate and the ten interval_obs_* results, then
neyman_fiber_card and neyman_estimator_eq to transport each group. The observed
vectors distinguish the ten treated states. The real interval bridge and exact
rational arithmetic give estimate inclusion and each coverage bit. At most 300 lines. -/
def T1_L4 : Prop := w1BadDiagnostics

/-- Zero-mask equality on the 1139 nonexceptional assignments and both actual
labeled coverage probabilities. For each of the ten certified observations the
estimate is inside its exact interval, so min/max with it do not enlarge the
zero-mask hull. Use the finite state certificate and neyman_event_pushforward
for complete-data coverage; badJointLaw_coverage and mask transport give the
imputation probability. A finite singleton complement gives 1139. At most 300 lines. -/
def T1_L5 : Prop := w1BadCoverageFacts

/-- Full two-atom labeled estimator law for the population (0,15,0,1). Its only
treated states are (0,7,0,1) and (0,8,0,0), each of multiplicity 6435. Use
neyman_treated_mem, neyman_fiber_card and neyman_estimator_eq, then rational
arithmetic for the three deviations. No enumeration of real-valued predicates
or extra sampling assumption is needed. Expected proof: at most 180 lines. -/
def T4_L1 : Prop :=
  let w : PotentialTable 16 := fun i => canonicalPair ⟨0,15,0,1⟩ i.val;
  tableCounts w = ⟨0,15,0,1⟩ ∧ tableTau w = 15/16 ∧
  (∀ z : Assignment 16 8, tableEstimator w z.val = 7/8 ∨ tableEstimator w z.val = 1) ∧
  (Finset.univ.filter fun z : Assignment 16 8 => tableEstimator w z.val = 7/8).card = 6435 ∧
  (Finset.univ.filter fun z : Assignment 16 8 => tableEstimator w z.val = 1).card = 6435 ∧
  |(7/8 : ℝ)-15/16| = 1/16 ∧ |(1 : ℝ)-15/16| = 1/16 ∧
  |estimate ⟨7,1,0,8⟩-15/16| = 1/16

theorem T21_assembly (h1 : T21_L1) : T21WholeStatement := by
  classical
  have hc := retained_T21
  have hi := real_interval_certificate (17/18) ⟨1,6,0,2⟩ 0 (1/9) hc.2.1
  have hI : exactInterval ((17/18 : ℚ) : ℝ) ⟨1,6,0,2⟩ = Set.Icc 0 (1/9) := by
    simpa using hi.2.2.2
  refine ⟨hc, ?_⟩
  refine ⟨rfl,rfl,by decide,by decide,?_,by decide +kernel,by decide +kernel,
    by decide +kernel,h1,by decide +kernel,by decide +kernel,?_,hI,?_,
    by decide +kernel,by decide +kernel⟩
  · norm_num [Assignment, Fintype.card_finset_len]
    decide +kernel
  · ext t
    rw [accepted_real_spec]
    have hd (d : ℤ) : d ∈ acceptedEffectsQ (17/18) ⟨1,6,0,2⟩ ↔ d = 0 ∨ d = 1 := by
      rw [← List.mem_toFinset,hc.1]
      simp
    simp [hd,Counts.total]
  · rw [hI]
    norm_num [estimate,estimateQ]

theorem T22_assembly (h1 : T22_L1) (h2 : T22_L2) : T22WholeStatement := by
  classical
  refine ⟨retained_T22,h1,h2,?_,zero_rank,by decide +kernel⟩
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,by decide +kernel,by decide +kernel,?_⟩
  intro K α _hK hα initial seeds
  have hfalse : w1Traversal false ⟨0,1,0,1⟩ =
      [⟨(0,1),⟨0,1,0,1⟩,0⟩,⟨(1,0),⟨0,0,0,2⟩,0⟩,⟨(2,0),⟨0,0,1,1⟩,0⟩] := by
    decide +kernel
  have htrue : w1Traversal true ⟨0,1,0,1⟩ =
      [⟨(0,1),⟨0,1,0,1⟩,0⟩,⟨(1,0),⟨0,0,0,2⟩,0⟩,
       ⟨(1,1),⟨0,1,1,0⟩,0⟩,⟨(2,0),⟨0,0,1,1⟩,0⟩] := by
    decide +kernel
  constructor <;> ext t
  · simp [w1GeneralOutput,hfalse,zero_rank,hα.2,reuseVector,or_comm,or_left_comm]
  · simp [w1GeneralOutput,htrue,zero_rank,hα.2,reuseVector,or_comm,or_left_comm]
    norm_num

theorem T1_assembly (h1 : T1_L1) (h2 : T1_L2) (h3 : T1_L3)
    (h4 : T1_L4) (h5 : T1_L5) : T1WholeStatement := by
  refine ⟨retained_T1,h1,h2,h3,?_,h4,h5,?_,?_,?_,?_⟩
  · decide +kernel
  all_goals norm_num

theorem T4_assembly (h1 : T4_L1) : T4WholeStatement := by
  classical
  have hc := retained_T4
  have hi := real_interval_certificate (1/20) ⟨7,1,0,8⟩ (1/2) (15/16) hc.2.2.2.2.2.2.1
  have hI : exactInterval ((1/20 : ℚ) : ℝ) ⟨7,1,0,8⟩ = Set.Icc (1/2) (15/16) := by
    simpa using hi.2.2.2
  have hU : upper ((1/20 : ℚ) : ℝ) ⟨7,1,0,8⟩ = 15/16 := by simpa using hi.2.2.1
  refine ⟨hc,by decide +kernel,?_,?_,?_,h1,?_⟩
  · intro fuel
    simpa [w1PrintedRun,searchStep,List.replicate_succ] using
      congrArg (fun r : W1PrintedResult =>
        (⟨r.value,1::r.queries,r.bracket⟩ : W1PrintedResult)) (printed_absorbing fuel)
  · have hl : logTwo 2 = 1 := by
      exact div_self (ne_of_gt (Real.log_pos (by norm_num)))
    rw [hl]
    norm_num
  · have h14 : (runTests (exactRejectQ (1/20) ⟨7,1,0,8⟩) 0
        (candidates ⟨7,1,0,8⟩ 14)).compatible = true := by decide +kernel
    refine ⟨rfl,rfl,rfl,by decide +kernel,by decide +kernel,by norm_num,by norm_num,
      by decide +kernel,?_,by decide +kernel,by decide +kernel,?_,?_,
      by decide +kernel,by decide +kernel,h14,by decide +kernel,
      by decide +kernel,by decide +kernel,hI,hU,?_,?_⟩
    · norm_num [Assignment,Fintype.card_finset_len]
      decide +kernel
    · intro j hj
      exact first_before_positive_none _ _ _ (by omega)
    · intro j hj
      exact first_before_positive_none _ _ _ (by omega)
    · decide +kernel
    · rw [hU]; norm_num
  · decide +kernel

theorem T23_assembly (h1 : T23_L1) (h2 : T23_L2) : T23WholeStatement := by
  classical
  refine ⟨retained_T23,?_⟩
  intro o K α ε ho _hK hα _hε pool
  let reject := w1ApproxReject α ε o pool
  let s := w1EffectUpperRun o reject
  let k₁ := (w1UpperBounds o).1
  let k₂ := (w1UpperBounds o).2
  have er := h1.1 (o.total+3) o reject k₁ k₂ (k₁-1) (k₂+1) 0
  have hev : s.value = (upperRun true o reject).value := er.1
  have het : s.tests = (upperRun true o reject).trace := er.2.1
  obtain ⟨A,hA⟩ := Option.isSome_iff_exists.mp (h1.2 o reject ho).1
  have hab : k₁-1 < k₂+1 := by dsimp [k₁,k₂,w1UpperBounds]; omega
  have hs := h2 (o.total+3) o reject (k₁-1) (k₂+1) 0 hab
  have hn : (0 : ℝ) < o.total := by
    have hnat : 0 < o.total := by dsimp [Counts.total]; omega
    exact_mod_cast hnat
  obtain ⟨r,_hr₁,_hr₂,hr,_hcover,_hsound⟩ :=
    AronowAudit.P003.Wave1.GLP0032B6_upper_certificate (toAudit o) α ho hα
  have hU : upper α o = (r : ℝ)/o.total := by simpa only [to_upper,to_total] using hr
  have hest := AronowAudit.P003.balanced_estimate_in_interval (toAudit o) α ho hα
  have hne : (accepted α o).Nonempty :=
    ⟨estimate o, by simpa only [to_estimate,to_accepted] using hest.1⟩
  refine ⟨A,r,hA,hev.symm.trans hA,het,hne,hU,er.2.2.1,?_,?_,?_,?_⟩
  · intro i hi
    change i < s.tests.length at hi
    constructor
    · have hb : s.tests.length ≤ w1TestBudget o.total := (h1.2 o reject ho).2
      omega
    change (s.tests[i]!).2 = reject (s.tests[i]!).1 i
    have hr := er.2.2.2 i hi
    rw [getElem!_pos (w1EffectSearch (o.total+3) o reject (k₁-1) (k₂+1) 0).tests i hi] at hr
    rw [getElem!_pos s.tests i hi]
    dsimp only [s,w1EffectUpperRun,k₁,k₂] at hr ⊢
    simpa only [Nat.zero_add] using hr
  · intro q hq hqrej
    apply (div_lt_div_iff_of_pos_right hn).mpr
    exact_mod_cast (hs.1 A hA).2.2 q hq hqrej
  · intro i j hij hj hrej
    change j < s.queries.length at hj
    change (s.queries[i]!).rejected = true at hrej
    change (s.queries[j]!).x < (s.queries[i]!).x
    have hi : i < s.queries.length := by omega
    have hp := hs.2.rel_getElem_of_lt hi hj hij
    rw [getElem!_pos s.queries i hi] at hrej
    rw [getElem!_pos s.queries j hj,getElem!_pos s.queries i hi]
    exact hp hrej
  · intro hreturn q hq hle
    by_cases hrq : q.rejected = true
    · have hAc : (A : ℝ)/o.total < (q.x : ℝ)/o.total := by
        apply (div_lt_div_iff_of_pos_right hn).mpr
        exact_mod_cast (hs.1 A hA).2.2 q hq hrq
      rw [hU] at hle
      linarith
    · exact Bool.eq_false_iff.mpr hrq

end SAP.P003a.WH.W1
