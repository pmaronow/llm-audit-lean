import SAP.P045a.WH.W1.Helpers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a.WH.W1
noncomputable section

/-- T1: missing both-arm conditional means and their lift to the actual two-stage law.
Group by K using bernoulli4_count_law and four_arm_domains; on the event use
co_members_arm_mean. The count certificate bernoulli_count_counterexample gives
the four both-arm values. For each first-stage-selected regime, apply
witness_high_expect or witness_low_expect to the event numerator and denominator.
Own-arm positivity is the probability of K>0 or K<4. About 80–140 lines. -/
def T1_L1 : Prop :=
  w1BothArmMean (1/2) true = 1 ∧ w1BothArmMean (1/2) false = 2 ∧
  w1BothArmMean (1/4) true = 13/29 ∧ w1BothArmMean (1/4) false = 42/29 ∧
  (∀ high b : Bool,
    let p : ℝ := if high then 1/2 else 1/4
    prob bernoulliWitnessMass (witnessDomain b high) = prob (bernoulli (n := 4) p) (armExists b) ∧
    0 < prob bernoulliWitnessMass (witnessDomain b high) ∧
    condMean bernoulliWitnessMass (witnessDomain b high) (witnessArm b high) =
      (if high then (if b then 17/15 else 28/15) else (if b then 81/175 else 84/85)) ∧
    condMean bernoulliWitnessMass
      (fun w => witnessDomain true high w ∧ witnessDomain false high w) (witnessArm b high) =
      (if high then (if b then 1 else 2) else (if b then 13/29 else 42/29)))

/-- T2: first-stage averaging from conditional coordinate marginals, with arbitrary
cross-group dependence. Expand the joint expectation, swap the selected-group and
assignment sums, and sum over fibres u(g)=z. For the high regime use
uniform_first_stage_mean. For the low regime change variables H to univ\H;
complement is a bijection between C-subsets and (G-C)-subsets. The guard on
w1RegimeCount excludes an empty regime, including the C=G low-regime case.
No independent product law may be added. About 120–220 lines. -/
def T2_L1 : Prop :=
  ∀ (G C : ℕ), C ≤ G → ∀ (n : Fin G → ℕ) (high : Bool),
    0 < w1RegimeCount G C high →
    ∀ (Q : Finset (Fin G) → Design (GroupAssignments n))
      (q : (g : Fin G) → Assignment (n g) → ℝ),
    w1CoordinateLaw C high Q q →
    ∀ (X : (g : Fin G) → Assignment (n g) → ℝ),
    expect (w1JointMass C Q) (w1RegimeMean C high X) =
      mean (fun g => expect (q g) (X g))

/-- T3: exact support of the actual joint experiment. Each first-stage set has
three groups of each kind; each local support has size three by fixed_three_supports.
Use the dependent finite-product cardinality formula, and card_powersetCard for
choose(6,3)=20. Every supported mass is (1/20)(1/3)^6=1/14580.
Sum that support formula for normalization; outside it a local factor is zero.
About 70–140 lines; do not enumerate the 2^6*8^6 ambient outcomes. -/
def T3_L1 : Prop :=
  w1ToySupport.card = 14580 ∧ (∀ w, 0 ≤ w1ToyMass w) ∧ (∑ w, w1ToyMass w) = 1 ∧
  (∀ w, w1ToyMass w = if w ∈ w1ToySupport then 1/14580 else 0)

/-- T3: selected-regime moment transfer from the true joint experiment to the
existing same-regime extension. For fixed H, sum out assignments outside the
selected regime using normalized CR masses; those coordinates do not occur in
any of the four statistics. For the low regime also complement the first-stage
set. Equality of first moments for arbitrary functions of the selected draws
implies the variance equality by applying it to the centered square.
This leaf covers arbitrary real schedules a,b, not just the numerical examples.
About 180–300 lines. -/
def T3_L2 : Prop :=
  ∀ (high : Bool) (a b : Fin 3 → ℝ),
    let m := if high then 2 else 1
    let n : Fin 6 → ℕ := fun _ => 3
    let law := selectedLaw n 3 (fun _ => crMass 3 m)
    expect w1ToyMass (w1ToyPoint high a b) =
      expect law (selectedMean 3 (fun _ => directGroup a b)) ∧
    variance w1ToyMass (w1ToyPoint high a b) =
      variance law (selectedMean 3 (fun _ => directGroup a b)) ∧
    expect w1ToyMass (w1ToyVest high a b) =
      expect law (directVarianceEstimate (n := n) 3 (fun _ => a) (fun _ => b)) ∧
    expect w1ToyMass (w1ToySampleVar high a b) =
      expect law (fun w => rawSampleVar w.1 (fun g => directGroup a b (w.2 g)))

private theorem mean_const_fin {n : ℕ} (hn : 0 < n) (c : ℝ) :
    mean (fun _ : Fin n => c) = c := by
  simp [mean, ne_of_gt (Nat.cast_pos.mpr hn)]

private theorem coMembers_unconditional (p : ℝ) (i : Fin 4) :
    expect (bernoulli p) (coMembers i) = 3*p := by
  change AronowAudit.P045.expect (AronowAudit.P045.bernoulli p)
    (fun z => ∑ j ∈ univ.erase i, AronowAudit.P045.bit (z j)) = _
  rw [AronowAudit.P045.expect_finset_sum]
  have he (j : Fin 4) : AronowAudit.P045.expect (AronowAudit.P045.bernoulli p)
      (fun z => AronowAudit.P045.bit (z j)) = p := by
    rw [AronowAudit.P045.bernoulli_coordinate_expect]
    simp [AronowAudit.P045.bit]
  simp_rw [he]
  simp

private theorem witness_targets : w1WitnessTargets := by
  have hm (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (b : Bool) :
      mean (fun i : Fin 4 => marginal (bernoulli p) coMembers i b) = 3*p := by
    have hi (i : Fin 4) := AronowAudit.P045.co_members_marginal_four p hp hp1 i b
    change mean (fun i : Fin 4 => AronowAudit.P045.marginal (AronowAudit.P045.bernoulli p)
      AronowAudit.P045.coMembers i b) = _
    simp_rw [hi]
    exact mean_const_fin (by norm_num) _
  have ho (p : ℝ) : mean (fun i : Fin 4 => expect (bernoulli p) (coMembers i)) = 3*p := by
    simp_rw [coMembers_unconditional]
    exact mean_const_fin (by norm_num) _
  refine ⟨fun p _ _ i => coMembers_unconditional p i, ?_, ?_, ?_, ?_⟩
  · intro p hp hp1 b
    refine ⟨hm p hp hp1 b, ?_, ho p, ?_⟩
    · rw [hm p hp hp1 b, mean_const_fin (by norm_num)]
    · rw [ho p, mean_const_fin (by norm_num)]
  · intro b
    constructor <;> rw [hm _ (by norm_num) (by norm_num)] <;> norm_num
  · intro b c
    rw [hm _ (by norm_num) (by norm_num), hm _ (by norm_num) (by norm_num)]
    norm_num
  · rw [ho, ho]; norm_num

/-- The whole T1 certificate; only the new conditional calculation is a leaf. -/
theorem T1_assembly (h1 : T1_L1) : T1WholeStatement := by
  refine ⟨retained_T1, witness_targets, ?_, h1⟩
  intro z
  have hd := AronowAudit.P045.four_arm_domains z
  refine ⟨hd.1, hd.2, ?_, ?_⟩
  · intro h
    have he := AronowAudit.P045.co_members_arm_mean z true (hd.1.mpr h)
    change armMean coMembers true z = (treatedCount z : ℝ)-bit true at he
    simpa only [bit, ite_true] using he
  · intro h
    have he := AronowAudit.P045.co_members_arm_mean z false (hd.2.mpr h)
    change armMean coMembers false z = (treatedCount z : ℝ)-bit false at he
    simpa only [bit, Bool.false_eq_true, ite_false, sub_zero] using he

/-- Coupled first-stage unbiasedness and all repairs; only finite conditional averaging is new. -/
theorem T2_assembly (h1 : T2_L1) : T2WholeStatement := by
  rcases retained_T2 with ⟨hbern, _, hcr, _, _, hoverall, _, _, _⟩
  have hsingle : ∀ (G C : ℕ), 0 < C → C ≤ G → ∀ (n : Fin G → ℕ), (∀ g, 0 < n g) →
      ∀ p : ℝ, 0 < p → p < 1 →
      ∀ (Q : Finset (Fin G) → Design (GroupAssignments n)),
      w1CoordinateLaw C true Q (fun _ => bernoulli p) →
      ∀ (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ) b,
      expect (w1JointMass C Q) (w1RegimeMean C true (fun g => groupHT p (y g) b)) =
        w1ArmTarget (fun _ => bernoulli p) y b := by
    intro G C hC hCG n hn p hp hp1 Q hc y b
    rw [h1 G C hCG n true hC Q _ hc]
    apply congrArg mean
    funext g
    exact (hbern (hn g) p hp hp1 (y g) b).2
  have hbernJoint : w1BernoulliJointResult := by
    intro G C hC hCG n hn p hp Q hc y
    apply contrasts_of_means
    intro high b
    have hcount : 0 < w1RegimeCount G C high := by
      cases high <;> simp [w1RegimeCount] <;> omega
    rw [h1 G C (le_of_lt hCG) n high hcount Q _ (hc high)]
    apply congrArg mean
    funext g
    exact (hbern (hn g) (p high) (hp high).1 (hp high).2 (y g) b).2
  have hcrJoint : w1CRJointResult := by
    intro G C hC hCG n k hk Q hc y
    refine ⟨?_, coupled_cr_domains Q k hk hc⟩
    apply contrasts_of_means
    intro high b
    have hcount : 0 < w1RegimeCount G C high := by
      cases high <;> simp [w1RegimeCount] <;> omega
    rw [h1 G C (le_of_lt hCG) n high hcount Q _ (hc high)]
    apply congrArg mean
    funext g
    exact hcr (hk high g).1 (hk high g).2 (y g) b
  have hcrSingle : w1CRSingleResult := by
    intro G C hC hCG n k hk Q hc y b
    rw [h1 G C hCG n true hC Q _ hc]
    apply congrArg mean
    funext g
    exact hcr (hk g).1 (hk g).2 (y g) b
  have hOJoint : w1OverallJointResult := by
    intro G C hC hCG n hn q Q hc y
    have he (high : Bool) :
        expect (w1JointMass C Q) (w1RegimeMean C high (fun g => groupOverall (y g))) =
        mean (fun g => mean (fun i => expect (q high g).mass (y g i))) := by
      have hcount : 0 < w1RegimeCount G C high := by
        cases high <;> simp [w1RegimeCount] <;> omega
      rw [h1 G C (le_of_lt hCG) n high hcount Q _ (hc high)]
      apply congrArg mean
      funext g
      exact hoverall (hn g) (q high g) (y g)
    rw [sap_expect_sub, he true, he false]
  have hOSingle : w1OverallSingleResult := by
    intro G C hC hCG n hn q Q hc y
    rw [h1 G C hCG n true hC Q _ hc]
    apply congrArg mean
    funext g
    exact hoverall (hn g) (q g) (y g)
  have hlocal (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (b : Bool) :
      expect (bernoulli p) (groupHT p (coMembers (n := 4)) b) = 3*p := by
    have h := AronowAudit.P045.co_members_group_ht_expectation p hp hp1
    cases b
    · exact h.2.1
    · exact h.1
  have he (high b : Bool) :
      expect bernoulliWitnessMass (fun w =>
        groupHT (if high then 1/2 else 1/4) coMembers b (if high then witnessHigh w else witnessLow w)) =
      if high then 3/2 else 3/4 := by
    cases high
    · change AronowAudit.P045.expect AronowAudit.P045.bernoulliWitnessMass
        (fun w => AronowAudit.P045.groupHT (1/4) AronowAudit.P045.coMembers b (AronowAudit.P045.witnessLow w)) = 3/4
      rw [AronowAudit.P045.witness_low_expect]
      have h := hlocal (1/4) (by norm_num) (by norm_num) b
      norm_num at h ⊢
      exact h
    · change AronowAudit.P045.expect AronowAudit.P045.bernoulliWitnessMass
        (fun w => AronowAudit.P045.groupHT (1/2) AronowAudit.P045.coMembers b (AronowAudit.P045.witnessHigh w)) = 3/2
      rw [AronowAudit.P045.witness_high_expect]
      have h := hlocal (1/2) (by norm_num) (by norm_num) b
      norm_num at h ⊢
      exact h
  refine ⟨retained_T2, ratio_failure, hsingle, hbernJoint, hcrJoint, hOJoint,
    hcrSingle, hOSingle, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n k hk hkn z hz b
    exact cr_arm_denominator hk hkn z hz b
  · intro n p y b z hz
    have hall : ∀ i, z i ≠ b := by simpa [armExists] using hz
    simp [groupHT, hall]
  · intro k hk i b
    have hp : (0 : ℝ) < (k.val : ℝ)/4 := by positivity
    have hp1 : (k.val : ℝ)/4 < 1 := by
      have h : (k.val : ℝ) < 4 := by exact_mod_cast k.isLt
      linarith
    have h := AronowAudit.P045.co_members_marginal_four ((k.val : ℝ)/4) hp hp1 i b
    change marginal (bernoulli ((k.val : ℝ)/4)) coMembers i b = 3*((k.val : ℝ)/4) at h
    rw [h]
    ring
  · intro high
    rw [sap_expect_sub, he high true, he high false]
    simp
  · have hh := he true false
    have hl := he false false
    simp only [ite_true, Bool.false_eq_true, ite_false] at hh hl
    rw [sap_expect_sub, hh, hl]
    norm_num
  · have hh := he true true
    have hl := he false false
    simp only [ite_true, Bool.false_eq_true, ite_false] at hh hl
    rw [sap_expect_sub, hh, hl]
    norm_num

/-- Joint-design numerical counterexample, obtained from local moments and the selected-regime transfer. -/
theorem T3_assembly (h1 : T3_L1) (h2 : T3_L2) : T3WholeStatement := by
  rcases retained_T3 with ⟨hold, hlocal⟩
  dsimp only at hold hlocal
  rcases hold with ⟨hadd, hψV, hψE, hφV, hφE, hupV, hupE⟩
  have hAdd (high : Bool) :
      expect w1ToyMass (w1ToyPoint high (fun i => w1ToyBaseline i+1) w1ToyBaseline) = 1 ∧
      variance w1ToyMass (w1ToyPoint high (fun i => w1ToyBaseline i+1) w1ToyBaseline) = 1/2 ∧
      expect w1ToyMass (w1ToyVest high (fun i => w1ToyBaseline i+1) w1ToyBaseline) = 1/3 := by
    have hm : (if high then 2 else 1 : ℕ) ∈ ({1,2} : Finset ℕ) := by cases high <;> simp
    have h := hadd _ hm
    have ht := h2 high (fun i => w1ToyBaseline i+1) w1ToyBaseline
    exact ⟨ht.1.trans h.1, ht.2.1.trans h.2.1, ht.2.2.1.trans h.2.2⟩
  have hs (high : Bool) :
      expect w1ToyMass (w1ToySampleVar high (fun i => w1ToyBaseline i+1) w1ToyBaseline) = 3/2 := by
    have hm : (if high then 2 else 1 : ℕ) ∈ ({1,2} : Finset ℕ) := by cases high <;> simp
    exact (h2 high _ _).2.2.2 |>.trans (toy_sample_variance _ hm)
  refine ⟨retained_T3, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, ?_,
    (h2 true _ _).2.1.trans hψV, (h2 true _ _).2.2.1.trans hψE,
    (h2 false _ _).2.1.trans hφV, (h2 false _ _).2.2.1.trans hφE,
    (h2 true _ _).2.1.trans hupV, (h2 true _ _).2.2.1.trans hupE,
    by norm_num, by norm_num, by norm_num⟩
  intro high
  dsimp only
  have hl := toy_local high
  dsimp only at hl
  refine ⟨?_, ?_, hl.1, hl.2.1, hl.2.2.1, hl.2.2.2,
    (hAdd high).1, (hAdd high).2.1, hs high, (hAdd high).2.2, ?_, ?_⟩
  · norm_num [mean, w1ToyBaseline]
  · norm_num [mean, w1ToyBaseline]
  · rw [(hAdd high).2.2, (hAdd high).2.1]; norm_num
  · rw [(hAdd high).2.2, (hAdd high).2.1]; norm_num

/-- Complete finite all-control witness; there is no new mathematical leaf. -/
theorem T5_assembly : T5WholeStatement := by
  refine ⟨retained_T5, ?_, ?_, ?_, by norm_num⟩
  · intro n A z i
    have h := AronowAudit.P045.full_neighborhood_events (SAP.P045a.Bridge.network A) z i
    exact ⟨h.1, h.2.1⟩
  · intro i
    fin_cases i
    all_goals refine ⟨by norm_num [neighborhood, edge2, Fin.univ_succ,
      Finset.filter_insert, Finset.filter_singleton], ?_⟩
    all_goals intro k
    all_goals fin_cases k
    all_goals norm_num [w1TwoAssignment, neighborhoodCount, neighborhood, edge2,
      allTreated, badAllControl, allControl, Fin.univ_succ,
      Finset.filter_insert, Finset.filter_singleton]
  · intro k
    fin_cases k <;>
      norm_num [w1TwoAssignment, neighborhood, neighborhoodCount, edge2, badAllControl,
        allControl, allTreated, fullHT, linear2, threshold2, expect, prob, mean, bit, bernoulli,
        AronowAudit.P045.sum_tuple_succ, Fin.sum_univ_succ, Fin.prod_univ_succ,
        Fin.univ_succ, Finset.filter_insert, Finset.filter_singleton]

/-- Complete finite storage-order witness, including both complete deletion laws. -/
theorem T7_assembly : T7WholeStatement := by
  have hU : upperCells 4 = [(0,1),(0,2),(1,2),(0,3),(1,3),(2,3)] := by decide
  have hL : lowerCells 4 = [(1,0),(2,0),(3,0),(2,1),(3,1),(3,2)] := by decide
  have hz (f : Bool) : w1RemovalOutput f true = (fun _ _ => 0) := by
    funext i j
    cases f <;> fin_cases i <;> fin_cases j <;>
      norm_num [w1RemovalOutput, faultyCopy, singleEdge4, hU, hL, List.idxOf_cons]
  have hn (f : Bool) : w1RemovalOutput f false ≠ (fun _ _ => 0) := by
    intro h
    have he := congrFun (congrFun h 0) 3
    cases f <;> norm_num [w1RemovalOutput, faultyCopy, singleEdge4] at he
  refine ⟨retained_T7, by decide, by decide, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [faultyCopy, singleEdge4, hU, hL, List.idxOf_cons]
  · intro q hq hq1 f
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro b; cases b <;> simp <;> linarith
    · simp [Fintype.univ_bool]
    · intro M
      simp [prob, expect, Fintype.univ_bool, hz, add_comm]
    · simp [prob, expect, Fintype.univ_bool, hz, Ne.symm (hn f)]
    · simp [prob, expect, Fintype.univ_bool, hz, hn f]
    · intro M hM hM0
      simp [prob, expect, Fintype.univ_bool, hz, Ne.symm hM, Ne.symm hM0]

end
end SAP.P045a.WH.W1
