import SAP.P045a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a.WH.W1.P.T1_L1

private theorem local_arm_probability (p : ℝ) (b : Bool) :
    AronowAudit.P045.prob (AronowAudit.P045.bernoulli (n := 4) p)
      (AronowAudit.P045.armExists (n := 4) b) =
    AronowAudit.P045.prob (AronowAudit.P045.binomial4 p) (AronowAudit.P045.countDomain b) := by
  classical
  have hd : ∀ z : AronowAudit.P045.Assignment 4,
      AronowAudit.P045.armExists b z ↔
        AronowAudit.P045.countDomain b (AronowAudit.P045.countIndex4 z) := by
    intro z
    cases b
    · change AronowAudit.P045.armExists false z ↔
        (AronowAudit.P045.countIndex4 z).val < 4
      simpa only [AronowAudit.P045.countIndex4] using
        (AronowAudit.P045.four_arm_domains z).2
    · change AronowAudit.P045.armExists true z ↔
        0 < (AronowAudit.P045.countIndex4 z).val
      simpa only [AronowAudit.P045.countIndex4] using
        (AronowAudit.P045.four_arm_domains z).1
  have hf : (fun z : AronowAudit.P045.Assignment 4 =>
      if AronowAudit.P045.armExists b z then (1 : ℝ) else 0) =
      (fun z => if AronowAudit.P045.countDomain b (AronowAudit.P045.countIndex4 z) then 1 else 0) := by
    funext z
    simp only [← hd z]
  unfold AronowAudit.P045.prob
  change AronowAudit.P045.expect (AronowAudit.P045.bernoulli p)
      (fun z : AronowAudit.P045.Assignment 4 =>
        if AronowAudit.P045.armExists b z then (1 : ℝ) else 0) = _
  rw [hf, AronowAudit.P045.bernoulli4_count_law p
    (fun k => if AronowAudit.P045.countDomain b k then 1 else 0)]

private theorem local_both_arm_conditional (p : ℝ) (b : Bool) :
    AronowAudit.P045.condMean (AronowAudit.P045.bernoulli (n := 4) p)
      (fun z : AronowAudit.P045.Assignment 4 =>
        AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z)
      (AronowAudit.P045.armMean AronowAudit.P045.coMembers b) =
    AronowAudit.P045.condMean (AronowAudit.P045.binomial4 p)
      (fun k : Fin 5 => 0 < k.val ∧ k.val < 4) (AronowAudit.P045.countArm b) := by
  classical
  have hd (z : AronowAudit.P045.Assignment 4) :
      (AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z) ↔
        (0 < (AronowAudit.P045.countIndex4 z).val ∧
          (AronowAudit.P045.countIndex4 z).val < 4) := by
    change (AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z) ↔
      (0 < (AronowAudit.P045.countIndex4 z).val ∧
        (AronowAudit.P045.countIndex4 z).val < 4)
    rw [(AronowAudit.P045.four_arm_domains z).1,
      (AronowAudit.P045.four_arm_domains z).2]
    rfl
  have hf : (fun z : AronowAudit.P045.Assignment 4 =>
      @ite ℝ (AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z)
        (Classical.propDecidable _) (AronowAudit.P045.armMean AronowAudit.P045.coMembers b z) 0) =
      (fun z => @ite ℝ (0 < (AronowAudit.P045.countIndex4 z).val ∧
          (AronowAudit.P045.countIndex4 z).val < 4) (Classical.propDecidable _)
        (AronowAudit.P045.countArm b (AronowAudit.P045.countIndex4 z)) 0) := by
    funext z
    by_cases h : AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z
    · have hb : AronowAudit.P045.armExists b z := by
        cases b
        · exact h.2
        · exact h.1
      have hc : 0 < (AronowAudit.P045.countIndex4 z).val ∧
          (AronowAudit.P045.countIndex4 z).val < 4 := (hd z).mp h
      simp only [if_pos h, if_pos hc]
      rw [AronowAudit.P045.co_members_arm_mean z b hb]
      simp [AronowAudit.P045.countArm, AronowAudit.P045.countIndex4,
        AronowAudit.P045.bit]
    · have hc : ¬ (0 < (AronowAudit.P045.countIndex4 z).val ∧
        (AronowAudit.P045.countIndex4 z).val < 4) := fun hc => h ((hd z).mpr hc)
      simp only [if_neg h, if_neg hc]
  have hg : (fun z : AronowAudit.P045.Assignment 4 =>
      @ite ℝ (AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z)
        (Classical.propDecidable _) (1 : ℝ) 0) =
      (fun z => @ite ℝ (0 < (AronowAudit.P045.countIndex4 z).val ∧
          (AronowAudit.P045.countIndex4 z).val < 4) (Classical.propDecidable _) 1 0) := by
    funext z
    by_cases h : AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z
    · have hc := (hd z).mp h
      simp only [if_pos h, if_pos hc]
    · have hc : ¬ (0 < (AronowAudit.P045.countIndex4 z).val ∧
        (AronowAudit.P045.countIndex4 z).val < 4) := fun hc => h ((hd z).mpr hc)
      simp only [if_neg h, if_neg hc]
  have hn : AronowAudit.P045.expect (AronowAudit.P045.bernoulli (n := 4) p)
      (fun z : AronowAudit.P045.Assignment 4 =>
        @ite ℝ (AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z)
          (Classical.propDecidable _) (AronowAudit.P045.armMean AronowAudit.P045.coMembers b z) 0) =
      AronowAudit.P045.expect (AronowAudit.P045.binomial4 p)
        (fun k : Fin 5 => @ite ℝ (0 < k.val ∧ k.val < 4) (Classical.propDecidable _)
          (AronowAudit.P045.countArm b k) 0) := by
    calc
      _ = AronowAudit.P045.expect (AronowAudit.P045.bernoulli (n := 4) p)
          (fun z : AronowAudit.P045.Assignment 4 =>
            @ite ℝ (0 < (AronowAudit.P045.countIndex4 z).val ∧
              (AronowAudit.P045.countIndex4 z).val < 4) (Classical.propDecidable _)
              (AronowAudit.P045.countArm b (AronowAudit.P045.countIndex4 z)) 0) :=
          congrArg (AronowAudit.P045.expect (AronowAudit.P045.bernoulli p)) hf
      _ = _ := AronowAudit.P045.bernoulli4_count_law p
        (fun k : Fin 5 => @ite ℝ (0 < k.val ∧ k.val < 4) (Classical.propDecidable _)
          (AronowAudit.P045.countArm b k) 0)
  have hp : AronowAudit.P045.prob (AronowAudit.P045.bernoulli (n := 4) p)
      (fun z : AronowAudit.P045.Assignment 4 =>
        AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z) =
      AronowAudit.P045.prob (AronowAudit.P045.binomial4 p)
        (fun k : Fin 5 => 0 < k.val ∧ k.val < 4) := by
    unfold AronowAudit.P045.prob
    calc
      _ = AronowAudit.P045.expect (AronowAudit.P045.bernoulli p)
          (fun z : AronowAudit.P045.Assignment 4 =>
            @ite ℝ (0 < (AronowAudit.P045.countIndex4 z).val ∧
              (AronowAudit.P045.countIndex4 z).val < 4) (Classical.propDecidable _) (1 : ℝ) 0) :=
          congrArg (AronowAudit.P045.expect (AronowAudit.P045.bernoulli p)) hg
      _ = _ := AronowAudit.P045.bernoulli4_count_law p
        (fun k : Fin 5 => @ite ℝ (0 < k.val ∧ k.val < 4) (Classical.propDecidable _) (1 : ℝ) 0)
  unfold AronowAudit.P045.condMean
  exact congrArg₂ (fun x y : ℝ => x / y) hn hp

private theorem witness_high_conditional (E : AronowAudit.P045.Assignment 4 → Prop)
    (X : AronowAudit.P045.Assignment 4 → ℝ) :
    AronowAudit.P045.condMean AronowAudit.P045.bernoulliWitnessMass
      (fun w => E (AronowAudit.P045.witnessHigh w))
      (fun w => X (AronowAudit.P045.witnessHigh w)) =
    AronowAudit.P045.condMean (AronowAudit.P045.bernoulli (n := 4) (1/2)) E X := by
  classical
  unfold AronowAudit.P045.condMean AronowAudit.P045.prob
  dsimp
  rw [AronowAudit.P045.witness_high_expect (fun z => if E z then X z else 0),
    AronowAudit.P045.witness_high_expect (fun z => if E z then (1 : ℝ) else 0)]

private theorem witness_low_conditional (E : AronowAudit.P045.Assignment 4 → Prop)
    (X : AronowAudit.P045.Assignment 4 → ℝ) :
    AronowAudit.P045.condMean AronowAudit.P045.bernoulliWitnessMass
      (fun w => E (AronowAudit.P045.witnessLow w))
      (fun w => X (AronowAudit.P045.witnessLow w)) =
    AronowAudit.P045.condMean (AronowAudit.P045.bernoulli (n := 4) (1/4)) E X := by
  classical
  unfold AronowAudit.P045.condMean AronowAudit.P045.prob
  dsimp
  rw [AronowAudit.P045.witness_low_expect (fun z => if E z then X z else 0),
    AronowAudit.P045.witness_low_expect (fun z => if E z then (1 : ℝ) else 0)]

private theorem local_own_arm_values :
    (∀ b, AronowAudit.P045.condMean (AronowAudit.P045.bernoulli (n := 4) (1/2))
      (AronowAudit.P045.armExists b) (AronowAudit.P045.armMean AronowAudit.P045.coMembers b) =
        if b then 17/15 else 28/15) ∧
    (∀ b, AronowAudit.P045.condMean (AronowAudit.P045.bernoulli (n := 4) (1/4))
      (AronowAudit.P045.armExists b) (AronowAudit.P045.armMean AronowAudit.P045.coMembers b) =
        if b then 81/175 else 84/85) := by
  rcases AronowAudit.P045.bernoulli_count_counterexample with
    ⟨_, _, hht, hhc, hlt, hlc, _, _, _, _, _⟩
  constructor
  · intro b
    rw [AronowAudit.P045.bernoulli_arm_count_conditional]
    cases b
    · change AronowAudit.P045.condMean (AronowAudit.P045.binomial4 (1/2))
        (fun k : Fin 5 => k.val < 4) (AronowAudit.P045.countArm false) = 28/15
      exact hhc
    · change AronowAudit.P045.condMean (AronowAudit.P045.binomial4 (1/2))
        (fun k : Fin 5 => 0 < k.val) (AronowAudit.P045.countArm true) = 17/15
      exact hht
  · intro b
    rw [AronowAudit.P045.bernoulli_arm_count_conditional]
    cases b
    · change AronowAudit.P045.condMean (AronowAudit.P045.binomial4 (1/4))
        (fun k : Fin 5 => k.val < 4) (AronowAudit.P045.countArm false) = 84/85
      exact hlc
    · change AronowAudit.P045.condMean (AronowAudit.P045.binomial4 (1/4))
        (fun k : Fin 5 => 0 < k.val) (AronowAudit.P045.countArm true) = 81/175
      exact hlt

private theorem local_both_arm_values :
    (∀ b, AronowAudit.P045.condMean (AronowAudit.P045.bernoulli (n := 4) (1/2))
      (fun z : AronowAudit.P045.Assignment 4 =>
        AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z)
      (AronowAudit.P045.armMean AronowAudit.P045.coMembers b) = if b then 1 else 2) ∧
    (∀ b, AronowAudit.P045.condMean (AronowAudit.P045.bernoulli (n := 4) (1/4))
      (fun z : AronowAudit.P045.Assignment 4 =>
        AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z)
      (AronowAudit.P045.armMean AronowAudit.P045.coMembers b) = if b then 13/29 else 42/29) := by
  rcases AronowAudit.P045.bernoulli_count_counterexample with
    ⟨_, _, _, _, _, _, hbt, hbc, hlt, hlc, _⟩
  constructor
  · intro b
    rw [local_both_arm_conditional]
    cases b
    · simpa using hbc
    · simpa using hbt
  · intro b
    rw [local_both_arm_conditional]
    cases b
    · simpa using hlc
    · simpa using hlt

private theorem source_leaf :
    AronowAudit.P045.condMean (AronowAudit.P045.bernoulli (n := 4) (1/2))
        (fun z : AronowAudit.P045.Assignment 4 =>
          AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z)
        (AronowAudit.P045.armMean AronowAudit.P045.coMembers true) = 1 ∧
    AronowAudit.P045.condMean (AronowAudit.P045.bernoulli (n := 4) (1/2))
        (fun z : AronowAudit.P045.Assignment 4 =>
          AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z)
        (AronowAudit.P045.armMean AronowAudit.P045.coMembers false) = 2 ∧
    AronowAudit.P045.condMean (AronowAudit.P045.bernoulli (n := 4) (1/4))
        (fun z : AronowAudit.P045.Assignment 4 =>
          AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z)
        (AronowAudit.P045.armMean AronowAudit.P045.coMembers true) = 13/29 ∧
    AronowAudit.P045.condMean (AronowAudit.P045.bernoulli (n := 4) (1/4))
        (fun z : AronowAudit.P045.Assignment 4 =>
          AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z)
        (AronowAudit.P045.armMean AronowAudit.P045.coMembers false) = 42/29 ∧
    (∀ high b : Bool,
      let p : ℝ := if high then 1/2 else 1/4
      AronowAudit.P045.prob AronowAudit.P045.bernoulliWitnessMass
          (AronowAudit.P045.witnessDomain b high) =
        AronowAudit.P045.prob (AronowAudit.P045.bernoulli (n := 4) p)
          (AronowAudit.P045.armExists b) ∧
      0 < AronowAudit.P045.prob AronowAudit.P045.bernoulliWitnessMass
          (AronowAudit.P045.witnessDomain b high) ∧
      AronowAudit.P045.condMean AronowAudit.P045.bernoulliWitnessMass
          (AronowAudit.P045.witnessDomain b high) (AronowAudit.P045.witnessArm b high) =
        (if high then (if b then 17/15 else 28/15) else
          (if b then 81/175 else 84/85)) ∧
      AronowAudit.P045.condMean AronowAudit.P045.bernoulliWitnessMass
          (fun w => AronowAudit.P045.witnessDomain true high w ∧
            AronowAudit.P045.witnessDomain false high w)
          (AronowAudit.P045.witnessArm b high) =
        (if high then (if b then 1 else 2) else (if b then 13/29 else 42/29))) := by
  rcases local_both_arm_values with ⟨hbh, hbl⟩
  refine ⟨hbh true, hbh false, hbl true, hbl false, ?_⟩
  intro high b
  dsimp
  have hprob : AronowAudit.P045.prob AronowAudit.P045.bernoulliWitnessMass
      (AronowAudit.P045.witnessDomain b high) =
      AronowAudit.P045.prob
        (AronowAudit.P045.bernoulli (n := 4) (if high then 1/2 else 1/4))
        (AronowAudit.P045.armExists b) := by
    cases high
    · change AronowAudit.P045.prob AronowAudit.P045.bernoulliWitnessMass
        (fun w => AronowAudit.P045.armExists b (AronowAudit.P045.witnessLow w)) = _
      unfold AronowAudit.P045.prob
      dsimp
      rw [AronowAudit.P045.witness_low_expect
        (fun z => if AronowAudit.P045.armExists b z then (1 : ℝ) else 0)]
    · change AronowAudit.P045.prob AronowAudit.P045.bernoulliWitnessMass
        (fun w => AronowAudit.P045.armExists b (AronowAudit.P045.witnessHigh w)) = _
      unfold AronowAudit.P045.prob
      dsimp
      rw [AronowAudit.P045.witness_high_expect
        (fun z => if AronowAudit.P045.armExists b z then (1 : ℝ) else 0)]
  have hpos : 0 < AronowAudit.P045.prob AronowAudit.P045.bernoulliWitnessMass
      (AronowAudit.P045.witnessDomain b high) := by
    rw [hprob, local_arm_probability]
    cases high <;> cases b <;>
      norm_num [AronowAudit.P045.prob, AronowAudit.P045.expect,
        AronowAudit.P045.countDomain, AronowAudit.P045.binomial4,
        Fin.sum_univ_succ, Nat.choose]
  have hown : AronowAudit.P045.condMean AronowAudit.P045.bernoulliWitnessMass
      (AronowAudit.P045.witnessDomain b high) (AronowAudit.P045.witnessArm b high) =
      (if high then (if b then 17/15 else 28/15) else
        (if b then 81/175 else 84/85)) := by
    cases high with
    | false =>
        change AronowAudit.P045.condMean AronowAudit.P045.bernoulliWitnessMass
          (fun w => AronowAudit.P045.armExists b (AronowAudit.P045.witnessLow w))
          (fun w => AronowAudit.P045.armMean AronowAudit.P045.coMembers b
            (AronowAudit.P045.witnessLow w)) = _
        rw [witness_low_conditional]
        exact local_own_arm_values.2 b
    | true =>
        change AronowAudit.P045.condMean AronowAudit.P045.bernoulliWitnessMass
          (fun w => AronowAudit.P045.armExists b (AronowAudit.P045.witnessHigh w))
          (fun w => AronowAudit.P045.armMean AronowAudit.P045.coMembers b
            (AronowAudit.P045.witnessHigh w)) = _
        rw [witness_high_conditional]
        exact local_own_arm_values.1 b
  have hboth : AronowAudit.P045.condMean AronowAudit.P045.bernoulliWitnessMass
      (fun w => AronowAudit.P045.witnessDomain true high w ∧
        AronowAudit.P045.witnessDomain false high w)
      (AronowAudit.P045.witnessArm b high) =
      (if high then (if b then 1 else 2) else (if b then 13/29 else 42/29)) := by
    cases high with
    | false =>
        change AronowAudit.P045.condMean AronowAudit.P045.bernoulliWitnessMass
          (fun w => AronowAudit.P045.armExists true (AronowAudit.P045.witnessLow w) ∧
            AronowAudit.P045.armExists false (AronowAudit.P045.witnessLow w))
          (fun w => AronowAudit.P045.armMean AronowAudit.P045.coMembers b
            (AronowAudit.P045.witnessLow w)) = _
        simpa using (witness_low_conditional
          (fun z => AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z)
          (AronowAudit.P045.armMean AronowAudit.P045.coMembers b)).trans
            (local_both_arm_values.2 b)
    | true =>
        change AronowAudit.P045.condMean AronowAudit.P045.bernoulliWitnessMass
          (fun w => AronowAudit.P045.armExists true (AronowAudit.P045.witnessHigh w) ∧
            AronowAudit.P045.armExists false (AronowAudit.P045.witnessHigh w))
          (fun w => AronowAudit.P045.armMean AronowAudit.P045.coMembers b
            (AronowAudit.P045.witnessHigh w)) = _
        simpa using (witness_high_conditional
          (fun z => AronowAudit.P045.armExists true z ∧ AronowAudit.P045.armExists false z)
          (AronowAudit.P045.armMean AronowAudit.P045.coMembers b)).trans
            (local_both_arm_values.1 b)
  exact ⟨hprob, hpos, hown, hboth⟩

end SAP.P045a.WH.W1.P.T1_L1

theorem SAP.P045a.WH.W1.T1_L1_proof : SAP.P045a.WH.W1.T1_L1 := by
  unfold SAP.P045a.WH.W1.T1_L1
  exact SAP.P045a.WH.W1.P.T1_L1.source_leaf
