import SAP.P045a.Defs.WholeW2
import SAP.P045a.Bridge
import AronowAudit.P045.Wave1.Gap.GLP041P042P045P045B1
import AronowAudit.P045.Wave1.Gap.FidP045

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a.WH.W2
open SAP.P045a.Bridge
noncomputable section

/-- Complete support of the two terminal centre laws on the four-path.
For the coded law use ClusterSampler.n5_proof applied to n3_proof: every nonzero trace is
[1], [2], [3,0], or 0^(r+1) followed by a nonzero vertex. Pass zero terms through the finite
inner sum and then through the series. For the repaired law, a nonzero product forces every
draw to be unmarked; hence it is a greedy run. Use ClusterSampler.n1_proof and
greedy_run_properties, and enumerate the sixteen subsets to identify the three nets.
Alternatively adapt the repaired trace classification in GLP041P042P045P045B1.lean.
No normalization or convergence assumption is required to prove that an identically zero
series is zero. Expected size: 100–180 lines. -/
def T10_L1 : Prop :=
  (∀ S : Finset (Fin 4), S ∉ fourPathCodedCentreSets →
    terminalCentres pathDistance 3 true S = 0) ∧
  (∀ S : Finset (Fin 4), S ∉ fourPathRepairedCentreSets →
    terminalCentres pathDistance 3 false S = 0)

/-- Convergence of every terminal-centre series used for this witness.
Use ClusterSampler.n6_proof and n7_proof with n4_proof and the n5_proof/n3_proof
classification for the singleton and {0,3} series. For {0,1} and {0,2}, each length t>=2
has exactly one contributing retry trace, of mass (1/4)^t; all other coded sets have zero
terms. The repaired traces are just [1], [2], [0,3], [3,0], so their length series have
finite support. Apply summable_geometric_of_lt_one and finite-support summability.
The private pair_inner and repaired_inner proofs in GLP041P042P045P045B1.lean are templates;
their private declarations are not callable donors. Expected size: 150–250 lines. -/
def T10_L2 : Prop :=
  ∀ coded : Bool, ∀ S : Finset (Fin 4), Summable (fourPathLengthMass coded S)

/-- Nearest-centre geometry and the repaired cluster-coin support.
Compute the nearest centre for each of four vertices for the five supported centre sets,
respecting the smallest-index tie rule at vertex 1 with centres {0,2}. A pair's toList is
either order (Finset.toList_insert and List.perm_pair); evaluating mergeSort gives the same
answer for both orders. The two singleton sets give one cluster. For an unlisted repaired
vector either z0 differs from z1 or z2 differs from z3; the event defining clusterProb is
then empty for each of {0,3}, {1}, {2}. Unfold prob and sum zero terms.
The private nearest_pairs, coin_single and coin_03 proofs in GLP041P042P045P045B1.lean are
templates. Expected size: 80–150 lines. -/
def T10_L3 : Prop :=
  (nearestPartition (pathDistance (n := 4)) {0, 1} = {{0}, {1, 2, 3}} ∧
    nearestPartition (pathDistance (n := 4)) {0, 2} = {{0, 1}, {2, 3}} ∧
    nearestPartition (pathDistance (n := 4)) {0, 3} = {{0, 1}, {2, 3}} ∧
    nearestPartition (pathDistance (n := 4)) {1} = {{0, 1, 2, 3}} ∧
    nearestPartition (pathDistance (n := 4)) {2} = {{0, 1, 2, 3}}) ∧
  (∀ z : Assignment 4, z ∉ fourPathRepairedVectors →
    ∀ S ∈ fourPathRepairedCentreSets, clusterProb pathDistance S (1/2) z = 0)

/-- The full sampler counterexample follows from terminal support, convergence and geometry. -/
theorem T10_assembly (h1 : T10_L1) (h2 : T10_L2) (h3 : T10_L3) : T10WholeStatement := by
  have hbase : T10Statement := AronowAudit.P045.Wave1.cluster_sampler_counterexample_proof
  have hdata := hbase
  rcases hdata with ⟨h01, h02, h03, hs1, hs2, htotal, hfail,
    hz0, hz1, hz2, hz3, hz4, hz5, hzoff, hr03, hrs1, hrs2,
    hrz0, hrz1, hrz2, hrz3, hrz4, hrz5⟩
  have hc := h1.1
  have hr := h1.2
  have hp := h3.1
  have hweighted (F : Finset (Fin 4) → ℝ) :
      (∑ S : Finset (Fin 4), terminalCentres pathDistance 3 true S * F S) =
        1/12 * F {0,1} + 1/12 * F {0,2} + 1/3 * F {0,3} +
          1/4 * F {1} + 1/4 * F {2} := by
    have htrim : (∑ S : Finset (Fin 4), terminalCentres pathDistance 3 true S * F S) =
        ∑ S ∈ fourPathCodedCentreSets, terminalCentres pathDistance 3 true S * F S := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hS
      rw [hc S hS, zero_mul]
    rw [htrim]
    simp +decide [fourPathCodedCentreSets, h01, h02, h03, hs1, hs2]
    ring
  have hprob (E : Finset (Fin 4) → Prop) :
      prob (terminalCentres (pathDistance (n := 4)) 3 true) E =
        1/12 * (if E {0,1} then 1 else 0) + 1/12 * (if E {0,2} then 1 else 0) +
        1/3 * (if E {0,3} then 1 else 0) + 1/4 * (if E {1} then 1 else 0) +
        1/4 * (if E {2} then 1 else 0) := by
    simpa only [prob, expect] using hweighted (fun S => if E S then 1 else 0)
  have hrweighted (F : Finset (Fin 4) → ℝ) :
      (∑ S : Finset (Fin 4), terminalCentres pathDistance 3 false S * F S) =
        1/2 * F {0,3} + 1/4 * F {1} + 1/4 * F {2} := by
    have htrim : (∑ S : Finset (Fin 4), terminalCentres pathDistance 3 false S * F S) =
        ∑ S ∈ fourPathRepairedCentreSets, terminalCentres pathDistance 3 false S * F S := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hS
      rw [hr S hS, zero_mul]
    rw [htrim]
    simp +decide [fourPathRepairedCentreSets, hr03, hrs1, hrs2]
    ring
  refine ⟨hbase, ?_, ?_, h2, hc, hr, ?_, ?_, ?_⟩
  · decide
  · refine ⟨?_, ?_, ?_⟩
    · exact AronowAudit.P045.four_path_coded_draws
    · intro v
      have hR : (univ : Finset (Fin 4)) \ marked pathDistance 3 {3} = {0} := by decide
      fin_cases v <;> norm_num [centreDraw, hR]
    · intro j hj
      have hm (r : ℕ) : traceMass pathDistance 3 true
          (List.replicate (r+1) (0 : Fin 4) ++ [j]) = (1/4 : ℝ)^(r+2) :=
        AronowAudit.P045.four_path_repeat_trace_mass r j hj
      refine ⟨hm, ?_, ?_⟩
      · simp_rw [hm, pow_add]
        exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/4)
          (by norm_num : (1/4 : ℝ) < 1)).mul_right _
      · have hsum : (∑' r : ℕ, traceMass pathDistance 3 true
            (List.replicate (r+1) (0 : Fin 4) ++ [j])) = 1/12 :=
          AronowAudit.P045.four_path_repeat_trace_sum j hj
        have hd : centreDraw pathDistance 3 true ∅ (0 : Fin 4) = 1/4 :=
          (AronowAudit.P045.four_path_coded_draws (0 : Fin 4)).1
        rw [hsum, hd]
        norm_num
  · refine ⟨?_, ?_, ?_, ?_⟩ <;>
      rw [hprob] <;> simp +decide [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2] <;>
      norm_num
  · unfold epsilonNet separated covers fourPathRepairedCentreSets
    decide
  · refine ⟨?_, ?_, ?_⟩
    · have h := hrweighted (fun _ => 1)
      norm_num at h ⊢
      exact h
    · intro z hz
      unfold clusteredTreatment
      apply Finset.sum_eq_zero
      intro S _
      by_cases hS : S ∈ fourPathRepairedCentreSets
      · rw [h3.2 z hz S hS, mul_zero]
      · rw [hr S hS, zero_mul]
    · intro heq
      have hv := congrFun heq ![true, false, false, false]
      rw [hz4, hrz4] at hv
      norm_num at hv

set_option maxRecDepth 4096 in
/-- All omitted ten-cycle clauses are finite counts, arithmetic, or existing HT calculations. -/
theorem T12_assembly : T12WholeStatement := by
  have hbase : T12Statement := by
    have h := AronowAudit.P045.naive_denominator_counterexample
    simp only [pairExposureProb_eq, cycleL_fun, cycleR_fun, exposure_pred,
      cycleOut_eq, decode_d11, decode_d10, decode_d01, decode_d00] at h
    exact h
  have hc : treatmentPairs.card = 45 := hbase.1
  have hprobs := hbase.2.1
  have hown (i : Fin 10) : cycleOwnProb i = 1/5 := by
    have hcount : (treatmentPairs.filter (fun e => pairAssignment e i = true)).card = 9 := by
      revert i
      decide
    norm_num [cycleOwnProb, average, Finset.sum_ite, hcount, hc]
  have hall : ∀ i : Fin 10, exposure cycle10 (fun _ => true) i = .d11 := by decide
  have hmu11 : mean (fun i : Fin 10 => cycleOut i .d11) = 2 := by
    norm_num [mean, cycleOut]
  have hmu10 : mean (fun i : Fin 10 => cycleOut i .d10) = 1 := by
    norm_num [mean, cycleOut]
  have hmuall : cycleAllTreatedMean = 2 := by
    simp only [cycleAllTreatedMean, hall]
    exact hmu11
  have hEL : average treatmentPairs cycleL = 11/9 := hbase.2.2.2.2.2.1
  have hER : average treatmentPairs cycleR = 3 := hbase.2.2.2.2.2.2.1
  have hEH : average treatmentPairs cycleHTMean = 2 := hbase.2.2.2.2.2.2.2.1
  refine ⟨hbase, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · intro i
    refine ⟨hown i, ?_, ?_, ?_⟩
    · rw [hown]; norm_num
    · intro d
      cases d <;> norm_num [(hprobs i).1, (hprobs i).2.1,
        (hprobs i).2.2.1, (hprobs i).2.2.2]
    · rw [hown, (hprobs i).1, (hprobs i).2.1]; norm_num
  · intro e
    simp only [hown, cycleL]
  · decide
  · intro e he
    have hcount : ∀ e ∈ treatmentPairs,
        (univ.filter (fun i => exposure cycle10 (pairAssignment e) i = .d11)).card =
          if cycle10 e.1 e.2 then 2 else 0 := by decide
    unfold cycleHTMean mean
    simp_rw [(hprobs _).1]
    simp [Finset.sum_ite, hcount e he]
    cases cycle10 e.1 e.2 <;> norm_num
  · refine ⟨hmuall, hmu11, hmu10, ?_, ?_⟩
    · rw [hER, hmu11, hmu10]; norm_num
    · rw [hEH, hmuall]
  · refine ⟨by rw [hEL, hmuall], by norm_num, ?_⟩
    simp only [hEL, hmuall, hown, (hprobs _).2.1, cycleOut]
    norm_num [mean]

/-- The missing indicator, weight, single-HT and all-treated identities are short glue. -/
theorem T13_assembly : T13WholeStatement := by
  have hbase : T13Statement := by
    refine ⟨?_, ?_, ?_⟩
    · intro n hn p A y hp
      have h := AronowAudit.P045.naive_bias_correction hn (design p) (network A) (outcome y) hp
      simp only [naiveTreated_fun, htTotal_eq, exposureProb_eq, outcome,
        decode_d11, decode_d10] at h
      exact h
    · intro n hn p A y hp z
      have h := AronowAudit.P045.naive_expansion_correct p.mass A.adj (outcome y) z
      simp only [naiveTreated_eq, repairedExpansion_eq] at h
      exact h
    · have h := AronowAudit.P045.spillover_cancellation_instance
      simp only [cancellingOut2_eq, naiveTreated_fun, outcome,
        decode_d11, decode_d10] at h
      exact h
  refine ⟨hbase, ?_⟩
  intro n hn p A y hp
  have hpart := (hbase.1 hn p A y hp).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z i
    unfold exposure
    cases hz : z i <;> by_cases hj : ∃ j, A.adj i j = true ∧ z j = true <;> simp [hj]
  · intro i
    have hnonneg (d : Exposure) : 0 ≤ exposureProb p.mass (exposure A.adj) i d := by
      exact AronowAudit.P045.prob_nonneg (design p) (fun z => exposure A.adj z i = d)
    refine ⟨div_nonneg (hnonneg .d11) (le_of_lt (hp i)),
      div_nonneg (hnonneg .d10) (le_of_lt (hp i)), ?_⟩
    rw [← add_div, ← hpart i, div_self (ne_of_gt (hp i))]
  · intro he
    have ht : expect p.mass (htTotal p.mass (exposure A.adj) y .d11) = ∑ i, y i .d11 :=
      AronowAudit.P045.ht_total_unbiased (design p) (exposure A.adj) y .d11
        (fun i => (he i).1)
    have hd : expect p.mass (fun z => htTotal p.mass (exposure A.adj) y .d11 z / n) =
        expect p.mass (htTotal p.mass (exposure A.adj) y .d11) / n :=
      AronowAudit.P045.expect_div p.mass (htTotal p.mass (exposure A.adj) y .d11) (n : ℝ)
    rw [hd, ht]
    simp only [mean, Fintype.card_fin]
  · intro hiso
    have hall (i : Fin n) : exposure A.adj (fun _ => true) i = .d11 := by
      simp [exposure, hiso i]
    simp only [hall]

/-- General finite-set partition identities and the existing two-stage witness suffice. -/
theorem T15_assembly : T15WholeStatement := by
  have hbase : T15Statement :=
    ⟨AronowAudit.P045.pooled_ratio_correction, AronowAudit.P045.tract_partition,
      AronowAudit.P045.Wave1.tract_mixture_bias_identified⟩
  refine ⟨hbase, ?_, ?_⟩
  · intro G _ H partner m
    dsimp only
    let P := H.filter (fun g => partner g ∈ H)
    let Q := H.filter (fun g => partner g ∉ H)
    have hc : H.card = P.card + Q.card :=
      (Finset.card_filter_add_card_filter_not (s := H) (fun g => partner g ∈ H)).symm
    have hs : (∑ g ∈ H, m g) = (∑ g ∈ P, m g) + (∑ g ∈ Q, m g) :=
      (Finset.sum_filter_add_sum_filter_not H (fun g => partner g ∈ H) m).symm
    have hav : average H m = ((∑ g ∈ P, m g) + (∑ g ∈ Q, m g)) /
        (P.card + Q.card : ℕ) := by rw [average, hs, hc]
    refine ⟨Finset.disjoint_filter_filter_not _ _ _,
      Finset.filter_union_filter_not_eq _ _, hc, hs, ?_, ?_, ?_⟩
    · intro hab
      refine ⟨hav, ?_⟩
      rw [hav]
      exact (AronowAudit.P045.pooled_ratio_correction _ _ _ _ hab).1
    · intro ha hb
      change 0 < P.card at ha
      change 0 < Q.card at hb
      have hab : 0 < P.card + Q.card := by omega
      have habR : (0 : ℝ) < (P.card + Q.card : ℕ) := by exact_mod_cast hab
      refine ⟨div_pos (by exact_mod_cast ha) habR,
        div_pos (by exact_mod_cast hb) habR, ?_, ?_⟩
      · rw [← add_div, ← Nat.cast_add, div_self (ne_of_gt habR)]
      · rw [hav]
        exact (AronowAudit.P045.pooled_ratio_correction _ _ _ _ hab).2.1 ha hb
    · intro ha _
      have hP : P = ∅ := Finset.card_eq_zero.mp ha
      change (∑ g ∈ P, m g) = 0 ∧ average H m = (∑ g ∈ Q, m g) / Q.card
      constructor
      · simp only [hP, Finset.sum_empty]
      · rw [hav, hP]
        simp
  · have hE : expect tractTwoStageMass (fun ω => tractDirectEstimator ω.1 ω.2) = 4/5 :=
      AronowAudit.P045.Wave1.tract_mixture_expectation
    rw [hE]
    norm_num

end
end SAP.P045a.WH.W2
