import SAP.P009a.Defs.WholeW4
import SAP.P009a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009a.WH.W4

open Filter
open scoped BigOperators Topology Classical

noncomputable section

/-- All finite ingredients already have project proofs. The remaining steps are transport,
bounded-moment monotonicity, support arithmetic, and exhibiting event preimages. -/
theorem T9_assembly : T9WholeStatement := by
  intro r hr
  obtain ⟨P, hCR, hy, _, hd, havg, hlt, hC1, hCinf, halpha⟩ :=
    AronowAudit.P009.Wave1.exceptional_pair_counterexample_proof r hr
  let E := Bridge.fromProjectExperiment P
  have hb (i : Fin (4*r+2)) (z : TreatmentVector (4*r+2)) :
      0 ≤ E.outcome i z ∧ E.outcome i z ≤ 1 := by
    change 0 ≤ P.outcome i z ∧ P.outcome i z ≤ 1
    rw [hy]
    exact AronowAudit.P009.Wave1.t9_outcome_bounds r hr i z
  have hm (i : Fin (4*r+2)) : armProbability E i true = 1/2 := by
    change AronowAudit.P009.marginal P i true = 1/2
    rw [AronowAudit.P009.CompleteConditional.complete_marginal_true P (2*r+1) hCR i]
    push_cast
    field_simp
    ring
  have hmom (X : TreatmentVector (4*r+2) → ℝ) (hX : ∀ z, |X z| ≤ 1)
      (u : ℝ) (hu : 0 ≤ u) :
      expectation E.design (fun z => Real.rpow |X z| u) ≤ Real.rpow 2 u := by
    apply AronowAudit.P009.SparseCompletion.mean_le_constant P.design
    intro z
    exact Real.rpow_le_rpow (abs_nonneg _) ((hX z).trans (by norm_num)) hu
  have hReg (q s : ℝ) (hq : 2 ≤ q) (hs : 1 ≤ s) : Regularity E 2 q s := by
    refine ⟨by norm_num, hq, hs, ?_, ?_, ?_⟩
    · intro i
      rw [hm]
      norm_num
    · intro i
      apply hmom (E.outcome i) _ q (by linarith)
      intro z
      rw [abs_of_nonneg (hb i z).1]
      exact (hb i z).2
    · intro i b
      apply hmom (potentialResponse E i b) _ s (by linarith)
      intro z
      exact (abs_of_nonneg (hb i (Function.update z i b)).1).le.trans
        (hb i (Function.update z i b)).2
  refine ⟨E, ⟨hCR, hy, hb, hm, hReg⟩, ?_, ?_⟩
  · have hn : ((4*r+2 : ℕ) : ℝ) ≠ 0 := by positivity
    have htotal : (∑ i, ∑ j, dependenceIndicator E i j) =
        3*((4*r+2 : ℕ) : ℝ)-4 := by
      have ha : (∑ i, ∑ j, dependenceIndicator E i j) / (4*r+2 : ℕ) =
          3-4/(4*r+2 : ℕ) := havg
      rw [div_eq_iff hn] at ha
      rw [ha]
      field_simp
    refine ⟨AronowAudit.P009.Wave1.t9_halfA_card r hr,
      AronowAudit.P009.Wave1.t9_halfB_card r hr, ?_, ?_, ?_, hd, htotal,
      havg, hlt, ?_, hC1, hCinf⟩
    · apply Finset.disjoint_left.mpr
      intro i ha hb'
      exact (Finset.mem_sdiff.mp hb').2 ha
    · ext i
      simp [wholeSecondHalf]
    · intro i j
      change (if AronowAudit.P009.Interferes P i j then (1 : ℝ) else 0) = _
      rw [AronowAudit.P009.Wave1.t9_interferes r P hy i j]
      by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;>
        simp [AronowAudit.P009.Wave1.t9_parents, wholeHalfParents,
          wholeSecondHalf, firstHalf, AronowAudit.P009.halfA, h0, h1]
    · intro i
      change AronowAudit.P009.outgoing P i = _
      rw [AronowAudit.P009.Wave1.t9_outgoing r P hy i]
      by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp_all <;> norm_num
  · have hprobs := AronowAudit.P009.Wave1.t9_majority_half r hr P hCR
    have hpA : probability E.design (wholeMajorityA r) = 1/2 := hprobs.1
    have hpB : probability E.design (wholeMinorityB r) = 1/2 := hprobs.2.1
    have hpAB : probability E.design
        (fun z => wholeMajorityA r z ∧ wholeMinorityB r z) = 1/2 := hprobs.2.2
    refine ⟨?_, ?_, hpA, hpB, hpAB, ?_, halpha⟩
    · intro z hz
      have hc := AronowAudit.P009.Wave1.t9_count_partition
        (AronowAudit.P009.halfA r) z
      rw [AronowAudit.P009.Wave1.t9_count_support r P hCR z hz] at hc
      change wholeTreatedCount (firstHalf r) z +
        wholeTreatedCount (wholeSecondHalf r) z = 2*r+1 at hc
      refine ⟨hc, by omega, ?_⟩
      dsimp [wholeMajorityA, wholeMinorityB]
      omega
    · refine ⟨{z | wholeMajorityA r z}, {z | wholeMinorityB r z}, ?_, ?_⟩
      · ext z
        change (r+1 ≤ AronowAudit.P009.Wave1.t9_count (AronowAudit.P009.halfA r) z) ↔
          r+1 ≤ AronowAudit.P009.Wave1.t9_count (AronowAudit.P009.halfA r)
            (AronowAudit.P009.masked P 0 z)
        rw [AronowAudit.P009.Wave1.t9_count_mask_zero r P hy z]
      · ext z
        change (AronowAudit.P009.Wave1.t9_count
          (Finset.univ \ AronowAudit.P009.halfA r) z ≤ r) ↔
          AronowAudit.P009.Wave1.t9_count (Finset.univ \ AronowAudit.P009.halfA r)
            (AronowAudit.P009.masked P 1 z) ≤ r
        rw [AronowAudit.P009.Wave1.t9_count_mask_one r P hy z]
    · rw [hpA, hpB, hpAB]
      norm_num

/-- The existing overwhelming-fraction theorem supplies the exceptional sets. Counting
gives eventual domains, finite suprema give the literal maximum, and T9 supplies necessity. -/
theorem T10_assembly : T10WholeStatement := by
  constructor
  · intro S hCR hBound
    obtain ⟨F, hF, hfrac, huniform⟩ :=
      AronowAudit.P009.corrected_exceptional_pair_mixing
        (Bridge.toProjectSequence S) hCR hBound
    have hsub (t : ℕ) : F t ⊆ wholeZeroPairs (S.experiment t) := by
      intro ij hij
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF t ij hij⟩
    have hcount (t : ℕ) : ((wholeZeroPairs (S.experiment t)).card : ℝ) =
        (S.N t : ℝ)^2 - (S.N t : ℝ)*averageDependence (S.experiment t) :=
      (AronowAudit.P009.exceptional_pair_finite_counts (S.positive t)
        (Bridge.toProjectExperiment (S.experiment t)) 1 (by norm_num)).2.2.2.2
    have hpos : ∀ᶠ t in atTop, 0 < (wholeZeroPairs (S.experiment t)).card := by
      obtain ⟨D, hD⟩ := hBound
      have hg : Tendsto (fun t => (S.N t : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp S.grows
      filter_upwards [hD, hg.eventually (eventually_gt_atTop D)] with t ht hlarge
      have hn : (0 : ℝ) < S.N t := by exact_mod_cast S.positive t
      have hc : (0 : ℝ) < (wholeZeroPairs (S.experiment t)).card := by
        rw [hcount]
        have hm := mul_pos hn (sub_pos.mpr (ht.trans_lt hlarge))
        nlinarith
      exact_mod_cast hc
    have hdomains : ∀ᶠ t in atTop,
        0 < (wholeZeroPairs (S.experiment t)).card ∧
        (wholeZeroPairs (S.experiment t) \ F t).Nonempty := by
      filter_upwards [hpos, hfrac.eventually_lt_const (by norm_num : (0 : ℝ) < 1)]
        with t ht hsmall
      have hn : (0 : ℝ) < (wholeZeroPairs (S.experiment t)).card := by exact_mod_cast ht
      have hlt : (F t).card < (wholeZeroPairs (S.experiment t)).card := by
        have h := (div_lt_one hn).mp hsmall
        exact_mod_cast h
      refine ⟨ht, Finset.sdiff_nonempty.mpr ?_⟩
      intro hreverse
      exact (not_le_of_gt hlt) (Finset.card_le_card hreverse)
    have hnonneg (t : ℕ) : 0 ≤ wholeMaximumMixing (S.experiment t)
        (wholeZeroPairs (S.experiment t) \ F t) := by
      unfold wholeMaximumMixing
      split_ifs with h
      · obtain ⟨ij, hij⟩ := h
        have hz : 0 ≤ wholePairMixing (S.experiment t) ij :=
          AronowAudit.P009.MixingBasics.alpha_nonnegative
          (Bridge.toProjectDistribution (S.experiment t).design)
          (relevantTreatments (S.experiment t) ij.1)
          (relevantTreatments (S.experiment t) ij.2)
        exact hz.trans (Finset.le_sup' (wholePairMixing (S.experiment t)) hij)
      · exact le_rfl
    have hmax : Tendsto (fun t => wholeMaximumMixing (S.experiment t)
        (wholeZeroPairs (S.experiment t) \ F t)) atTop (nhds 0) := by
      apply tendsto_order.mpr
      constructor
      · intro a ha
        exact Eventually.of_forall (fun t => ha.trans_le (hnonneg t))
      · intro ε hε
        filter_upwards [huniform ε hε] with t ht
        unfold wholeMaximumMixing
        split_ifs with h
        · apply (Finset.sup'_lt_iff h).mpr
          rintro ⟨i,j⟩ hij
          obtain ⟨hz, hnot⟩ := Finset.mem_sdiff.mp hij
          exact ht i j (Finset.mem_filter.mp hz).2 hnot
        · exact hε
    exact ⟨F, hsub, hdomains, hfrac, hmax, huniform⟩
  · have hfamily (t : ℕ) := T9_assembly (t+1) (by omega)
    choose E hE using hfamily
    let S : ExperimentSequence :=
      { N := fun t => 4*(t+1)+2
        positive := fun t => by omega
        grows := tendsto_atTop_mono
          (fun t : ℕ => show t ≤ 4*(t+1)+2 by omega) tendsto_id
        experiment := E }
    have hzero (t : ℕ) : dependenceIndicator (E t) 0 1 = 0 := by
      obtain ⟨_, _, _, _, _, hz, _⟩ := (hE t).2.1
      exact hz
    have halpha (t : ℕ) : wholePairMixing (E t) (0,1) = 1/4 := by
      obtain ⟨_, _, _, _, _, _, ha⟩ := (hE t).2.2
      exact ha
    refine ⟨S, (fun _ => rfl), ?_, ?_, ?_, (fun _ => 0), (fun _ => 1), ?_, ?_⟩
    · intro t
      exact (hE t).1.2.2.2.2 4 1 (by norm_num) (by norm_num)
    · intro t
      exact ⟨2*(t+1)+1, (hE t).1.1⟩
    · intro t
      obtain ⟨_, _, _, _, _, _, _, _, hlt, _⟩ := (hE t).2.1
      exact hlt
    · intro t
      refine ⟨rfl, ?_, hzero t, halpha t⟩
      change 1 % (4*(t+1)+2) = 1
      exact Nat.mod_eq_of_lt (by omega)
    · intro huniform
      obtain ⟨t, ht⟩ := (huniform (1/8) (by norm_num)).exists
      have hbad := ht 0 1 (hzero t)
      change wholePairMixing (E t) (0,1) < 1/8 at hbad
      rw [halpha t] at hbad
      norm_num at hbad

end
end SAP.P009a.WH.W4
