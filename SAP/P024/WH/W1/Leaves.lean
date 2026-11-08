import SAP.P024.Defs.WholeW1
import SAP.P024.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P024.WH.W1
open scoped BigOperators
open Filter SAP.P024 SAP.P024.Bridge
noncomputable section

/-- The new finite-sample calculation for T5: on every twelve-treated allocation
the estimate is 46/57 when the large cluster is treated and zero otherwise,
independently of the empty-arm extension. Prove that twelve treated clusters
give nonempty arms; use `AronowAudit.P024.cluster_dim_subset` to rewrite the
means over the treated subset and its complement, then
`AronowAudit.P024.sum_two_values` to evaluate the sums. If zero is treated,
the treated numerator is 46 and denominator 46+11=57; otherwise the numerator
is zero. All control outcomes are zero. This needs no enumeration of subsets. -/
def T5_L1 : Prop :=
  ∀ (empty : Finset (Fin 24) → ℝ)
    (s : {s : Finset (Fin 24) // s.card = 12}),
    populationEstimator fewDozenPopulation empty s.val =
      if (0 : Fin 24) ∈ s.val then 46/57 else 0

theorem T5_assembly (h1 : T5_L1) : T5WholeStatement := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro P d p empty B η hB hη hbound hdesign hinterior hdominance
      exact AronowAudit.P024.corrected_cluster_consistency
        (fun k => toPopulation (P k)) (fun k => toDesign (d k)) p empty B η
        hB hη hbound hdesign hinterior hdominance
    · intro P
      exact AronowAudit.P024.no_dominance_iff_squared_weights
        (fun k => clusterWeight (P k))
        (fun k j => ((AronowAudit.P024.population_weights (toPopulation (P k))).1 j).le)
        (fun k => (AronowAudit.P024.population_weights (toPopulation (P k))).2)
  · refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j i
      dsimp [fewDozenPopulation]
      split_ifs <;> norm_num
    · intro j hj
      simp [fewDozenPopulation, hj]
    · norm_num [fewDozenPopulation, Fin.sum_univ_succ]
    · have hm0 : clusterMean0 fewDozenPopulation = fun _ => 0 := by
        funext j
        change (∑ _ : Fin (if j = 0 then 46 else 1), (0 : ℝ)) / _ = 0
        simp
      have hm1 : clusterMean1 fewDozenPopulation = fun j => if j = 0 then 1 else 0 := by
        funext j
        change (∑ _ : Fin (if j = 0 then 46 else 1),
          (if j = 0 then (1 : ℝ) else 0)) / ((if j = 0 then 46 else 1 : ℕ) : ℝ) = _
        by_cases hj : j = 0 <;> norm_num [hj]
      unfold populationEffect
      rw [hm0, hm1]
      norm_num [clusterEffect, fewDozenPopulation, Fin.sum_univ_succ]
    · intro empty
      have he : (fun s : {s : Finset (Fin 24) // s.card = 12} =>
          populationEstimator fewDozenPopulation empty s.val) =
          (fun s => if (0 : Fin 24) ∈ s.val then (46/57 : ℝ) else 0) :=
        funext (h1 empty)
      rw [he]
      have hd := (AronowAudit.P024.dominant_complete_distribution 11).1
      have hp : AronowAudit.P024.probability (toDesign fewDozenDesign)
          (fun s => (0 : Fin 24) ∈ s.val) = 1/2 := hd
      change AronowAudit.P024.expectation (toDesign fewDozenDesign)
        (fun s => if (0 : Fin 24) ∈ s.val then (46/57 : ℝ) else 0) = _
      rw [AronowAudit.P024.expectation_if_constant, hp]
      norm_num
    · norm_num
    · norm_num
  · refine ⟨fun k => AronowAudit.P024.uniform_subsets_independent (k+2),
      ?_, AronowAudit.P024.dominant_effect,
      AronowAudit.P024.dominant_share_limit, ?_⟩
    · intro k j i
      change |(if j.val = 0 then (1/2 : ℝ) else 1/4)| ≤ 1 ∧
        |(if j.val = 0 then (3/4 : ℝ) else 1/2)| ≤ 1
      split_ifs <;> norm_num
    · intro empty
      exact AronowAudit.P024.dominant_cluster_inconsistent empty

theorem T6_assembly : T6WholeStatement := by
  classical
  unfold T6WholeStatement
  have he : expectation unequalSixDesign
      (fun ω => clusterDIM (fun _ => 1) (fun _ => 0) ![1,0,0] (sixExposure ω)) = 3/8 := by
    norm_num [expectation, unequalSixDesign, clusterDIM, sixExposure,
      Fin.sum_univ_succ, -Finset.sum_boole]
  have ht : averageEffect Finset.univ (fun _ : Fin 3 => 0) ![1,0,0] = 1/3 := by
    norm_num [averageEffect, Fin.sum_univ_succ]
  refine ⟨?_, ?_, ?_, ?_, ?_, he, ht, ?_⟩
  · intro ω
    fin_cases ω <;> norm_num [unequalSixDesign]
  · intro ω
    fin_cases ω <;> decide
  · decide
  · decide
  · intro i
    fin_cases i <;>
      norm_num [exposureProbability, expectation, unequalSixDesign, indicator,
        sixExposure, Fin.sum_univ_succ, -Finset.sum_boole]
  · rw [he, ht]
    norm_num

theorem T7_assembly : T7WholeStatement := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro k p hp hp1
    let d := bernoulliDesign (k+2) p hp.le hp1.le
    let A := fun s : Finset (Fin (k+2)) => s ≠ ∅ ∧ s ≠ Finset.univ
    have hne : (∅ : Finset (Fin (k+2))) ≠ Finset.univ := by
      intro h
      have hc := congrArg Finset.card h
      simp at hc
    have hsplit (s : Finset (Fin (k+2))) :
        d.mass s = (if A s then d.mass s else 0) +
          (if s = ∅ then d.mass s else 0) +
          (if s = Finset.univ then d.mass s else 0) := by
      by_cases h0 : s = ∅
      · subst s
        simp [A, hne]
      · by_cases hU : s = Finset.univ <;> simp [A, h0, hU, hne.symm]
    have htotal := d.total
    conv_lhs at htotal => arg 2; ext s; rw [hsplit s]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at htotal
    have hprob : probability d A = ∑ s, if A s then d.mass s else 0 := by
      simp [probability, expectation, mul_ite]
    have hformula : probability d A = 1-p^(k+2)-(1-p)^(k+2) := by
      rw [← hprob] at htotal
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at htotal
      have h0 : d.mass ∅ = (1-p)^(k+2) := by
        simp [d, bernoulliDesign, bernoulliMass]
      have hU : d.mass Finset.univ = p^(k+2) := by
        simp [d, bernoulliDesign, bernoulliMass]
      rw [h0, hU] at htotal
      linarith
    have hm : bernoulliNonemptyMass k p = probability d A :=
      AronowAudit.P024.bernoulli_nonempty_mass_probability k p hp hp1
    have hpos : 0 < bernoulliNonemptyMass k p :=
      AronowAudit.P024.bernoulli_nonempty_mass_positive k p hp hp1
    refine ⟨fun s => rfl, hformula, ?_, ?_, ?_⟩
    · rw [← hformula, ← hm]
      exact hpos
    · intro s
      change bernoulliMass p s.val / bernoulliNonemptyMass k p = _
      rw [hm, hformula]
      rfl
    · unfold bernoulliConditionalMass
      rw [← Finset.sum_div]
      exact div_self hpos.ne'
  · constructor
    · intro k q hq P hsize p hp hp1
      have h := AronowAudit.P024.Wave1.equal_cluster_independent_population_on_defined_domain
        k q hq (toPopulation P) hsize p hp hp1
      refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, ?_⟩
      intro s
      have hm : 0 < s.val.card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr s.property.1)
      have hmK : s.val.card < Fintype.card (Fin (k+2)) :=
        Finset.card_lt_card (Finset.ssubset_univ_iff.mpr s.property.2)
      have hcount : AronowAudit.P024.treatedCount (AronowAudit.P024.subsetExposure s.val) =
          s.val.card := by
        simp [AronowAudit.P024.treatedCount, AronowAudit.P024.subsetExposure]
      have hn : (fun j => (P.size j : ℝ)) = fun _ => (q : ℝ) := by
        funext j
        rw [hsize j]
      simp only [populationEstimator, s.property.1, s.property.2, or_self, ite_false]
      rw [hn]
      exact AronowAudit.P024.equal_size_dim q (by exact_mod_cast hq) s.val.card hm hmK
        (AronowAudit.P024.subsetExposure s.val) hcount (clusterMean0 P) (clusterMean1 P)
    · have h := AronowAudit.P024.Wave1.independent_unequal_size_bias_on_defined_domain
      dsimp only at h ⊢
      refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_, h.2.2.2.2.1, h.2.2.2.2.2⟩
      all_goals norm_num [clusterDIM, subsetExposure, Fin.sum_univ_two]
  · have hm0 : clusterMean0 unequalPairPopulation = ![0,0] := by
      funext j
      change (∑ _ : Fin ((![1,2] : Fin 2 → ℕ) j), (0 : ℝ)) / _ = _
      fin_cases j <;> norm_num
    have hm1 : clusterMean1 unequalPairPopulation = ![0,1] := by
      funext j
      change (∑ _ : Fin ((![1,2] : Fin 2 → ℕ) j),
        (if j = 0 then (0 : ℝ) else 1)) / ((![1,2] : Fin 2 → ℕ) j : ℝ) = _
      fin_cases j <;> norm_num
    have hn : (fun j => (unequalPairPopulation.size j : ℝ)) = ![1,2] := by
      funext j
      fin_cases j <;> norm_num [unequalPairPopulation]
    refine ⟨rfl, fun _ _ => ⟨rfl, rfl⟩, hm0, hm1, ?_, ?_, ?_⟩
    · unfold populationEffect
      rw [hm0, hm1]
      norm_num [clusterEffect, unequalPairPopulation, Fin.sum_univ_two]
    · intro empty
      have h := AronowAudit.P024.Wave1.independent_unequal_size_bias_on_defined_domain
      dsimp only at h
      have he : (fun s : NonemptyAllocations 0 =>
          populationEstimator unequalPairPopulation empty s.val) =
          (fun s => if s.val = ∅ ∨ s.val = Finset.univ then empty s.val else
            clusterDIM (![1,2] : Fin 2 → ℝ) ![0,0] ![0,1] (subsetExposure s.val)) := by
        funext s
        unfold populationEstimator
        rw [hm0, hm1, hn]
      rw [he]
      exact h.2.2.2.2.1 empty
    · intro s
      have hc : Fintype.card (NonemptyAllocations 0) = 2 := by decide
      change 1/(Fintype.card (NonemptyAllocations 0) : ℝ) = 1/2
      rw [hc]
      norm_num

theorem T8_assembly : T8WholeStatement := by
  classical
  unfold T8WholeStatement
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;>
        norm_num [exposureProbability, expectation, uniformDesign, indicator,
          sixExposure, Fin.sum_univ_succ, -Finset.sum_boole]
    · intro ω
      fin_cases ω <;> decide
    all_goals
      norm_num [actualBlockedHT, weightedBlockDIM, blockPopulation,
        oneBlockThreeExposure, exposureProbability, expectation, uniformDesign,
        indicator, sixExposure, clusterDIM, Fin.sum_univ_succ, -Finset.sum_boole]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;>
        norm_num [exposureProbability, expectation, unequalTwoDesign, indicator,
          oneBlockTwoExposure, Fin.sum_univ_succ, -Finset.sum_boole]
    · intro ω
      fin_cases ω <;> decide
    all_goals
      norm_num [actualBlockedHT, weightedBlockDIM, blockPopulation,
        oneBlockTwoExposure, exposureProbability, expectation, unequalTwoDesign,
        indicator, clusterDIM, averageEffect, Fin.sum_univ_succ, -Finset.sum_boole]

end
end SAP.P024.WH.W1
