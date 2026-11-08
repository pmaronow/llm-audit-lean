import SAP.P009a.Defs.WholeW2
import SAP.P009a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009a.WH.W2

open Filter MeasureTheory
open scoped BigOperators Topology Classical

noncomputable section

/-- Bounded fair experiments satisfy all the finite moment assumptions. -/
theorem fair_regular_all_orders {n : ℕ} (y : Fin n → TreatmentVector n → ℝ)
    (k : ℝ) (hk : 2 ≤ k) (hy : ∀ i z, |y i z| ≤ k)
    (q s : ℝ) (hq : 2 ≤ q) (hs : 1 ≤ s) :
    Regularity (fairPopulation n y) k q s := by
  refine ⟨by linarith, hq, hs, ?_, ?_, ?_⟩
  · intro i
    have hm : armProbability (fairPopulation n y) i true = 1/2 :=
      AronowAudit.P009.SparseCompletion.fair_marginal n y i true
    rw [hm]
    have hinv : k⁻¹ ≤ (2:ℝ)⁻¹ := inv_anti₀ (by norm_num) hk
    norm_num at hinv
    constructor <;> linarith
  · intro i
    change AronowAudit.P009.mean (AronowAudit.P009.fairLaw n)
      (fun z => Real.rpow |y i z| q) ≤ Real.rpow k q
    apply AronowAudit.P009.SparseCompletion.mean_le_constant
    intro z
    exact Real.rpow_le_rpow (abs_nonneg _) (hy i z) (by linarith)
  · intro i b
    change AronowAudit.P009.mean (AronowAudit.P009.fairLaw n)
      (fun z => Real.rpow |y i (Function.update z i b)| s) ≤ Real.rpow k s
    apply AronowAudit.P009.SparseCompletion.mean_le_constant
    intro z
    exact Real.rpow_le_rpow (abs_nonneg _) (hy i (Function.update z i b)) (by linarith)

/-- Self-interference gives positive average outgoing and dependence counts. -/
theorem graph_lower_bounds {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n) :
    1 ≤ averageOutgoing E ∧ 1 ≤ averageDependence E := by
  constructor
  · have hout (i : Fin n) : 1 ≤ outgoingCount E i := by
      have hI (j : Fin n) : 0 ≤ interferenceIndicator E i j := by
        unfold interferenceIndicator
        split_ifs <;> norm_num
      have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hI j)
        (Finset.mem_univ i)
      simpa [interferenceIndicator, Affects, outgoingCount] using h
    unfold averageOutgoing
    apply (le_div_iff₀ (show (0:ℝ) < n by exact_mod_cast hn)).2
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hout i)
  · exact AronowAudit.P009.average_degree_at_least_one (Bridge.toProjectExperiment E) hn

/-- Existing star computations, with the explicit restricted-interference limit. -/
theorem star_sequence_facts :
    SequenceRegularity wholeStarSequence 2 4 1 ∧
    (∀ t, ProductDesign (wholeStarSequence.experiment t)) ∧
    SparseDependence wholeStarSequence ∧
    Tendsto (fun t => averageDependence (wholeStarSequence.experiment t)/
      averageOutgoing (wholeStarSequence.experiment t)) atTop atTop ∧
    (∀ t, indirectBias (wholeStarSequence.experiment t) = 0 ∧
      0 < directBias (wholeStarSequence.experiment t) ∧
      0 < meanSquaredEffect (wholeStarSequence.experiment t)/
        averageDependence (wholeStarSequence.experiment t)) := by
  obtain ⟨hf, hr⟩ := AronowAudit.P009.Wave1.dominating_term_counterexample_proof
  have h (t : ℕ) := hf (t+2) (by omega)
  have hd (t : ℕ) : averageDependence (wholeStarSequence.experiment t) = (t+2:ℕ) := (h t).2.2.2.1
  have hc (t : ℕ) : averageOutgoing (wholeStarSequence.experiment t) = 2 := (h t).2.2.1
  have hm (t : ℕ) : meanSquaredEffect (wholeStarSequence.experiment t) = 1 := (h t).2.2.2.2.1
  refine ⟨fun t => (h t).2.1, fun t => (h t).1, ?_, ?_, ?_⟩
  · change Tendsto (fun t => averageDependence (wholeStarSequence.experiment t) /
      (((t+2)*(t+2):ℕ):ℝ)) atTop (nhds 0)
    simp_rw [hd, Nat.cast_mul]
    have he (t : ℕ) : ((t+2:ℕ):ℝ) / (((t+2:ℕ):ℝ)*((t+2:ℕ):ℝ)) =
        1/((t+2:ℕ):ℝ) := by field_simp
    simp_rw [he]
    exact (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)).const_div_atTop 1
  · simpa only [hd, hc] using hr
  · intro t
    refine ⟨(h t).2.2.2.2.2.2.1, (h t).2.2.2.2.2.2.2.1, ?_⟩
    rw [hm, hd]
    positivity

/-- Squeezing a nonnegative reciprocal by the claimed ratio. -/
theorem reciprocal_consequence (C D B : ℕ → ℝ)
    (hC : ∀ t, 1 ≤ C t) (hD : ∀ t, 0 < D t)
    (hB : ∀ᶠ t in atTop, B t ≠ 0)
    (h : Tendsto (fun t => C t/(D t*|B t|)) atTop (nhds 0)) :
    Tendsto (fun t => 1/(D t*|B t|)) atTop (nhds 0) := by
  apply squeeze_zero' _ _ h
  · exact Eventually.of_forall fun t => div_nonneg (by norm_num)
      (mul_nonneg (hD t).le (abs_nonneg _))
  · filter_upwards [hB] with t ht
    exact div_le_div_of_nonneg_right (hC t) (mul_nonneg (hD t).le (abs_nonneg _))

/-- A positive eventual lower bound supplies the additional ratio condition. -/
theorem ratio_from_lower_bound (C D B : ℕ → ℝ)
    (hC : ∀ t, 0 ≤ C t) (hD : ∀ t, 0 < D t)
    (h : Tendsto (fun t => D t/C t) atTop atTop)
    (c : ℝ) (hc : 0 < c) (hl : ∀ᶠ t in atTop, c ≤ |B t|) :
    (∀ᶠ t in atTop, B t ≠ 0) ∧
    Tendsto (fun t => C t/(D t*|B t|)) atTop (nhds 0) := by
  have hnz : ∀ᶠ t in atTop, B t ≠ 0 := by
    filter_upwards [hl] with t ht
    exact abs_pos.mp (hc.trans_le ht)
  refine ⟨hnz, ?_⟩
  have hi : Tendsto (fun t => C t/D t) atTop (nhds 0) := by
    simpa only [Function.comp_def, inv_div] using tendsto_inv_atTop_zero.comp h
  have hz : Tendsto (fun t => (C t/D t)/c) atTop (nhds 0) := by
    simpa using hi.div_const c
  apply squeeze_zero' _ _ hz
  · exact Eventually.of_forall fun t => div_nonneg (hC t)
      (mul_nonneg (hD t).le (abs_nonneg _))
  · filter_upwards [hl] with t ht
    rw [← div_div]
    exact div_le_div_of_nonneg_left (div_nonneg (hC t) (hD t).le) hc ht

end
end SAP.P009a.WH.W2
