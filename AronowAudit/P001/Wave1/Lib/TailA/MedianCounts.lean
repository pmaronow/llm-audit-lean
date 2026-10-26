import AronowAudit.P001.Wave1.Lib.TailA.FiniteBootstrap
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort

/-! The upper sample median, with ties and both sample-size parities. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA

local instance instDecidableMedianCounts (p : Prop) : Decidable p := Classical.propDecidable p

/-- Rank and weak-threshold count for an arbitrary sorted list. -/
theorem medianCounts_sorted_rank (l : List ℝ) (hl : l.Pairwise (· ≤ ·))
    (k : ℕ) (hk : k < l.length) (t : ℝ) :
    l.getD k 0 ≤ t ↔ k + 1 ≤ (l.filter (fun a => a ≤ t)).length := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    obtain ⟨ha, hs⟩ := List.pairwise_cons.mp hl
    by_cases hat : a ≤ t
    · cases k with
      | zero => simp [hat]
      | succ k =>
        have hk' : k < l.length := by simpa using hk
        simpa [hat, Nat.add_assoc] using ih hs k hk'
    · have hnone : ∀ b ∈ l, ¬ b ≤ t := fun b hb hbt => hat ((ha b hb).trans hbt)
      have hf : l.filter (fun b => b ≤ t) = [] :=
        List.filter_eq_nil_iff.mpr (by simpa using hnone)
      have hleft : ¬ (a :: l).getD k 0 ≤ t := by
        cases k with
        | zero => simpa using hat
        | succ k =>
          have hk' : k < l.length := by simpa using hk
          simpa only [List.getD_cons_succ, List.getD_eq_getElem l 0 hk'] using
            hnone (l[k]) (List.getElem_mem hk')
      have hright : ¬ k + 1 ≤ ((a :: l).filter (fun b => b ≤ t)).length := by
        simp [hat, hf]
      exact iff_of_false hleft hright

/-- Sorting preserves the number of observations below a weak threshold. -/
theorem medianCounts_sorted_filter_card {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    (((List.ofFn x).mergeSort (fun a b => a ≤ b)).filter (fun a => a ≤ t)).length =
      (Finset.univ.filter (fun i => x i ≤ t)).card := by
  rw [((List.mergeSort_perm (List.ofFn x) (fun a b => a ≤ b)).filter
    (fun a => decide (a ≤ t))).length_eq]
  simp only [Finset.card_filter]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    by_cases h : x 0 ≤ t <;> simp [h, ih (fun i => x i.succ), Nat.add_comm]

/-- The definition uses rank `n / 2`, hence the upper median for even sizes. -/
theorem upper_median_count {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (t : ℝ) :
    sampleMedian x ≤ t ↔ n/2 + 1 ≤ (Finset.univ.filter (fun i => x i ≤ t)).card := by
  have hk : n / 2 < ((List.ofFn x).mergeSort (fun a b => a ≤ b)).length := by
    simpa using Nat.div_lt_self hn (by norm_num : 1 < (2 : ℕ))
  have hs : ((List.ofFn x).mergeSort (fun a b => a ≤ b)).Pairwise (· ≤ ·) :=
    List.pairwise_mergeSort' (· ≤ ·) _
  simpa only [sampleMedian, medianCounts_sorted_filter_card] using
    medianCounts_sorted_rank _ hs (n / 2) hk t

/-- Every weak-threshold count is a measurable finite sum. -/
theorem medianCounts_count_measurable (n : ℕ) (t : ℝ) :
    Measurable (fun x : Fin n → ℝ => (Finset.univ.filter (fun i => x i ≤ t)).card) := by
  simp only [Finset.card_filter]
  exact Finset.univ.measurable_sum fun i _ => Measurable.ite
    (measurableSet_le (measurable_pi_apply i) measurable_const)
    measurable_const measurable_const

theorem upper_median_measurable (n : ℕ) : Measurable (@sampleMedian n) := by
  by_cases hn : 0 < n
  · apply measurable_of_Iic
    intro t
    have he : sampleMedian ⁻¹' Set.Iic t =
        {x : Fin n → ℝ | n / 2 + 1 ≤ (Finset.univ.filter (fun i => x i ≤ t)).card} := by
      ext x
      exact upper_median_count hn x t
    rw [he]
    exact measurableSet_le measurable_const (medianCounts_count_measurable n t)
  · have hz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hz : (@sampleMedian 0) = fun _ => 0 := by
      funext x
      simp [sampleMedian]
    rw [hz]
    exact measurable_const

/-- The finite resampling median event is exactly a binomial upper tail. -/
theorem upper_median_bootstrap_probability {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (t : ℝ) :
    prob (UniformResampling n) {a | sampleMedian (resample x a) ≤ t} =
      prob (binomial n (empiricalThresholdProbability x t)) {k | n / 2 + 1 ≤ k} := by
  rw [← bootstrap_threshold_count_law x t]
  simp only [prob]
  rw [Measure.map_apply (Measurable.of_discrete) (MeasurableSet.of_discrete)]
  congr 2
  ext a
  exact upper_median_count hn (resample x a) t

end AronowAudit.P001.TailA
