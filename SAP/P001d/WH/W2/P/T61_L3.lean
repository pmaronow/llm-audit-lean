import SAP.P001d.WH.W2.Leaves
import AronowAudit.P001.Wave1.Lib.TailA.MedianCounts
import AronowAudit.P001.Wave1.Lib.TailA.MedianTailBounds
import AronowAudit.P001.Wave1.Gap.GP0014B1

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.WH.W2.P.T61_L3

lemma half_count_iff {n m : ℕ} (hn : 0 < n) :
    (1 / 2 : ℝ) ≤ (m : ℝ) / (n : ℝ) ↔ (n - 1) / 2 + 1 ≤ m := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnat : n ≤ 2 * m ↔ (n - 1) / 2 + 1 ≤ m := by omega
  constructor
  · intro h
    have hm : (1 / 2 : ℝ) * (n : ℝ) ≤ (m : ℝ) :=
      (le_div_iff₀ hnR).mp h
    have hmn : (n : ℝ) ≤ 2 * (m : ℝ) := by nlinarith
    exact hnat.mp (by exact_mod_cast hmn)
  · intro h
    have hmn : n ≤ 2 * m := hnat.mpr h
    have hmnR : (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hmn
    apply (le_div_iff₀ hnR).2
    nlinarith

lemma whole_empirical_cdf_is_cdf {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : WholeCDF (wholeEmpiricalCDF x) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : IsProbabilityMeasure
      (StatLean.ComputationalStatistics.empiricalMeasure x) := inferInstance
  let μ := StatLean.ComputationalStatistics.empiricalMeasure x
  have hcdf : cdf μ id = fun t => ProbabilityTheory.cdf μ t := by
    funext t
    exact (ProbabilityTheory.cdf_eq_real μ t).symm
  have heq : wholeEmpiricalCDF x = cdf μ id := by
    rw [hcdf]
    funext t
    rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
    rw [AronowAudit.P001.Wave1.TailA.medianTail_empirical_cdf]
    unfold wholeEmpiricalCDF AronowAudit.Literature.FiniteCDF
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  rw [heq]
  exact SAP.P001d.WH.W2.whole_cdf _

lemma sorted_lower_count_iff {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (t : ℝ) :
    wholeLowerMedian x ≤ t ↔ (1 / 2 : ℝ) ≤ wholeEmpiricalCDF x t := by
  let l := (List.ofFn x).mergeSort (fun a b => a ≤ b)
  have hlen : l.length = n := by
    dsimp [l]
    have hp := List.mergeSort_perm (List.ofFn x) (fun a b => a ≤ b)
    simpa using hp.length_eq
  have hk : (n - 1) / 2 < l.length := by
    rw [hlen]
    omega
  have hs : l.Pairwise (· ≤ ·) := by
    dsimp [l]
    exact List.pairwise_mergeSort' (· ≤ ·) _
  have hr := AronowAudit.P001.TailA.medianCounts_sorted_rank l hs ((n - 1) / 2) hk t
  change l.getD ((n - 1) / 2) 0 ≤ t ↔
    (1 / 2 : ℝ) ≤
      ((Finset.univ.filter (fun i : Fin n => x i ≤ t)).card : ℝ) / (n : ℝ)
  rw [← AronowAudit.P001.TailA.medianCounts_sorted_filter_card]
  exact hr.trans (half_count_iff hn).symm

lemma empirical_quantile_inf {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    ({t : ℝ | (1 / 2 : ℝ) ≤ wholeEmpiricalCDF x t}).Nonempty ∧
    BddBelow {t : ℝ | (1 / 2 : ℝ) ≤ wholeEmpiricalCDF x t} ∧
    sInf {t : ℝ | (1 / 2 : ℝ) ≤ wholeEmpiricalCDF x t} = wholeLowerMedian x := by
  let S := {t : ℝ | (1 / 2 : ℝ) ≤ wholeEmpiricalCDF x t}
  have hmem : wholeLowerMedian x ∈ S := by
    change (1 / 2 : ℝ) ≤ wholeEmpiricalCDF x (wholeLowerMedian x)
    exact (sorted_lower_count_iff hn x (wholeLowerMedian x)).1 le_rfl
  have hbelow : BddBelow S := by
    refine ⟨wholeLowerMedian x, ?_⟩
    intro t ht
    exact (sorted_lower_count_iff hn x t).2 ht
  have hne : S.Nonempty := ⟨wholeLowerMedian x, hmem⟩
  have hle : sInf S ≤ wholeLowerMedian x := csInf_le hbelow hmem
  have hge : wholeLowerMedian x ≤ sInf S :=
    le_csInf hne (by
      intro t ht
      exact (sorted_lower_count_iff hn x t).2 ht)
  exact ⟨hne, hbelow, hle.antisymm hge⟩

lemma whole_lower_median_const {n : ℕ} (hn : 0 < n) (c : ℝ) :
    wholeLowerMedian (fun _ : Fin n => c) = c := by
  unfold wholeLowerMedian
  rw [List.ofFn_const]
  have hs : (List.replicate n c).mergeSort (fun a b => a ≤ b) = List.replicate n c :=
    List.perm_replicate.mp (List.mergeSort_perm _ _)
  rw [hs]
  apply List.getD_replicate
  omega

lemma lower_eq_upper_of_odd {n : ℕ} (ho : Odd n) :
    (n - 1) / 2 = n / 2 := by
  rcases ho with ⟨k, hk⟩
  omega

end SAP.P001d.WH.W2.P.T61_L3

theorem SAP.P001d.WH.W2.T61_L3_proof : SAP.P001d.WH.W2.T61_L3 := by
  constructor
  · intro n hn x
    have hq := SAP.P001d.WH.W2.P.T61_L3.empirical_quantile_inf hn x
    refine ⟨SAP.P001d.WH.W2.P.T61_L3.whole_empirical_cdf_is_cdf hn x,
      hq.1, hq.2.1, hq.2.2, ?_⟩
    intro ho
    have hidx := SAP.P001d.WH.W2.P.T61_L3.lower_eq_upper_of_odd ho
    have hquant := hq.2.2
    have h0 : wholeEmpiricalCDF x 0 =
        ((Finset.univ.filter (fun i : Fin n => x i ≤ 0)).card : ℝ) / (n : ℝ) := rfl
    unfold wholeRegularStatistic regularHeavyStatistic regularHeavyFunctional
    rw [h0]
    by_cases h :
        (((Finset.univ.filter (fun i : Fin n => x i ≤ 0)).card : ℝ) / (n : ℝ)) ∈
          Set.Icc (1 / 4 : ℝ) (3 / 4)
    · simp only [if_pos h]
    · simp only [if_neg h]
      rw [hquant]
      simp [wholeLowerMedian, sampleMedian, hidx]
  · intro n hn c
    have hq := SAP.P001d.WH.W2.P.T61_L3.empirical_quantile_inf hn (fun _ : Fin n => c)
    have hmedian := SAP.P001d.WH.W2.P.T61_L3.whole_lower_median_const hn c
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hcdf : wholeEmpiricalCDF (fun _ : Fin n => c) 0 = if c ≤ 0 then 1 else 0 := by
      unfold wholeEmpiricalCDF
      by_cases hc : c ≤ 0 <;> simp [hc, hnR]
    unfold wholeRegularStatistic regularHeavyFunctional
    rw [hcdf]
    by_cases hc : c ≤ 0
    · have hbad : (1 : ℝ) ∉ Set.Icc (1 / 4 : ℝ) (3 / 4) := by norm_num
      simp only [if_pos hc, if_neg hbad]
      rw [hq.2.2, hmedian]
    · have hbad : (0 : ℝ) ∉ Set.Icc (1 / 4 : ℝ) (3 / 4) := by norm_num
      simp only [if_neg hc, if_neg hbad]
      rw [hq.2.2, hmedian]

