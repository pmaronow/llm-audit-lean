import AronowAudit.P001.Wave1.Lib.TailA.MedianWeak

/-! A positive absolute moment controls the sample maximum at a polynomial rate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
namespace AronowAudit.P001.Wave1.TailA
open AronowAudit.P001.TailA
local instance instDecidableMedianMaximum (p : Prop) : Decidable p := Classical.propDecidable p

/-- Markov applied to the sum of positive-order absolute moments. -/
theorem medianMaximum_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X)
    (η : ℝ) (hη : 0 < η) (hmoment : Integrable (fun ω => |X 0 ω|^η) μ)
    {n : ℕ} (hn : 0 < n) :
    prob μ {ω | ∃ i : Fin n, (n : ℝ)^(2/η) < |X i ω|} ≤
      (∫ ω, |X 0 ω|^η ∂μ) / n := by
  let S := fun ω => ∑ i : Fin n, |X i ω|^η
  have hg : Measurable (fun z : ℝ => |z|^η) := by fun_prop
  have hi (i : ℕ) : Integrable (fun ω => |X i ω|^η) μ :=
    ((hiid.2.2 i).comp hg).integrable_iff.mpr hmoment
  have hmean (i : ℕ) : (∫ ω, |X i ω|^η ∂μ) = ∫ ω, |X 0 ω|^η ∂μ :=
    ((hiid.2.2 i).comp hg).integral_eq
  have hI : Integrable S μ := integrable_finset_sum _ (fun i _ => hi i)
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω =>
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
  have hM : (∫ ω, S ω ∂μ) = n * (∫ ω, |X 0 ω|^η ∂μ) := by
    dsimp only [S]
    rw [integral_finsetSum _ (fun (i : Fin n) _ => hi i)]
    simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsub : {ω | ∃ i : Fin n, (n : ℝ)^(2/η) < |X i ω|} ⊆
      {ω | (n : ℝ)^2 ≤ S ω} := by
    rintro ω ⟨i, hi'⟩
    have hh := Real.rpow_lt_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) hi' hη
    rw [← Real.rpow_mul (Nat.cast_nonneg n), div_mul_cancel₀ _ hη.ne', Real.rpow_two] at hh
    change (n : ℝ)^2 ≤ ∑ j : Fin n, |X j ω|^η
    exact hh.le.trans (Finset.single_le_sum
      (fun (j : Fin n) _ => Real.rpow_nonneg (abs_nonneg (X j ω)) η) (Finset.mem_univ i))
  have hP := (measureReal_mono hsub (measure_ne_top μ _)).trans_eq (rfl : μ.real _ = prob μ _)
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hS0) hI ((n : ℝ)^2)
  rw [hM] at hMarkov
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  apply (le_div_iff₀ hnR).2
  have hh := mul_le_mul_of_nonneg_left hP (sq_nonneg (n : ℝ))
  have hb : (n : ℝ)^2 * prob μ {ω | ∃ i : Fin n, (n : ℝ)^(2/η) < |X i ω|} ≤
      n * (∫ ω, |X 0 ω|^η ∂μ) := hh.trans hMarkov
  nlinarith

/-- The maximum event fails with probability tending to zero for every positive order. -/
theorem medianMaximum_polynomial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X)
    (η : ℝ) (hη : 0 < η) (hmoment : Integrable (fun ω => |X 0 ω|^η) μ) :
    ∃ b : ℝ, 0 < b ∧ Tendsto
      (fun n => prob μ {ω | ∃ i : Fin n, (n : ℝ)^b < |X i ω|}) atTop (nhds 0) := by
  refine ⟨2/η, by positivity, ?_⟩
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    (by filter_upwards [eventually_gt_atTop 0] with n hn
        exact medianMaximum_probability μ X hiid η hη hmoment hn)
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

/-- A nonempty sample median is one of the observations, hence inherits a maximum bound. -/
theorem medianMaximum_median_bound {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (B : ℝ) (hB : ∀ i, |x i| ≤ B) : |sampleMedian x| ≤ B := by
  have hk : n/2 < ((List.ofFn x).mergeSort (fun a b => a ≤ b)).length := by
    simpa using Nat.div_lt_self hn (by norm_num : 1 < (2 : ℕ))
  have hmem : sampleMedian x ∈ (List.ofFn x).mergeSort (fun a b => a ≤ b) := by
    change ((List.ofFn x).mergeSort (fun a b => a ≤ b)).getD (n/2) 0 ∈ _
    rw [List.getD_eq_getElem _ 0 hk]
    exact List.getElem_mem hk
  have hm : sampleMedian x ∈ List.ofFn x :=
    (List.mergeSort_perm (List.ofFn x) (fun a b => a ≤ b)).mem_iff.mp hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
  simpa only [← hi] using hB i

end AronowAudit.P001.Wave1.TailA
