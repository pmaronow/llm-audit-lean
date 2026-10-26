import AronowAudit.P005.Wave1.InteractedExpansion

namespace AronowAudit.P005.Wave1

noncomputable section
open scoped BigOperators Matrix Topology
open Finset Filter
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

/-!
P005-T7: grid moments, standardization, all-assignment regularity,
a divergent remainder and the leverage limit for the spike population.
-/

lemma t7_standardized (n : ℕ) (hn : 3 ≤ n) : standardized (spikePopulation n) :=
  InteractedExpansion.n2_proof InteractedExpansion.n1_proof n hn

lemma t7_finite_moments_allocation (n : ℕ) (hn : 3 ≤ n) :
    standardized (spikePopulation n) ∧
    popMean (fun i => (spikePopulation n).yT i^2) ≤ 1 ∧
    popMean (fun i => (spikePopulation n).yC i^2) ≤ 1 ∧
    (∀ k, popMean (fun i => (spikePopulation n).x i k^2) = 1) ∧
    (1/4 : ℝ) < pT n (n/2) ∧ pT n (n/2) < (3/4 : ℝ) := by
  have hstd := t7_standardized n hn
  have hnon : (univ : Finset (Fin n)).Nonempty :=
    Finset.card_pos.mp (by simpa using (show 0 < n by omega))
  have hy : popMean (fun i => spikeV n i ^ 2) ≤ 1 := by
    calc
      _ ≤ mean univ (fun _ => (1 : ℝ)) := by
        apply mean_mono
        intro i hi
        have h := abs_le.mp (InteractedExpansion.spikeV_abs n hn i)
        nlinarith [h.1, h.2]
      _ = 1 := mean_const univ hnon 1
  refine ⟨hstd, hy, hy, ?_, ?_, ?_⟩
  · intro k
    have hg := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M k k) hstd.2
    simpa [gram, pow_two] using hg
  · have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hd : (0 : ℝ) < n := by linarith
    have hl : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ 3 * (n / 2) by omega)
    exact (lt_div_iff₀ hd).2 (by nlinarith)
  · have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hd : (0 : ℝ) < n := by linarith
    have hh : ((n / 2 : ℕ) : ℝ) * 2 ≤ n := by
      exact_mod_cast (Nat.div_mul_le_self n 2)
    exact (div_lt_iff₀ hd).2 (by nlinarith)

/-- The special unit alone gives a leverage lower bound converging to one.
An exact maximization over all units is unnecessary. -/
lemma t7_special_le_kappa (n : ℕ) (hn : 3 ≤ n) :
    (1 - 1 / (n : ℝ)) /
      (1 + 1 / (3 * ((n : ℝ) - 2) * (n : ℝ)^2)) ≤
      kappa (spikePopulation n) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have hq := InteractedExpansion.spikeQ_pos_of_S1
    InteractedExpansion.n1_proof n hn
  let z : Fin n := ⟨0, by omega⟩
  have hlev : leverage (spikePopulation n) z =
      (1 - 1 / (n : ℝ))^2 / spikeQ n := by
    simp only [leverage, dot, Fin.sum_univ_one, spikePopulation,
      spikeZ, spikeA, z, ↓reduceIte]
    rw [← pow_two, div_pow, Real.sq_sqrt hq.le]
  have heq : leverage (spikePopulation n) z / n =
      (1 - 1 / (n : ℝ)) /
        (1 + 1 / (3 * ((n : ℝ) - 2) * (n : ℝ)^2)) := by
    rw [hlev, (InteractedExpansion.n1_proof n hn).2.2.2.2]
    field_simp [hn0, hn1, hn2]
  rw [← heq]
  apply (div_le_iff₀ hnpos).2
  simpa only [mul_comm] using
    leverage_le_maximum (spikePopulation n) (by omega) z

lemma t7_kappa_tendsto :
    Tendsto (fun n => kappa (spikePopulation n)) atTop (nhds 1) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) - 2) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-2 : ℝ)
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hsmall : Tendsto
      (fun n : ℕ => 1 / (3 * ((n : ℝ) - 2) * (n : ℝ)^2)) atTop (nhds 0) := by
    have h := ((tendsto_const_nhds (x := (3 : ℝ)⁻¹)).mul
      hshift.inv_tendsto_atTop).mul (hinv.pow 2)
    simpa only [Pi.inv_apply, one_div, mul_inv_rev, inv_pow, mul_zero, zero_mul,
      mul_assoc, mul_comm, mul_left_comm] using h
  have hlower : Tendsto
      (fun n : ℕ => (1 - 1 / (n : ℝ)) /
        (1 + 1 / (3 * ((n : ℝ) - 2) * (n : ℝ)^2))) atTop (nhds 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).div
        (tendsto_const_nhds.add hsmall) (by norm_num : (1 : ℝ) + 0 ≠ 0)
    change Tendsto (fun n : ℕ => (1 - 1 / (n : ℝ)) /
      (1 + 1 / (3 * ((n : ℝ) - 2) * (n : ℝ)^2))) atTop
      (nhds ((1 - 0) / (1 + 0))) at h
    simpa only [sub_zero, add_zero, div_one] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · exact Filter.eventually_atTop.2 ⟨3, fun n hn => t7_special_le_kappa n hn⟩
  · exact Filter.eventually_atTop.2 ⟨3, fun n hn =>
      (kappa_bounds (spikePopulation n) (by omega) (t7_standardized n hn).2).2⟩

theorem univariate_endpoint_counterexample_proof :
    standingAssumptions (fun _ => 1) (fun n => n/2) spikePopulation ∧
    (∀ n, 6 ≤ n → standardized (spikePopulation n) ∧
      popMean (fun i => (spikePopulation n).yT i^2) ≤ 1 ∧
      popMean (fun i => (spikePopulation n).yC i^2) ≤ 1 ∧
      (∀ k, popMean (fun i => (spikePopulation n).x i k^2) = 1) ∧
      (1/4 : ℝ) < pT n (n/2) ∧ pT n (n/2) < (3/4 : ℝ)) ∧
    (∀ n, 6 ≤ n → interactedRegular (spikePopulation n) (n/2)) ∧
    Tendsto (fun n => kappa (spikePopulation n)) atTop (nhds 1) ∧
    Tendsto (fun n => kappa (spikePopulation n) * Real.log (1 : ℝ)) atTop (nhds 0) ∧
    (∀ n, 6 ≤ n → ate (spikePopulation n) = 0) ∧
    (∀ n, 6 ≤ n → Even n → ∀ S ∈ design n (n/2),
      (n : ℝ)-6 ≤ |interactedATE (spikePopulation n) S - ate (spikePopulation n) -
        armLeading (spikePopulation n) S|) ∧
    ¬stochasticO (fun n => n/2)
      (fun n S => interactedATE (spikePopulation n) S - ate (spikePopulation n) - armLeading (spikePopulation n) S)
      (fun n => Real.sqrt (kappa (spikePopulation n)/n)) := by
  have h1 := InteractedExpansion.n1_proof
  have h2 := InteractedExpansion.n2_proof h1
  have h4 := InteractedExpansion.n4_proof
  have h5 := InteractedExpansion.n5_proof
  have h9 := InteractedExpansion.n9_proof h1
  have h10 := InteractedExpansion.n10_proof h1 h4 h5
    (InteractedExpansion.n7_proof h5) (InteractedExpansion.n8_proof h1 h5) h9
  refine ⟨InteractedExpansion.n3_proof h1 h2,
    fun n hn => t7_finite_moments_allocation n (by omega),
    InteractedExpansion.n6_proof h1 h4 h5, t7_kappa_tendsto,
    (univariate_printed_condition (fun n => kappa (spikePopulation n))).2,
    fun n hn => (h9 n hn).1, h10, ?_⟩
  simpa only [stochasticO, InteractedExpansion.R, Nat.cast_one, mul_one] using
    InteractedExpansion.n11_proof h10 (fun n hn =>
      (kappa_bounds (spikePopulation n) (by omega) (h2 n (by omega)).2).2)

end
end AronowAudit.P005.Wave1
