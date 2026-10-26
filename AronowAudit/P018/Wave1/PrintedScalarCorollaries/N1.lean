import AronowAudit.P018.Wave1.PrintedScalarCorollariesBlueprint

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace AronowAudit.P018.Wave1.PrintedScalarCorollaries
open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
noncomputable section

theorem endpoints_ne {N : ℕ} (d : Dyad N) : firstUnit d ≠ secondUnit d :=
  (Finset.min'_lt_max'_of_card (members d) (by rw [members_card]; omega)).ne

theorem members_endpoints {N : ℕ} (d : Dyad N) :
    members d = {firstUnit d, secondUnit d} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.min'_mem _ _
    · exact Finset.max'_mem _ _
  · rw [members_card, Finset.card_pair (endpoints_ne d)]

theorem incidence_count {N : ℕ} (i : Fin N) :
    ((dyads N).filter (fun s => i ∈ s)).card = N - 1 := by
  have h := Finset.card_filter_powersetCard_subset ({i} : Finset (Fin N))
    univ 2 (by simp) (by simp)
  simpa [dyads] using h

theorem endpoint_sum {N : ℕ} (u : Fin N → ℝ) :
    (∑ d : Dyad N, (u (firstUnit d) + u (secondUnit d))) =
      ((N - 1 : ℕ) : ℝ) * ∑ i, u i := by
  classical
  calc
    _ = ∑ d : Dyad N, ∑ i ∈ members d, u i := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [members_endpoints, Finset.sum_pair (endpoints_ne d)]
    _ = ∑ d ∈ dyads N, ∑ i ∈ d, u i := by
      simpa only [members] using
        (Finset.sum_coe_sort (dyads N) (fun d => ∑ i ∈ d, u i))
    _ = ∑ d ∈ dyads N, ∑ i : Fin N, if i ∈ d then u i else 0 := by simp
    _ = ∑ i : Fin N, ∑ d ∈ dyads N, if i ∈ d then u i else 0 := Finset.sum_comm
    _ = ∑ i : Fin N, ((N - 1 : ℕ) : ℝ) * u i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      simp [incidence_count]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem n1_proof : N1 := by
  intro N hN ω
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]; simp
  have hD : (Fintype.card (Dyad N) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
    rw [number_of_dyads, Nat.cast_choose_two]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hgram : sampleGram (design signKernel ω) =
      (Matrix.of (fun _ _ : Fin 1 => (Fintype.card (Dyad N) : ℝ))) := by
    ext a b
    fin_cases a; fin_cases b
    simp [sampleGram, Matrix.sum_apply, outer, design, signKernel, Matrix.of_apply]
  rw [sampleOLS, hgram, Matrix.inv_def]
  simp only [Matrix.of_apply, Matrix.det_unique, Matrix.adjugate_subsingleton,
    Ring.inverse_eq_inv, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Matrix.mulVec, dotProduct, Fin.sum_univ_one, Finset.sum_apply,
    score, Pi.smul_apply, smul_eq_mul, design, response, signKernel,
    Matrix.cons_val_zero, mul_one]
  rw [endpoint_sum (fun i => signValue (ω i)), hcast, hD]
  field_simp [hN0, hN1]
  <;> ring
end
end AronowAudit.P018.Wave1.PrintedScalarCorollaries
