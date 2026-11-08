import SAP.P004a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped BigOperators Classical

theorem SAP.P004a.WH.W1.T15_L2_proof : SAP.P004a.WH.W1.T15_L2 := by
  unfold SAP.P004a.WH.W1.T15_L2 SAP.P004a.T15KernelStatement
  intro N hN P U hP hU
  constructor
  · intro hid i
    letI : IsProbabilityMeasure (P i) := hP i
    letI : IsProbabilityMeasure U := hU
    apply Measure.ext
    intro s hs
    let g : Fin N → ℝ → ℝ := fun j x =>
      if j = i then s.indicator (fun _ : ℝ => (1 : ℝ)) x else 0
    have hgmeas : ∀ j, Measurable (g j) := by
      intro j
      by_cases hji : j = i
      · simpa [g, hji] using (measurable_const.indicator hs)
      · simp [g, hji]
    have hgbound : ∀ j, ∃ C : ℝ, ∀ r, |g j r| ≤ C := by
      intro j
      refine ⟨1, ?_⟩
      intro r
      by_cases hji : j = i
      · by_cases hrs : r ∈ s <;> simp [g, hji, hrs]
      · simp [g, hji]
    have h := hid g hgmeas hgbound
    have hsum : (∑ j : Fin N, ∫ r, g j r ∂P j) = (P i).real s := by
      rw [Finset.sum_eq_single i]
      · simp only [g, if_pos rfl]
        exact integral_indicator_one hs
      · intro j hj hji
        simp [g, hji]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    have hsumfun : (fun r : ℝ => ∑ j : Fin N, g j r) =
        s.indicator (fun _ : ℝ => (1 : ℝ)) := by
      funext r
      rw [Finset.sum_eq_single i]
      · simp [g]
      · intro j hj hji
        simp [g, hji]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    have hL : (∑ j : Fin N, ∫ r, g j r ∂P j) / (N : ℝ) =
        (P i).real s / (N : ℝ) := by rw [hsum]
    have hR : (∫ r, (∑ j : Fin N, g j r) / (N : ℝ) ∂U) =
        U.real s / (N : ℝ) := by
      calc
        _ = ∫ r, (s.indicator (fun _ : ℝ => (1 : ℝ)) r) / (N : ℝ) ∂U := by
          apply integral_congr_ae
          filter_upwards with r
          rw [← hsumfun]
        _ = (∫ r, s.indicator (fun _ : ℝ => (1 : ℝ)) r ∂U) / (N : ℝ) := by
          rw [integral_div]
        _ = U.real s / (N : ℝ) := by
          exact congrArg (fun x : ℝ => x / (N : ℝ))
            (integral_indicator_one (μ := U) hs)
    have hreal : (P i).real s / (N : ℝ) = U.real s / (N : ℝ) := by
      exact hL.symm.trans (h.trans hR)
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hreal' : (P i).real s = U.real s := by
      field_simp [hNreal] at hreal
      exact hreal
    exact (measureReal_eq_measureReal_iff).mp hreal'
  · intro hEq f hf hbound
    letI : IsProbabilityMeasure U := hU
    have hInt : ∀ i : Fin N, Integrable (f i) U := by
      intro i
      obtain ⟨C, hC⟩ := hbound i
      exact Integrable.of_bound (hf i).aestronglyMeasurable C
        (Filter.Eventually.of_forall fun r => by
          simpa [Real.norm_eq_abs] using hC r)
    calc
      (∑ i, ∫ r, f i r ∂P i) / (N : ℝ)
          = (∑ i, ∫ r, f i r ∂U) / (N : ℝ) := by
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              rw [hEq i]
      _ = (∫ r, ∑ i, f i r ∂U) / (N : ℝ) := by
            rw [integral_finsetSum Finset.univ (fun i hi => hInt i)]
      _ = ∫ r, (∑ i, f i r) / (N : ℝ) ∂U := by
            rw [integral_div]
