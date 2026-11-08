import SAP.P022.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T7_L3

open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

theorem designProbability_nonneg (d : Design) (E : Assignment d → Prop) :
    0 ≤ designProbability d E := by
  classical
  unfold designProbability designExpectation
  apply Finset.expect_nonneg
  intro π hπ
  split_ifs <;> norm_num

theorem probability_tail_eventually_lt (S : ExperimentSequence)
    (X : (q : ℕ) → Assignment (S.design q) → ℝ)
    (hbound : ∀ η, 0 < η → ∃ K : ℝ,
      scaledProbabilityLimsup S (fun q π => η ≤ |X q π|) ≤ ENNReal.ofReal K)
    (η : ℝ) (hη : 0 < η) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop,
      designProbability (S.design q) (fun π => η ≤ |X q π|) < δ := by
  obtain ⟨K, hK⟩ := hbound η hη
  let B : ℝ := |K| + 1
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hKB : K < B := by
    dsimp [B]
    linarith [le_abs_self K]
  have hreal : ENNReal.ofReal K < ENNReal.ofReal B :=
    (ENNReal.ofReal_lt_ofReal_iff').2 ⟨hKB, hB⟩
  let u : ℕ → ℝ≥0∞ := fun q => ENNReal.ofReal
    (((S.design q).N : ℝ) *
      designProbability (S.design q) (fun π => η ≤ |X q π|))
  have hlim : Filter.limsup u atTop ≤ ENNReal.ofReal K := by
    simpa [u, scaledProbabilityLimsup] using hK
  have hscaled : ∀ᶠ q : ℕ in atTop, u q < ENNReal.ofReal B :=
    Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hlim hreal)
  have hsize : ∀ᶠ q : ℕ in atTop, B / δ < rowSize S q :=
    (size_tendsto S) (Ioi_mem_atTop (B / δ))
  filter_upwards [hscaled, hsize] with q hqscaled hqsize
  have hmul : B < rowSize S q * δ := by
    have h := mul_lt_mul_of_pos_right hqsize hδ
    have heq : (B / δ) * δ = B := by field_simp
    rw [heq] at h
    exact h
  have hNpos : 0 < ((S.design q).N : ℝ) := by
    exact_mod_cast (show 0 < (S.design q).N by have := (S.design q).population_min; omega)
  have hscaled' : ENNReal.ofReal (((S.design q).N : ℝ) *
      designProbability (S.design q) (fun π => η ≤ |X q π|)) < ENNReal.ofReal B := by
    simpa [u] using hqscaled
  have hprod : ((S.design q).N : ℝ) *
      designProbability (S.design q) (fun π => η ≤ |X q π|) < B := by
    exact (ENNReal.ofReal_lt_ofReal_iff').1 hscaled' |>.1
  apply (mul_lt_mul_iff_of_pos_left hNpos).mp
  exact lt_trans hprod (by simpa [rowSize] using hmul)

end
end SAP.P022.WH.W1.P.T7_L3

open SAP.P022.WH.W1.P.T7_L3
open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

theorem SAP.P022.WH.W1.T7_L3_proof : SAP.P022.WH.W1.T7_L3 := by
  intro S X hbound
  change ∀ η : ℝ, 0 < η →
    Tendsto (fun q => designProbability (S.design q)
      (fun π => η ≤ |X q π - 0|)) atTop (𝓝 0)
  intro η hη
  simp only [sub_zero]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [] with q
    exact lt_of_lt_of_le ha (designProbability_nonneg (S.design q)
      (fun π => η ≤ |X q π|))
  · intro a ha
    exact probability_tail_eventually_lt S X hbound η hη a ha
