import SAP.P022.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T7_L4

open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def shift (r : ℕ) : ℝ :=
  rowSize cornerWitness (4 * r) /
    (2 * (rowSize cornerWitness (4 * r) - 1))

lemma rowSize_tendsto :
    Tendsto (fun r => rowSize cornerWitness (4 * r)) atTop atTop := by
  apply Filter.tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
  filter_upwards with r
  change (r : ℝ) ≤ ((4 * r + 4 : ℕ) : ℝ)
  exact_mod_cast (show r ≤ 4 * r + 4 by omega)

lemma rowSize_ge_four (r : ℕ) : 4 ≤ rowSize cornerWitness (4 * r) := by
  unfold rowSize
  exact_mod_cast (cornerWitness.design (4 * r)).population_min

lemma shift_tendsto : Tendsto shift atTop (𝓝 (1 / 2 : ℝ)) := by
  have hden : Tendsto (fun r => 2 * (rowSize cornerWitness (4 * r) - 1)) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop ?_ (rowSize_tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    filter_upwards with r
    have hn := rowSize_ge_four r
    nlinarith
  have hinv : Tendsto (fun r => (2 * (rowSize cornerWitness (4 * r) - 1))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hden
  have heq (r : ℕ) : shift r = (1 / 2 : ℝ) +
      (2 * (rowSize cornerWitness (4 * r) - 1))⁻¹ := by
    dsimp [shift]
    have hn1 : (0 : ℝ) < rowSize cornerWitness (4 * r) - 1 := by
      have hh := rowSize_ge_four r
      have hh' : (4 : ℝ) ≤ rowSize cornerWitness (4 * r) := by exact_mod_cast hh
      linarith
    have hn : (2 : ℝ) * (rowSize cornerWitness (4 * r) - 1) ≠ 0 :=
      ne_of_gt (mul_pos (by norm_num) hn1)
    field_simp [hn, ne_of_gt hn1]
    <;> ring
  have hfun : shift = fun r => (1 / 2 : ℝ) +
      (2 * (rowSize cornerWitness (4 * r) - 1))⁻¹ := by
    funext r
    exact heq r
  rw [hfun]
  simpa using (tendsto_const_nhds.add hinv)

lemma wrong_identity (hvar : CornerBalancedVariances) (r : ℕ)
    (π : Assignment (cornerWitness.design (4 * r))) :
    wrongUpperError cornerWitness (4 * r) π =
      |centeredUpperError cornerWitness (4 * r) π + shift r| := by
  have hpoint := (hvar r).2.2 π
  have hn : 0 ≤ rowSize cornerWitness (4 * r) :=
    (size_pos cornerWitness (4 * r)).le
  unfold wrongUpperError
  calc
    _ = |rowSize cornerWitness (4 * r)| *
          |rowEstimate cornerWitness .H (4 * r) π - rowTrueVariance cornerWitness (4 * r)| := by
            rw [abs_of_nonneg hn]
    _ = |rowSize cornerWitness (4 * r) *
          (rowEstimate cornerWitness .H (4 * r) π - rowTrueVariance cornerWitness (4 * r))| := by
            rw [abs_mul, abs_of_nonneg hn]
    _ = |centeredUpperError cornerWitness (4 * r) π + shift r| := by
      rw [hpoint]
      rfl

lemma designProbability_le_one (d : Design) (E : Assignment d → Prop) :
    designProbability d E ≤ 1 := by
  classical
  unfold designProbability designExpectation
  have hc : (1 : ℝ) = (𝔼 _π : Assignment d, (1 : ℝ)) :=
    (Finset.expect_const Finset.univ_nonempty _).symm
  rw [hc]
  apply Finset.expect_le_expect
  intro π hπ
  by_cases h : E π <;> simp [h]

lemma designProbability_nonneg (d : Design) (E : Assignment d → Prop) :
    0 ≤ designProbability d E := by
  classical
  unfold designProbability designExpectation
  apply Finset.expect_nonneg
  intro π hπ
  split_ifs <;> norm_num

lemma designProbability_mono (d : Design) (E F : Assignment d → Prop)
    (hEF : ∀ π, E π → F π) : designProbability d E ≤ designProbability d F := by
  classical
  unfold designProbability designExpectation
  apply Finset.expect_le_expect
  intro π hπ
  by_cases h : E π
  · simp [h, hEF π h]
  · simp only [h, if_false]
    split_ifs <;> norm_num

lemma one_le_probability_add (d : Design) (E F : Assignment d → Prop)
    (hEF : ∀ π, ¬ E π → F π) :
    1 ≤ designProbability d E + designProbability d F := by
  classical
  rw [designProbability, designProbability, designExpectation, designExpectation,
    ← Finset.expect_add_distrib]
  have hc : (1 : ℝ) = (𝔼 _π : Assignment d, (1 : ℝ)) :=
    (Finset.expect_const Finset.univ_nonempty _).symm
  rw [hc]
  apply Finset.expect_le_expect
  intro π hπ
  by_cases h : E π
  · simp only [h, if_true]
    split_ifs <;> norm_num
  · simp [h, hEF π h]

theorem main_proof : SAP.P022.WH.W1.T7_L4 := by
  intro hvar hcenter
  let d : ℕ → Design := fun r => cornerWitness.design (4 * r)
  have h4 : Tendsto (fun r : ℕ => 4 * r) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
    filter_upwards with r
    exact_mod_cast (show r ≤ 4 * r by omega)
  have hwrong : designConvergence d
      (fun r π => wrongUpperError cornerWitness (4 * r) π) (1 / 2 : ℝ) := by
    intro η hη
    let δ : ℝ := η / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    let p : ℕ → ℝ := fun r => designProbability (d r)
      (fun π => η ≤ |wrongUpperError cornerWitness (4 * r) π - (1 / 2 : ℝ)|)
    let v : ℕ → ℝ := fun r => designProbability (d r)
      (fun π => δ ≤ |centeredUpperError cornerWitness (4 * r) π|)
    have hv : Tendsto v atTop (𝓝 0) := by
      have ht := (hcenter δ hδ).comp h4
      change Tendsto (fun r => designProbability (cornerWitness.design (4 * r))
        (fun π => δ ≤ |centeredUpperError cornerWitness (4 * r) π - 0|)) atTop (𝓝 0) at ht
      change Tendsto (fun r => designProbability (cornerWitness.design (4 * r))
        (fun π => δ ≤ |centeredUpperError cornerWitness (4 * r) π|)) atTop (𝓝 0)
      simpa using ht
    have hshift_small : ∀ᶠ r in atTop, |shift r - (1 / 2 : ℝ)| < δ := by
      have hh := (tendsto_iff_dist_tendsto_zero.mp shift_tendsto).eventually_lt_const hδ
      filter_upwards [hh] with r hr
      simpa [Real.dist_eq] using hr
    have hmono : ∀ᶠ r in atTop, p r ≤ v r := by
      filter_upwards [hshift_small] with r hrs
      apply designProbability_mono (d r)
      intro π hbad
      rw [wrong_identity hvar r π] at hbad
      let c := centeredUpperError cornerWitness (4 * r) π
      have habs : abs (abs (c + shift r) - (1 / 2 : ℝ)) ≤
          |c| + |shift r - (1 / 2 : ℝ)| := by
        have h1 := abs_abs_sub_abs_le_abs_sub (c + shift r) (1 / 2 : ℝ)
        have h2 : |(c + shift r) - (1 / 2 : ℝ)| ≤
            |c| + |shift r - (1 / 2 : ℝ)| := by
          calc
            |(c + shift r) - (1 / 2 : ℝ)| = |c + (shift r - (1 / 2 : ℝ))| := by ring_nf
            _ ≤ |c| + |shift r - (1 / 2 : ℝ)| := abs_add_le c _
        have hhalf : |(1 / 2 : ℝ)| = (1 / 2 : ℝ) := by norm_num
        have h1' : abs (abs (c + shift r) - (1 / 2 : ℝ)) ≤
            |(c + shift r) - (1 / 2 : ℝ)| := by simpa [hhalf] using h1
        exact h1'.trans h2
      have hcenter_dev : δ ≤ |c| := by
        dsimp [c, δ] at *
        nlinarith [hbad, habs, hrs]
      simpa [v, c] using hcenter_dev
    have hp : Tendsto p atTop (𝓝 0) := by
      apply squeeze_zero' (Filter.Eventually.of_forall (fun r => designProbability_nonneg
        (d r) (fun π => η ≤ abs (wrongUpperError cornerWitness (4 * r) π - (1 / 2 : ℝ))))) hmono hv
    change Tendsto p atTop (𝓝 0)
    exact hp
  refine ⟨?_, ?_⟩
  · intro η hη
    exact hwrong η hη
  · intro ε hε hεhalf
    let δ : ℝ := (1 / 2 - ε) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    let p : ℕ → ℝ := fun r => designProbability (d r)
      (fun π => ε ≤ wrongUpperError cornerWitness (4 * r) π)
    let v : ℕ → ℝ := fun r => designProbability (d r)
      (fun π => δ ≤ |wrongUpperError cornerWitness (4 * r) π - (1 / 2 : ℝ)|)
    have hv : Tendsto v atTop (𝓝 0) := by
      simpa [v, designConvergence, d, sub_zero] using hwrong δ hδ
    have hlarge (r : ℕ) : 1 ≤ p r + v r := by
      apply one_le_probability_add
      intro π hnot
      have hy : wrongUpperError cornerWitness (4 * r) π < ε := lt_of_not_ge hnot
      have habs : δ ≤
          |wrongUpperError cornerWitness (4 * r) π - (1 / 2 : ℝ)| := by
        rw [abs_of_neg (by linarith [hεhalf, hy])]
        dsimp [δ]
        linarith
      exact habs
    have hp_le (r : ℕ) : p r ≤ 1 := by
      exact designProbability_le_one (d r)
        (fun π => ε ≤ wrongUpperError cornerWitness (4 * r) π)
    have hgap_nonneg (r : ℕ) : 0 ≤ 1 - p r := by linarith [hp_le r]
    have hgap_le (r : ℕ) : 1 - p r ≤ v r := by linarith [hlarge r]
    have hgap : Tendsto (fun r => 1 - p r) atTop (𝓝 0) :=
      squeeze_zero hgap_nonneg hgap_le hv
    have hp : Tendsto p atTop (𝓝 1) := by
      have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hgap
      simpa using ht
    have hsize := rowSize_tendsto
    have hscaled : Tendsto (fun r => rowSize cornerWitness (4 * r) * p r) atTop atTop := by
      apply Filter.tendsto_atTop_mono' atTop ?_
        (hsize.atTop_div_const (by norm_num : (0 : ℝ) < 2))
      have hevp : ∀ᶠ r in atTop, (1 / 2 : ℝ) < p r :=
        hp.eventually (isOpen_Ioi.mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
      filter_upwards [hevp] with r hr
      have hn : 0 ≤ rowSize cornerWitness (4 * r) :=
        (size_pos cornerWitness (4 * r)).le
      nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hr) hn]
    refine ⟨hp, hscaled, ?_⟩
    intro R
    filter_upwards [hscaled.eventually (eventually_ge_atTop (R + 1))] with r hr
    linarith

end
end SAP.P022.WH.W1.P.T7_L4

theorem SAP.P022.WH.W1.T7_L4_proof : SAP.P022.WH.W1.T7_L4 :=
  SAP.P022.WH.W1.P.T7_L4.main_proof
